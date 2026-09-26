'use strict';

const { parse, ParseError } = require('./parser');
const U = require('./units');

class InferError extends Error {
  constructor(message, spans, slice = null) {
    super(message);
    this.name = 'InferError';
    this.spans = spans || [];
    this.slice = slice; // 冲突依据切片（buildConflictSlice 产物）
  }
}

/* ---------------- 类型 ----------------
 * { kind:'tvar', id, instance, why }  类型变量（可绑定；why 为起源事实 id 集合）
 * { kind:'num',  unit }               带单位数值（单位单项式自带 src 锚点）
 * { kind:'fun',  param, ret }         单参数函数
 * 类型方案 scheme = { tvars, uvars, type, genFact }（let 绑定处泛化）
 *
 * 来源追踪的两条通道：
 *   - 事实日志 ctx.facts：推断中每个有来源意义的动作（声明 / 绑定 / 泛化 /
 *     每次实例化 / 每次合一与单位求解 / 调用 / 运算 / 单位组合），按序产生，
 *     deps 指向其前提事实；
 *   - 变量 why 与单位锚点：类型变量、单位变量携带起源事实 id；单位基元
 *     （m、s…）在 parser 中锚定源码区间，并经 ctx.anchorFacts 映射到声明/
 *     字面量事实。绑定沿 tvar.instance 边实时累积，故任何已归约类型都能
 *     还原出它经过的全部实例化、调用与合一前提。
 */

function newCtx(unitSrcs) {
  return {
    tvarSeq: 0,
    uvarSeq: 0,
    R: createRenderCtx(),
    stack: [],
    events: new Map(),
    nodeType: new Map(),
    lets: [],
    facts: new Map(),
    factSeq: 0,
    unitSrcs,
    anchorFacts: new Map(), // 单位基元锚点 id -> 声明/字面量事实 id
  };
}

function addFact(ctx, kind, nodeId, detail, deps = []) {
  const id = ++ctx.factSeq;
  const fact = {
    id,
    kind,
    nodeId,
    detail,
    deps: [...new Set([...deps].filter((d) => d != null))],
  };
  ctx.facts.set(id, fact);
  return id;
}

const mergeWhy = (acc, xs) => {
  if (xs instanceof Set) for (const v of xs) acc.add(v);
  else if (typeof xs === 'number') acc.add(xs);
  return acc;
};

function newTVar(ctx, why = null) {
  return { kind: 'tvar', id: ++ctx.tvarSeq, instance: null, why: new Set(why || []) };
}

function newUVar(ctx, why = null) {
  return { id: ++ctx.uvarSeq, instance: null, why: new Set(why || []) };
}

function prune(t) {
  if (t.kind === 'tvar' && t.instance) {
    t.instance = prune(t.instance);
    return t.instance;
  }
  return t;
}

function occursTVar(v, t) {
  t = prune(t);
  if (t.kind === 'tvar') return t === v;
  if (t.kind === 'fun') return occursTVar(v, t.param) || occursTVar(v, t.ret);
  return false;
}

function freeTVars(t, acc) {
  t = prune(t);
  if (t.kind === 'tvar') acc.add(t);
  else if (t.kind === 'fun') {
    freeTVars(t.param, acc);
    freeTVars(t.ret, acc);
  }
  return acc;
}

function freeUVars(t, acc) {
  t = prune(t);
  if (t.kind === 'num') {
    for (const v of U.resolveMono(t.unit).vars.keys()) acc.add(v);
  } else if (t.kind === 'fun') {
    freeUVars(t.param, acc);
    freeUVars(t.ret, acc);
  }
  return acc;
}

function freeVarsEnv(env) {
  const t = new Set();
  const u = new Set();
  for (const sc of env.values()) {
    for (const v of freeTVars(sc.type, new Set())) if (!sc.tvars.includes(v)) t.add(v);
    for (const v of freeUVars(sc.type, new Set())) if (!sc.uvars.includes(v)) u.add(v);
  }
  return { t, u };
}

/* ---------------- 命名与渲染（每次推断独立、确定） ---------------- */

const LETTERS = 'abcdefghijklmnopqrstuvwxyz';

function createRenderCtx() {
  return { tNames: new Map(), uNames: new Map(), tSeq: 0, uSeq: 0 };
}

function nameT(R, v) {
  let name = R.tNames.get(v);
  if (!name) {
    const n = R.tSeq++;
    name = n < 26 ? `'${LETTERS[n]}` : `'t${n - 25}`;
    R.tNames.set(v, name);
  }
  return name;
}

function nameU(R, v) {
  let name = R.uNames.get(v);
  if (!name) {
    name = `'u${++R.uSeq}`;
    R.uNames.set(v, name);
  }
  return name;
}

function renderMono(R, m) {
  return U.renderMono(m, (v) => nameU(R, v));
}

function renderType(R, t) {
  t = prune(t);
  if (t.kind === 'tvar') return nameT(R, t);
  if (t.kind === 'num') return `num<${renderMono(R, t.unit)}>`;
  const pRaw = prune(t.param);
  const p = renderType(R, pRaw);
  const left = pRaw.kind === 'fun' ? `(${p})` : p;
  return `${left} -> ${renderType(R, t.ret)}`;
}

function renderScheme(R, sc) {
  const qs = [...sc.tvars.map((v) => nameT(R, v)), ...sc.uvars.map((v) => nameU(R, v))];
  const body = renderType(R, sc.type);
  return qs.length ? `∀ ${qs.join(' ')}. ${body}` : body;
}

/* ---------------- 来源提取 ---------------- */

/** 单位单项式的全部起源事实：基元锚点映射回声明事实、传播事实、变量沿绑定累积。 */
function unitWhy(ctx, m, acc = new Set()) {
  for (const w of m.why) acc.add(w);
  for (const anchor of m.src) {
    const fid = ctx.anchorFacts.get(anchor);
    if (fid != null) acc.add(fid);
  }
  for (const [v] of m.vars) {
    mergeWhy(acc, v.why);
    if (v.instance) unitWhy(ctx, v.instance, acc);
  }
  return acc;
}

/**
 * 类型的全部起源事实。不做 prune 跳转：沿 tvar.instance 绑定边继续向下遍历，
 * 同时累加每个被消解变量自身的 why，使参数绑定 / 实例化 / 调用事实不致丢失。
 */
function typeWhy(ctx, t, acc = new Set()) {
  if (t.kind === 'tvar') {
    mergeWhy(acc, t.why);
    if (t.instance) typeWhy(ctx, t.instance, acc);
    return acc;
  }
  if (t.why) mergeWhy(acc, t.why);
  if (t.kind === 'num') return unitWhy(ctx, t.unit, acc);
  typeWhy(ctx, t.param, acc);
  typeWhy(ctx, t.ret, acc);
  return acc;
}

/** 把被绑定变量的来源事实并入代表类型，保证从代表侧出发也能还原这些前提。 */
function absorbWhy(rep, why) {
  if (!why || !why.size) return;
  if (rep.kind === 'num') for (const w of why) rep.unit.why.add(w);
  else if (rep.kind === 'fun') {
    if (!rep.why) rep.why = new Set();
    for (const w of why) rep.why.add(w);
  }
}

/* ---------------- 合一（带事实登记） ---------------- */

function unify(ctx, t1, t2, nodeId, detail) {
  const a = prune(t1);
  const b = prune(t2);
  if (a === b) return null;
  if (a.kind === 'tvar') {
    if (occursTVar(a, b)) throw new U.UnifyError('occurs', { v: a, t: b });
    const fid = addFact(ctx, 'unify', nodeId, detail || `合一 ${nameT(ctx.R, a)} := ${renderType(ctx.R, b)}`, [
      ...a.why,
      ...typeWhy(ctx, b),
    ]);
    a.instance = b;
    absorbWhy(b, a.why);
    if (b.kind === 'tvar') b.why.add(fid); else absorbWhy(b, new Set([fid]));
    log(ctx, `合一约束：${nameT(ctx.R, a)} := ${renderType(ctx.R, b)}`);
    return fid;
  }
  if (b.kind === 'tvar') {
    if (occursTVar(b, a)) throw new U.UnifyError('occurs', { v: b, t: a });
    const fid = addFact(ctx, 'unify', nodeId, detail || `合一 ${nameT(ctx.R, b)} := ${renderType(ctx.R, a)}`, [
      ...b.why,
      ...typeWhy(ctx, a),
    ]);
    b.instance = a;
    absorbWhy(a, b.why);
    if (a.kind === 'tvar') a.why.add(fid); else absorbWhy(a, new Set([fid]));
    log(ctx, `合一约束：${nameT(ctx.R, b)} := ${renderType(ctx.R, a)}`);
    return fid;
  }
  if (a.kind !== b.kind) throw new U.UnifyError('type-mismatch', { t1: a, t2: b });
  if (a.kind === 'fun') {
    unify(ctx, a.param, b.param, nodeId, detail ? `${detail}（参数部分）` : '函数参数合一');
    unify(ctx, a.ret, b.ret, nodeId, detail ? `${detail}（返回部分）` : '函数返回合一');
    return null;
  }
  // num/num：单位在整数指数群上合一，每次单位变量求解都登记事实并把前提并入其 why
  U.unifyMonos(a.unit, b.unit, ({ v, unit }) => {
    const fid = addFact(
      ctx,
      'unit-solve',
      nodeId,
      `单位求解 ${nameU(ctx.R, v)} := ${renderMono(ctx.R, unit)}`,
      [...v.why, ...unitWhy(ctx, unit)],
    );
    v.why.add(fid);
    unit.why.add(fid);
  });
  addFact(
    ctx,
    'unit-unify',
    nodeId,
    detail || `单位合一成功：两侧归一为 ${renderMono(ctx.R, a.unit)}`,
    [...unitWhy(ctx, a.unit), ...unitWhy(ctx, b.unit)],
  );
  log(ctx, `单位合一成功：两侧单位归一为 ${renderMono(ctx.R, a.unit)}`);
  return null;
}

/* ---------------- 泛化与实例化 ---------------- */

function generalize(ctx, env, type, nodeId, name) {
  const envFree = freeVarsEnv(env);
  const qt = [...freeTVars(type, new Set())].filter((v) => !envFree.t.has(v));
  const qu = [...freeUVars(type, new Set())].filter((v) => !envFree.u.has(v));
  const genFact = addFact(
    ctx,
    'generalize',
    nodeId,
    `let 泛化「${name}」：${qt.length} 个类型变量、${qu.length} 个单位变量提升为类型方案`,
    typeWhy(ctx, type),
  );
  // 泛化事实注入被量化变量：它们之后经实例化进入任何约束，都可回溯到本次泛化
  for (const v of qt) v.why.add(genFact);
  for (const v of qu) v.why.add(genFact);
  return { tvars: qt, uvars: qu, type, genFact };
}

function substType(t, tMap, uMap) {
  t = prune(t);
  if (t.kind === 'tvar') return tMap.get(t) || t;
  if (t.kind === 'num') return { kind: 'num', unit: U.substMono(t.unit, uMap) };
  return { kind: 'fun', param: substType(t.param, tMap, uMap), ret: substType(t.ret, tMap, uMap) };
}

/**
 * 结构复制单态方案：新建 num/fun 与单项式外壳（why 独立，引用事实不互相污染），
 * 但保留环境中自由的类型/单位变量对象本身（仍与原绑定联动）。
 */
function copyType(t) {
  t = prune(t);
  if (t.kind === 'tvar') return t;
  if (t.kind === 'num') {
    const u = U.monoUnit(t.unit.src, t.unit.why);
    for (const [b, e] of t.unit.bases) u.bases.set(b, e);
    for (const [v, e] of t.unit.vars) u.vars.set(v, e);
    return { kind: 'num', unit: u };
  }
  return { kind: 'fun', param: copyType(t.param), ret: copyType(t.ret) };
}

/**
 * 标识符引用：泛化方案取新鲜变量副本（每次引用独立实例化）；
 * 单态绑定取结构副本。两种路径都登记事实，使引用节点成为传播链上可点选的一环。
 */
function instantiate(ctx, sc, nodeId, name) {
  if (sc.tvars.length === 0 && sc.uvars.length === 0) {
    // 函数参数等自由类型变量：其来源（参数绑定）已在变量 why 上，引用不另立事实
    if (prune(sc.type).kind === 'tvar') return sc.type;
    const t = copyType(sc.type);
    const fid = addFact(
      ctx,
      'use',
      nodeId,
      `引用「${name}」：沿用单态类型 ${renderType(ctx.R, t)}`,
      [sc.genFact, ...typeWhy(ctx, t)],
    );
    absorbWhy(t, new Set([fid]));
    return t;
  }
  const tMap = new Map();
  for (const v of sc.tvars) tMap.set(v, newTVar(ctx, v.why));
  const uMap = new Map();
  for (const v of sc.uvars) uMap.set(v, U.monoVar(newUVar(ctx, v.why)));
  const t = substType(sc.type, tMap, uMap);
  // 实例化事实以泛化事实与新鲜变量的全部来源为前提
  const fid = addFact(
    ctx,
    'instantiate',
    nodeId,
    `实例化「${name}」：类型方案 ${renderScheme(ctx.R, sc)} 取一份新鲜变量副本（与其他引用互不影响）`,
    [sc.genFact, ...typeWhy(ctx, t)],
  );
  // 注入到本次新鲜变量：之后经这些变量传播的任何约束都能回溯到本次实例化
  for (const nv of tMap.values()) nv.why.add(fid);
  for (const m of uMap.values()) for (const [nv] of m.vars) nv.why.add(fid);
  return t;
}

/* ---------------- 事件日志（成功表达式依据，保持既有行为） ---------------- */

function pushEvent(ctx, nodeId, msg) {
  let arr = ctx.events.get(nodeId);
  if (!arr) {
    arr = [];
    ctx.events.set(nodeId, arr);
  }
  arr.push(msg);
}

function log(ctx, msg) {
  const top = ctx.stack[ctx.stack.length - 1];
  if (top) pushEvent(ctx, top.id, msg);
}

const spanOf = (node, label) => ({ start: node.span.start, end: node.span.end, label });

/* ---------------- 主推断 ---------------- */

function inferNode(ctx, env, node) {
  ctx.stack.push(node);
  try {
    const t = dispatch(ctx, env, node);
    ctx.nodeType.set(node.id, t);
    return t;
  } catch (e) {
    if (e instanceof U.UnifyError) throw enrichUnify(ctx, e, node);
    throw e;
  } finally {
    ctx.stack.pop();
  }
}

/** 登记声明/字面量事实，并把其单位基元锚点映射到该事实（切片回溯的根）。 */
function registerUnitAnchors(ctx, unit, fid) {
  for (const anchor of unit.src) {
    if (!ctx.anchorFacts.has(anchor)) ctx.anchorFacts.set(anchor, fid);
  }
}

function dispatch(ctx, env, node) {
  const R = ctx.R;
  switch (node.kind) {
    case 'sensor': {
      const t = { kind: 'num', unit: node.unit };
      const fid = addFact(ctx, 'sensor', node.id, `传感器声明「${node.name}」：单位 ${renderMono(R, node.unit)}`, []);
      registerUnitAnchors(ctx, node.unit, fid);
      env.set(node.name, { tvars: [], uvars: [], type: t });
      log(ctx, `传感器声明「${node.name}」：${renderType(R, t)}`);
      return t;
    }
    case 'num': {
      if (node.unit) {
        const t = { kind: 'num', unit: node.unit };
        const fid = addFact(ctx, 'literal', node.id, `数值 ${node.text}：标注单位 ${renderMono(R, node.unit)}`, []);
        registerUnitAnchors(ctx, node.unit, fid);
        log(ctx, `数值 ${node.text}：标注单位，类型 ${renderType(R, t)}`);
        return t;
      }
      const uv = newUVar(ctx);
      const fid = addFact(ctx, 'literal', node.id, `数值 ${node.text}：引入单位变量 ${nameU(R, uv)}（由上下文约束确定）`, []);
      uv.why.add(fid);
      const t = { kind: 'num', unit: U.monoVar(uv) };
      log(ctx, `数值 ${node.text}：引入单位变量 ${renderMono(R, t.unit)}，具体单位由上下文约束确定`);
      return t;
    }
    case 'ident': {
      const sc = env.get(node.name);
      if (!sc) {
        throw new InferError(`未定义标识符「${node.name}」`, [
          spanOf(node, `未定义标识符「${node.name}」`),
        ]);
      }
      const t = instantiate(ctx, sc, node.id, node.name);
      if (sc.tvars.length || sc.uvars.length) {
        log(
          ctx,
          `引用「${node.name}」：类型方案 ${renderScheme(R, sc)} 重新实例化为 ${renderType(R, t)}（每次引用独立实例化，互不影响）`,
        );
      } else {
        log(ctx, `引用「${node.name}」：${renderType(R, t)}`);
      }
      return t;
    }
    case 'fun': {
      const tv = newTVar(ctx);
      const bindFact = addFact(ctx, 'bind', node.id, `参数绑定「${node.param}」：引入类型变量 ${nameT(R, tv)}`, []);
      tv.why.add(bindFact);
      log(ctx, `引入参数「${node.param}」：类型变量 ${nameT(R, tv)}`);
      const env2 = new Map(env);
      env2.set(node.param, { tvars: [], uvars: [], type: tv });
      const tb = inferNode(ctx, env2, node.body);
      const ft = { kind: 'fun', param: tv, ret: tb };
      addFact(ctx, 'fun', node.id, `函数体归并：${renderType(R, ft)}`, [...typeWhy(ctx, ft), bindFact]);
      log(ctx, `函数类型归并：${renderType(R, ft)}`);
      return ft;
    }
    case 'app': {
      const tf = inferNode(ctx, env, node.func);
      const ta = inferNode(ctx, env, node.arg);
      const beta = newTVar(ctx);
      const fid = addFact(
        ctx,
        'app',
        node.id,
        `调用约束：被调用类型 ${renderType(R, tf)} 须与 ${renderType(R, ta)} -> ${nameT(R, beta)} 合一`,
        [...typeWhy(ctx, tf), ...typeWhy(ctx, ta)],
      );
      beta.why.add(fid);
      log(ctx, `调用约束：函数类型 ${renderType(R, tf)} 须与 ${renderType(R, ta)} -> ${nameT(R, beta)} 合一`);
      try {
        unify(ctx, tf, { kind: 'fun', param: ta, ret: beta }, node.id, '调用合一：函数类型 与 实参 -> 结果');
      } catch (e) {
        if (e instanceof U.UnifyError) throw appError(ctx, node, e, tf, ta, fid);
        throw e;
      }
      addFact(ctx, 'app-result', node.id, `调用结果类型：${renderType(R, beta)}`, [...typeWhy(ctx, beta), fid]);
      log(ctx, `调用结果类型：${renderType(R, beta)}`);
      return beta;
    }
    case 'neg': {
      const te = inferNode(ctx, env, node.expr);
      const uv = newUVar(ctx);
      const t = { kind: 'num', unit: U.monoVar(uv) };
      try {
        unify(ctx, te, t, node.id, '取负：操作数须为数值');
      } catch (e) {
        if (e instanceof U.UnifyError) {
          throw new InferError(`取负运算要求数值类型，但此处为 ${renderType(R, te)}`, [
            spanOf(node.expr, `非数值类型：${renderType(R, te)}`),
          ]);
        }
        throw e;
      }
      return t;
    }
    case 'binop':
      return inferBinop(ctx, env, node);
    case 'let': {
      const tv = inferNode(ctx, env, node.value);
      const sc = generalize(ctx, env, tv, node.id, node.name);
      ctx.lets.push({ name: node.name, scheme: sc });
      const qn = [...sc.tvars.map((v) => nameT(R, v)), ...sc.uvars.map((v) => nameU(R, v))];
      log(
        ctx,
        qn.length
          ? `let 绑定「${node.name}」：泛化变量 ${qn.join('、')}，得到类型方案 ${renderScheme(R, sc)}；每次引用将独立实例化`
          : `let 绑定「${node.name}」：类型 ${renderScheme(R, sc)}（无可泛化变量）`,
      );
      if (node.body === null) {
        env.set(node.name, sc);
        return tv;
      }
      const env2 = new Map(env);
      env2.set(node.name, sc);
      return inferNode(ctx, env2, node.body);
    }
    default:
      throw new Error(`未知节点类型：${node.kind}`);
  }
}

function inferBinop(ctx, env, node) {
  const R = ctx.R;
  const tl = inferNode(ctx, env, node.left);
  const tr = inferNode(ctx, env, node.right);
  if (node.op === '+' || node.op === '-') {
    // 加减：两侧须为相同单位的数值
    const uv = newUVar(ctx);
    const t = { kind: 'num', unit: U.monoVar(uv) };
    const fid = addFact(
      ctx,
      'binop',
      node.id,
      `「${node.op}」约束：两侧须为相同单位的数值（左 ${renderType(R, tl)}；右 ${renderType(R, tr)}）`,
      [...typeWhy(ctx, tl), ...typeWhy(ctx, tr)],
    );
    uv.why.add(fid);
    log(ctx, `「${node.op}」约束：两侧须为相同单位的数值；左侧 ${renderType(R, tl)}，右侧 ${renderType(R, tr)}`);
    try {
      unify(ctx, tl, t, node.id, `「${node.op}」左操作数与共同单位合一`);
      unify(ctx, tr, t, node.id, `「${node.op}」右操作数与共同单位合一`);
    } catch (e) {
      if (e instanceof U.UnifyError) throw binopError(ctx, node, e, tl, tr, fid);
      throw e;
    }
    log(ctx, `「${node.op}」结果类型：${renderType(R, t)}`);
    return t;
  }
  // 乘除：组合单位
  const uva = newUVar(ctx);
  const uvb = newUVar(ctx);
  try {
    unify(ctx, tl, { kind: 'num', unit: U.monoVar(uva) }, node.id, `「${node.op}」左操作数须为数值`);
    unify(ctx, tr, { kind: 'num', unit: U.monoVar(uvb) }, node.id, `「${node.op}」右操作数须为数值`);
  } catch (e) {
    if (e instanceof U.UnifyError) throw binopError(ctx, node, e, tl, tr, null);
    throw e;
  }
  const ra = U.resolveMono(U.monoVar(uva));
  const rb = U.resolveMono(U.monoVar(uvb));
  const ru = node.op === '*' ? U.monoMul(ra, rb) : U.monoDiv(ra, rb);
  addFact(
    ctx,
    'unit-combine',
    node.id,
    `「${node.op}」单位组合：${renderMono(R, ra)} ${node.op} ${renderMono(R, rb)} ⇒ ${renderMono(R, ru)}`,
    [...uva.why, ...uvb.why],
  );
  log(ctx, `「${node.op}」单位组合：${renderMono(R, ra)} ${node.op} ${renderMono(R, rb)} ⇒ ${renderMono(R, ru)}`);
  return { kind: 'num', unit: ru };
}

/* ---------------- 错误加工（定位源码片段 + 冲突切片） ---------------- */

function binopError(ctx, node, e, tl, tr, seedFact) {
  const R = ctx.R;
  const lSpan = spanOf(node.left, `左操作数：${renderType(R, tl)}`);
  const rSpan = spanOf(node.right, `右操作数：${renderType(R, tr)}`);
  if (e.kind === 'unit-mismatch') {
    const slice = buildConflictSlice(ctx, e, {
      spans: [lSpan, rSpan],
      seedFact,
      node,
      headline: `「${node.op}」要求两侧单位相同`,
    });
    return new InferError(
      `单位不匹配：「${node.op}」要求两侧单位相同，但左操作数为 ${renderType(R, tl)}、右操作数为 ${renderType(R, tr)}`,
      [lSpan, rSpan],
      slice,
    );
  }
  if (e.kind === 'type-mismatch') {
    const badLeft = prune(tl).kind !== 'num';
    const badT = badLeft ? tl : tr;
    return new InferError(
      `「${node.op}」的操作数须为数值类型，但${badLeft ? '左' : '右'}侧为 ${renderType(R, badT)}`,
      [spanOf(badLeft ? node.left : node.right, `非数值类型：${renderType(R, badT)}`)],
    );
  }
  return enrichUnify(ctx, e, node);
}

function appError(ctx, node, e, tf, ta, seedFact) {
  const R = ctx.R;
  if (e.kind === 'occurs') {
    const slice = buildConflictSlice(ctx, e, {
      spans: [spanOf(node, '自应用调用'), spanOf(node.func, '被调用表达式'), spanOf(node.arg, '实参')],
      seedFact,
      node,
      headline: '自应用要求类型变量等于含其自身的函数类型，无法构造有限类型',
    });
    return new InferError(
      `无限类型：类型变量 ${nameT(R, e.v)} 出现在 ${renderType(R, e.t)} 中，自应用无法构造有限类型（occurs check 失败）`,
      [spanOf(node, '自应用调用'), spanOf(node.func, '被调用表达式'), spanOf(node.arg, '实参')],
      slice,
    );
  }
  if (e.kind === 'type-mismatch') {
    return new InferError(`类型不匹配：试图调用非函数类型 ${renderType(R, tf)}`, [
      spanOf(node.func, `非函数类型：${renderType(R, tf)}`),
      spanOf(node.arg, `实参：${renderType(R, ta)}`),
    ]);
  }
  if (e.kind === 'unit-mismatch') {
    const slice = buildConflictSlice(ctx, e, {
      spans: [spanOf(node.arg, `实参：${renderType(R, ta)}`), spanOf(node.func, `形参要求：${renderType(R, tf)}`)],
      seedFact,
      node,
      headline: '实参单位与形参要求不符',
    });
    return new InferError(
      `单位不匹配：实参单位与形参要求不符（${renderMono(R, e.u1)} 与 ${renderMono(R, e.u2)}）`,
      [spanOf(node.arg, `实参：${renderType(R, ta)}`), spanOf(node.func, `形参要求：${renderType(R, tf)}`)],
      slice,
    );
  }
  return enrichUnify(ctx, e, node);
}

function enrichUnify(ctx, e, node) {
  const R = ctx.R;
  switch (e.kind) {
    case 'occurs': {
      const slice = buildConflictSlice(ctx, e, {
        spans: [spanOf(node, '约束冲突位置')],
        seedFact: null,
        node,
        headline: '类型变量出现在其自身定义中，无法构造有限类型',
      });
      return new InferError(
        `无限类型：类型变量 ${nameT(R, e.v)} 出现在 ${renderType(R, e.t)} 中（occurs check 失败）`,
        [spanOf(node, '约束冲突位置')],
        slice,
      );
    }
    case 'type-mismatch':
      return new InferError(
        `类型不匹配：${renderType(R, e.t1)} 与 ${renderType(R, e.t2)} 无法统一`,
        [spanOf(node, '类型冲突位置')],
      );
    case 'unit-mismatch': {
      const slice = buildConflictSlice(ctx, e, {
        spans: [spanOf(node, '单位冲突位置')],
        seedFact: null,
        node,
        headline: '两侧单位无法统一',
      });
      return new InferError(
        `单位不匹配：${renderMono(R, e.u1)} 与 ${renderMono(R, e.u2)} 无法统一`,
        [spanOf(node, '单位冲突位置')],
        slice,
      );
    }
    case 'occurs-unit':
      return new InferError('无限单位类型：单位变量出现在其自身定义中（occurs check 失败）', [
        spanOf(node, '单位冲突位置'),
      ]);
    default:
      return new InferError(`类型错误：${e.message}`, [spanOf(node, '错误位置')]);
  }
}

/* ---------------- 冲突依据切片 ---------------- */

const FACT_KIND_TITLE = {
  sensor: '传感器声明',
  literal: '数值引入单位',
  bind: '参数绑定',
  fun: '函数体归并',
  generalize: 'let 泛化',
  instantiate: '类型方案实例化',
  use: '单态引用',
  unify: '类型合一',
  'unit-solve': '单位求解',
  'unit-unify': '单位合一',
  'unit-combine': '单位组合',
  app: '调用约束',
  'app-result': '调用结果',
  binop: '运算约束',
};

/** 首次不可合一的两侧中涉及的起源事实（反向归并种子）。 */
function conflictSeeds(ctx, e) {
  const seeds = new Set();
  switch (e.kind) {
    case 'unit-mismatch':
      unitWhy(ctx, e.u1, seeds);
      unitWhy(ctx, e.u2, seeds);
      break;
    case 'occurs':
      typeWhy(ctx, e.v, seeds);
      typeWhy(ctx, e.t, seeds);
      break;
    case 'occurs-unit':
      if (e.v) mergeWhy(seeds, e.v.why);
      if (e.u) unitWhy(ctx, e.u, seeds);
      break;
    case 'type-mismatch':
      typeWhy(ctx, e.t1, seeds);
      typeWhy(ctx, e.t2, seeds);
      break;
    default:
      break;
  }
  return seeds;
}

/**
 * 从首次不可合一处沿事实依赖反向归并最小冲突依据：
 * 闭包内每条事实都位于「某起源 → 冲突点」的真实传播边上，删除任一项，
 * 对应约束链即断裂。严格按类型/单位/实例化传播边回溯——不按文本邻近、
 * 不只取最后一个操作符、不反复试探脚本。
 */
function buildConflictSlice(ctx, e, opts) {
  const seeds = conflictSeeds(ctx, e);
  if (opts.seedFact) seeds.add(opts.seedFact);

  const involved = new Set();
  const stack = [...seeds];
  while (stack.length) {
    const id = stack.pop();
    if (involved.has(id)) continue;
    const f = ctx.facts.get(id);
    if (!f) continue;
    involved.add(id);
    for (const d of f.deps) if (!involved.has(d)) stack.push(d);
  }

  // 冲突点（运算/调用）相关事实收尾，保证相加位置/调用位置在切片内
  let goalFactId = opts.seedFact;
  if (opts.node) {
    for (const f of ctx.facts.values()) {
      if (f.nodeId === opts.node.id && (f.kind === 'binop' || f.kind === 'app')) {
        involved.add(f.id);
        goalFactId = f.id;
      }
    }
  }

  const ordered = [...involved].sort((a, b) => a - b).map((id) => ctx.facts.get(id)).filter(Boolean);
  const nodeIds = [...new Set(ordered.map((f) => f.nodeId).filter((n) => n != null))].sort((a, b) => a - b);

  return {
    headline: opts.headline || '冲突依据切片',
    conflict: conflictSummary(ctx, e),
    goalFactId,
    steps: ordered.map((f) => ({
      factId: f.id,
      kind: f.kind,
      title: FACT_KIND_TITLE[f.kind] || f.kind,
      detail: f.detail,
      nodeId: f.nodeId,
      deps: f.deps,
    })),
    nodeIds,
  };
}

function conflictSummary(ctx, e) {
  const R = ctx.R;
  if (e.kind === 'unit-mismatch') {
    return `首次不可合一：单位 ${renderMono(R, e.u1)} 与 ${renderMono(R, e.u2)} 不一致`;
  }
  if (e.kind === 'occurs') {
    return `首次不可合一：${nameT(R, e.v)} 出现在 ${renderType(R, e.t)} 中（occurs check）`;
  }
  if (e.kind === 'type-mismatch') {
    return `首次不可合一：${renderType(R, e.t1)} 与 ${renderType(R, e.t2)} 类型构造子不同`;
  }
  return '首次不可合一';
}

/* ---------------- 程序级入口 ---------------- */

function inferProgram(ctx, statements) {
  const env = new Map();
  let last = null;
  for (const st of statements) last = inferNode(ctx, env, st);
  return last;
}

const KIND_LABEL = {
  sensor: '传感器声明',
  let: 'let 绑定',
  num: '数值',
  ident: '标识符',
  fun: '函数（单参数）',
  app: '调用',
  binop: '四则运算',
  neg: '取负',
};

const NODE_ROLE = {
  sensor: '传感器声明',
  let: 'let 绑定',
  num: '数值',
  ident: '宏引用',
  fun: '函数体',
  app: '宏调用',
  binop: '冲突运算',
  neg: '取负',
};

function lineColIndex(source) {
  const starts = [0];
  for (let i = 0; i < source.length; i++) if (source[i] === '\n') starts.push(i + 1);
  return (offset) => {
    let lo = 0;
    let hi = starts.length - 1;
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if (starts[mid] <= offset) lo = mid;
      else hi = mid - 1;
    }
    return { line: lo + 1, col: offset - starts[lo] + 1 };
  };
}

function snippet(source, node) {
  const s = source.slice(node.span.start, node.span.end).replace(/\s+/g, ' ').trim();
  return s.length > 60 ? `${s.slice(0, 57)}…` : s;
}

function fmtSpanPos(lc, s) {
  const a = lc(s.start);
  const b = lc(Math.max(s.start, s.end - 1));
  return {
    start: s.start,
    end: s.end,
    label: s.label || '',
    startLine: a.line,
    startCol: a.col,
    endLine: b.line,
    endCol: b.col + 1,
  };
}

function fmtSpans(source, spans) {
  const lc = lineColIndex(source);
  return (spans || []).map((s) => fmtSpanPos(lc, s));
}

function errorResult(source, message, spans, sliceInfo) {
  // 出错响应不携带任何成功结论（expressions 等），由页面清除旧结论
  return { ok: false, error: { message, spans: fmtSpans(source, spans), slice: sliceInfo || null } };
}

/* ---------------- 切片序列化（页面高亮 + 点选传播链） ---------------- */

function serializeSlice(source, prog, slice) {
  const lc = lineColIndex(source);
  const nodeById = new Map(prog.nodes.map((n) => [n.id, n]));
  const stepById = new Map(slice.steps.map((s) => [s.factId, s]));

  // 事实依赖的正向图：前提 -> 依赖它的后续事实（仅保留切片内事实）
  const dependents = new Map();
  for (const s of slice.steps) {
    for (const d of s.deps) {
      if (!stepById.has(d)) continue;
      if (!dependents.has(d)) dependents.set(d, []);
      dependents.get(d).push(s.factId);
    }
  }

  /**
   * 片段传播链：从该片段事实沿「谁依赖了它」正向闭包到冲突点；
   * 再对途中（不含冲突点本身——它是唯一同时连接两侧的事实，展开其前提会
   * 串入另一侧）事实的依赖做不动点回补，把实例化、let 泛化、参数绑定、
   * 调用约束等跨宏环节补全，得到「声明 → 实例化 → 调用合一 → 冲突」的完整链。
   */
  const chainFor = (factIds) => {
    const toStep = (fid) => {
      const s = stepById.get(fid);
      return {
        factId: fid,
        title: s.title,
        detail: s.detail,
        kind: s.kind,
        nodeId: s.nodeId,
        isGoal: fid === slice.goalFactId,
      };
    };
    // 相加/冲突位置是两条传播链的汇合点：展示两侧如何在此归并到冲突
    if (factIds.includes(slice.goalFactId)) {
      return slice.steps.map((s) => s.factId).sort((a, b) => a - b).map(toStep);
    }
    const reached = new Set(factIds);
    const queue = [...factIds];
    while (queue.length) {
      const cur = queue.shift();
      if (cur === slice.goalFactId) continue; // 到冲突点为止，不向其后的求解步骤扩散
      for (const nx of dependents.get(cur) || []) {
        if (!reached.has(nx)) { reached.add(nx); queue.push(nx); }
      }
    }
    let changed = true;
    while (changed) {
      changed = false;
      for (const fid of [...reached]) {
        if (fid === slice.goalFactId) continue;
        const f = stepById.get(fid);
        if (!f) continue;
        for (const d of f.deps) {
          if (!reached.has(d) && stepById.has(d)) { reached.add(d); changed = true; }
        }
      }
    }
    return [...reached].sort((a, b) => a - b).map((fid) => {
      const s = stepById.get(fid);
      return {
        factId: fid,
        title: s.title,
        detail: s.detail,
        kind: s.kind,
        nodeId: s.nodeId,
        isGoal: fid === slice.goalFactId,
      };
    });
  };

  const pushFragment = (out, start, end, role, nodeId, factIds) => {
    const a = lc(start);
    const b = lc(Math.max(start, end - 1));
    out.push({
      nodeId,
      role,
      text: source.slice(start, end).replace(/\s+/g, ' ').trim(),
      start,
      end,
      startLine: a.line,
      startCol: a.col,
      endLine: b.line,
      endCol: b.col + 1,
      factIds: [...factIds],
      chain: null,
    });
  };

  const fragments = [];
  for (const nodeId of slice.nodeIds) {
    const n = nodeById.get(nodeId);
    if (!n) continue;
    const factIds = slice.steps.filter((s) => s.nodeId === nodeId).map((s) => s.factId);
    pushFragment(fragments, n.span.start, n.span.end, NODE_ROLE[n.kind] || '相关片段', n.id, factIds);

    // 可独立点选的子区间：运算位置（+/-/* 或 /）与函数参数绑定（x）
    if (n.kind === 'binop' && n.opSpan) {
      const opFacts = slice.steps
        .filter((s) => s.nodeId === n.id && (s.kind === 'binop' || s.kind === 'unit-combine'))
        .map((s) => s.factId);
      pushFragment(
        fragments,
        n.opSpan.start,
        n.opSpan.end,
        n.op === '+' || n.op === '-' ? '相加位置' : '单位组合位置',
        n.id,
        opFacts.length ? opFacts : factIds,
      );
    }
    if (n.kind === 'fun' && n.paramSpan) {
      const bindFacts = slice.steps
        .filter((s) => s.nodeId === n.id && s.kind === 'bind')
        .map((s) => s.factId);
      if (bindFacts.length) {
        pushFragment(fragments, n.paramSpan.start, n.paramSpan.end, '参数绑定', n.id, bindFacts);
      }
    }
  }
  fragments.sort((x, y) => x.start - y.start || x.end - y.end || x.nodeId - y.nodeId);
  for (const f of fragments) f.chain = chainFor(f.factIds);

  const steps = slice.steps.map((s) => ({
    factId: s.factId,
    kind: s.kind,
    title: s.title,
    detail: s.detail,
    nodeId: s.nodeId,
    deps: s.deps,
    isGoal: s.factId === slice.goalFactId,
  }));

  return { headline: slice.headline, conflict: slice.conflict, steps, fragments };
}

/** 对源码完成「解析 + Hindley–Milner 主类型推断」，返回 API 形状的结果。 */
function runInference(source) {
  let prog;
  try {
    prog = parse(source);
  } catch (e) {
    if (e instanceof ParseError) return errorResult(source, e.message, e.spans);
    throw e;
  }
  const ctx = newCtx(prog.unitSrcs);
  let last;
  try {
    last = inferProgram(ctx, prog.statements);
  } catch (e) {
    if (e instanceof InferError) {
      const slice = e.slice ? serializeSlice(source, prog, e.slice) : null;
      return errorResult(source, e.message, e.spans, slice);
    }
    if (e instanceof U.UnifyError) {
      const ie = enrichUnify(ctx, e, { span: { start: 0, end: source.length }, id: -1 });
      const slice = ie.slice ? serializeSlice(source, prog, ie.slice) : null;
      return errorResult(source, ie.message, ie.spans, slice);
    }
    throw e;
  }
  const R = ctx.R;
  const lc = lineColIndex(source);
  for (const node of prog.nodes) {
    const t = ctx.nodeType.get(node.id);
    if (t) pushEvent(ctx, node.id, `最终归约类型：${renderType(R, t)}`);
  }
  const expressions = prog.nodes
    .slice()
    .sort((a, b) => a.span.start - b.span.start || a.id - b.id)
    .map((node) => {
      const pos = lc(node.span.start);
      const t = ctx.nodeType.get(node.id);
      return {
        id: node.id,
        kind: node.kind === 'binop' ? `四则运算「${node.op}」` : KIND_LABEL[node.kind],
        snippet: snippet(source, node),
        line: pos.line,
        col: pos.col,
        type: t ? renderType(R, t) : '—',
        events: ctx.events.get(node.id) || [],
      };
    });
  const generalizable = ctx.lets.map((l) => ({
    name: l.name,
    scheme: renderScheme(R, l.scheme),
    quantified: [...l.scheme.tvars.map((v) => nameT(R, v)), ...l.scheme.uvars.map((v) => nameU(R, v))],
  }));
  return {
    ok: true,
    expressions,
    generalizable,
    output: last ? renderType(R, last) : '（无输出表达式）',
  };
}

module.exports = { runInference, InferError };
