'use strict';

const { parse, ParseError } = require('./parser');
const U = require('./units');

class InferError extends Error {
  constructor(message, spans, seeds = null, rootId = null) {
    super(message);
    this.name = 'InferError';
    this.spans = spans || [];
    this.seeds = seeds; // 冲突切片种子事实（首次不可合一约束 + 冲突两侧锚点）
    this.rootId = rootId; // 首次不可合一的约束事实 id（传播链终点）
  }
}

/* ---------------- 类型 ----------------
 * { kind:'tvar', id, instance }   类型变量（可绑定）
 * { kind:'num',  unit }           带单位数值
 * { kind:'fun',  param, ret }     单参数函数
 * 类型方案 scheme = { tvars, uvars, type }（let 绑定处泛化）
 */

/* ================================================================
 * 可追溯来源（provenance）
 *
 * 推断过程中每一步都登记为「事实」(fact)，事实之间以 deps 构成有向
 * 依赖图（后一步依赖它所归并的前一步）：
 *   tvar/uvar 出生  —— 该变量由哪个源码位置、哪一步引入；
 *   合一约束/绑定   —— 哪个调用（或运算）提出约束、变量被绑定到什么；
 *   单位组合        —— 乘除在哪一处把两个单位拼成结果单位；
 *   let 泛化        —— 类型方案在何处形成；
 *   实例化          —— 哪次宏引用把方案刷新为新鲜变量（边指向泛化点）。
 *
 * 单位指数项上附带不透明令牌（令牌即事实 id），随乘除/合一/实例化
 * 在单位结构中传播；类型变量则通过出生/绑定事实追踪。
 * 失败时从「首次不可合一」的约束事实与冲突两侧锚点反向闭包，再删去
 * 无路径到达种子的事实，即得到不可再删除任一项的最小冲突依据切片。
 * ================================================================ */

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

/* ---------------- 推断上下文：事实图 + 证据日志 ---------------- */

function newCtx() {
  return {
    tvarSeq: 0,
    uvarSeq: 0,
    R: createRenderCtx(),
    stack: [],
    events: new Map(),
    nodeType: new Map(),
    lets: [],
    factSeq: 0,
    factById: new Map(),
    tvBirth: new Map(), // tvar -> 出生事实 id
    uvBirth: new Map(), // uvar -> 出生事实 id
    tvBind: new Map(),  // tvar -> 绑定事实 id（只绑定一次）
    uvBind: new Map(),  // uvar -> 绑定事实 id
  };
}

function addFact(ctx, kind, role, node, label, deps, extra = {}) {
  const id = ++ctx.factSeq;
  const span = extra.span || node.span;
  const f = {
    id,
    seq: id,
    kind,
    role,
    nodeId: node.id,
    start: span.start,
    end: span.end,
    label,
    deps: [...new Set([...deps].filter((d) => d !== null && d !== undefined))],
    tvar: extra.tvar || null,
    uvar: extra.uvar || null,
  };
  ctx.factById.set(id, f);
  return f;
}

/** 引入类型变量并登记出生事实（可附带来源依赖，如实例化边）。 */
function birthTVar(ctx, node, role, label, deps = [], span = null) {
  const v = { kind: 'tvar', id: ++ctx.tvarSeq, instance: null };
  const f = addFact(ctx, 'tvar', role, node, label, deps, { tvar: v, span });
  ctx.tvBirth.set(v, f.id);
  return v;
}

/** 引入单位变量并登记出生事实；返回携带来源令牌的单项式。 */
function birthUVarMono(ctx, node, role, label, deps = [], span = null) {
  const v = { id: ++ctx.uvarSeq, instance: null, prov: null };
  const f = addFact(ctx, 'uvar', role, node, label, deps, { uvar: v, span });
  v.prov = new Set([f.id]); // 单位层令牌即事实 id
  ctx.uvBirth.set(v, f.id);
  return U.monoVar(v, 1, v.prov);
}

/* ---------------- 类型/单位中现存事实锚点 ---------------- */

function scanMono(ctx, m, out) {
  // 归约后单项式上的全部令牌（传感器声明、组合点、实例化后代等）
  for (const p of U.collectProv(m)) out.add(p);
  // 穿过已绑定的单位变量：绑定事实不可绕过
  for (const [v] of m.vars) {
    if (v.instance) {
      const b = ctx.uvBind.get(v);
      if (b) out.add(b);
      scanMono(ctx, v.instance, out);
    }
  }
  return out;
}

/** 一个类型当前牵涉到的全部事实锚点（未归约穿越绑定链）。 */
function anchorsType(ctx, t, out = new Set()) {
  if (t.kind === 'tvar') {
    if (t.instance) {
      // 已绑定变量：绑定事实不可绕过，再深入绑定值
      out.add(ctx.tvBind.get(t));
      return anchorsType(ctx, t.instance, out);
    }
    out.add(ctx.tvBirth.get(t));
    return out;
  }
  if (t.kind === 'num') return scanMono(ctx, t.unit, out);
  anchorsType(ctx, t.param, out);
  anchorsType(ctx, t.ret, out);
  return out;
}

/* ---------------- 合一（记录每一步绑定事实） ---------------- */

function bindTVar(ctx, a, b, fid, binds) {
  if (occursTVar(a, b)) throw new U.UnifyError('occurs', { v: a, t: b });
  a.instance = b;
  log(ctx, `合一约束：${nameT(ctx.R, a)} := ${renderType(ctx.R, b)}`);
  const bf = addFact(
    ctx,
    'bind',
    '类型变量合一',
    ctx.stack[ctx.stack.length - 1] || { id: 0, span: { start: 0, end: 0 } },
    `类型合一：${nameT(ctx.R, a)} := ${renderType(ctx.R, b)}`,
    // 同一约束内靠后的方程会看到先前的绑定：绑定链不可断开
    [fid, ctx.tvBirth.get(a), ...binds],
    { tvar: a },
  );
  ctx.tvBind.set(a, bf.id);
  binds.push(bf.id);
}

function unifyRaw(ctx, t1, t2, fid, binds) {
  const a = prune(t1);
  const b = prune(t2);
  if (a === b) return;
  const top = ctx.stack[ctx.stack.length - 1] || { id: 0, span: { start: 0, end: 0 } };
  if (a.kind === 'tvar') {
    bindTVar(ctx, a, b, fid, binds);
    return;
  }
  if (b.kind === 'tvar') {
    bindTVar(ctx, b, a, fid, binds);
    return;
  }
  if (a.kind !== b.kind) throw new U.UnifyError('type-mismatch', { t1: a, t2: b });
  if (a.kind === 'fun') {
    unifyRaw(ctx, a.param, b.param, fid, binds);
    unifyRaw(ctx, a.ret, b.ret, fid, binds);
    return;
  }
  U.unifyMonos(a.unit, b.unit, (v) => {
    const bf = addFact(
      ctx,
      'ubind',
      '单位变量合一',
      top,
      `单位变量求解：${nameU(ctx.R, v)} := ${renderMono(ctx.R, v.instance)}`,
      [fid, ctx.uvBirth.get(v), ...binds],
      { uvar: v },
    );
    ctx.uvBind.set(v, bf.id);
    binds.push(bf.id);
  });
  log(ctx, `单位合一成功：两侧单位归一为 ${renderMono(ctx.R, a.unit)}`);
}

/**
 * 登记一条合一约束事实并执行合一。
 * 失败时把「该约束事实 + 两侧全部锚点」附在 UnifyError 上，
 * 作为最小冲突切片的反向归并种子（首次不可合一处）。
 */
function constrainUnify(ctx, node, role, label, t1, t2, extraDeps = []) {
  const deps = new Set([...anchorsType(ctx, t1), ...anchorsType(ctx, t2), ...extraDeps]);
  const f = addFact(ctx, 'constraint', role, node, label, deps);
  const binds = [];
  try {
    unifyRaw(ctx, t1, t2, f.id, binds);
  } catch (e) {
    if (e instanceof U.UnifyError) {
      e.factId = f.id;
      e.anchors = new Set([...anchorsType(ctx, t1), ...anchorsType(ctx, t2), ...extraDeps]);
    }
    throw e;
  }
  return f.id;
}

/* ---------------- 泛化与实例化 ---------------- */

function generalize(ctx, env, type) {
  const envFree = freeVarsEnv(env);
  const qt = [...freeTVars(type, new Set())].filter((v) => !envFree.t.has(v));
  const qu = [...freeUVars(type, new Set())].filter((v) => !envFree.u.has(v));
  return { tvars: qt, uvars: qu, type };
}

function substType(t, tMap, uMap) {
  t = prune(t);
  if (t.kind === 'tvar') return tMap.get(t) || t;
  if (t.kind === 'num') return { kind: 'num', unit: U.substMono(t.unit, uMap) };
  return { kind: 'fun', param: substType(t.param, tMap, uMap), ret: substType(t.ret, tMap, uMap) };
}

/** let 绑定的每次引用都重新实例化类型方案（新鲜变量，互不影响）。 */
function instantiate(ctx, sc, node, genFactId, name) {
  const R = ctx.R;
  const tMap = new Map();
  const uMap = new Map();
  if (sc.tvars.length === 0 && sc.uvars.length === 0) {
    const f = addFact(
      ctx,
      'ref',
      '标识符引用',
      node,
      `引用「${name}」：${renderType(R, sc.type)}`,
      [...anchorsType(ctx, sc.type), ...(genFactId ? [genFactId] : [])],
    );
    return { t: sc.type, factId: f.id };
  }
  // 实例化事实：边指向 let 泛化点（跨宏调用传播链由此贯通）
  const inst = addFact(
    ctx,
    'instantiate',
    '方案实例化（宏调用）',
    node,
    `引用「${name}」：类型方案 ${renderScheme(R, sc)} 在此处重新实例化（新鲜变量，与其他引用互不影响）`,
    genFactId ? [genFactId] : [],
  );
  for (const v of sc.tvars) {
    // 同一量化变量的所有出现共享一个新鲜副本（a -> a 的两个 a 必须一致）
    tMap.set(v, birthTVar(ctx, node, '实例化类型变量', `实例化新鲜类型变量（${name}：来自方案 ${renderScheme(R, sc)}）`, [inst.id]));
  }
  for (const v of sc.uvars) {
    const m = birthUVarMono(ctx, node, '实例化单位变量', `实例化新鲜单位变量（${name}：来自方案 ${renderScheme(R, sc)}）`, [inst.id]);
    uMap.set(v, m);
  }
  return { t: substType(sc.type, tMap, uMap), factId: inst.id };
}

/* ---------------- 证据日志（成功路径，行为保持不变） ---------------- */

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

function dispatch(ctx, env, node) {
  const R = ctx.R;
  switch (node.kind) {
    case 'sensor': {
      const t = { kind: 'num', unit: node.unit };
      const f = addFact(
        ctx,
        'sensor',
        '传感器声明（单位来源）',
        node,
        `传感器声明「${node.name}」：读数类型 ${renderType(R, t)}，单位由此处引入`,
        [],
      );
      U.tagMono(node.unit, f.id);
      env.set(node.name, { tvars: [], uvars: [], type: t, genFactId: null });
      log(ctx, `传感器声明「${node.name}」：${renderType(R, t)}`);
      return t;
    }
    case 'num': {
      if (node.unit) {
        const t = { kind: 'num', unit: node.unit };
        const f = addFact(
          ctx,
          'literal',
          '数值字面量（显式单位）',
          node,
          `数值 ${node.text}：显式标注单位，类型 ${renderType(R, t)}`,
          [],
        );
        U.tagMono(node.unit, f.id);
        log(ctx, `数值 ${node.text}：标注单位，类型 ${renderType(R, t)}`);
        return t;
      }
      const unit = birthUVarMono(ctx, node, '数值单位变量', `数值 ${node.text}：引入单位变量，具体单位由上下文约束确定`);
      const t = { kind: 'num', unit };
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
      const { t } = instantiate(ctx, sc, node, sc.genFactId || null, node.name);
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
      const paramSpan = node.paramSpan || node.span;
      // 函数体归并事实先建立（体推断失败时它也在切片中），标签在归并后补全
      const funFact = addFact(
        ctx,
        'fun',
        '函数体',
        node,
        `函数「${node.param} -> …」：函数体类型正在归并`,
        [],
      );
      const tv = birthTVar(ctx, node, '参数绑定', `引入参数「${node.param}」：绑定类型变量`, [funFact.id], paramSpan);
      funFact.deps.push(ctx.tvBirth.get(tv));
      log(ctx, `引入参数「${node.param}」：类型变量 ${nameT(R, tv)}`);
      ctx.factById.get(ctx.tvBirth.get(tv)).label = `引入参数「${node.param}」：绑定类型变量 ${nameT(R, tv)}`;
      const env2 = new Map(env);
      env2.set(node.param, { tvars: [], uvars: [], type: tv, genFactId: null });
      const tb = inferNode(ctx, env2, node.body);
      const ft = { kind: 'fun', param: tv, ret: tb };
      funFact.role = '函数体类型归并';
      funFact.label = `函数体归并：参数与返回值经函数体约束得到 ${renderType(R, ft)}`;
      for (const d of anchorsType(ctx, ft)) if (!funFact.deps.includes(d)) funFact.deps.push(d);
      log(ctx, `函数类型归并：${renderType(R, ft)}`);
      return ft;
    }
    case 'app': {
      const tf = inferNode(ctx, env, node.func);
      const ta = inferNode(ctx, env, node.arg);
      const beta = birthTVar(ctx, node, '调用结果变量', '调用：引入结果类型变量');
      log(ctx, `调用约束：函数类型 ${renderType(R, tf)} 须与 ${renderType(R, ta)} -> ${nameT(R, beta)} 合一`);
      ctx.factById.get(ctx.tvBirth.get(beta)).label = `调用结果类型变量 ${nameT(R, beta)}`;
      try {
        constrainUnify(
          ctx,
          node,
          '调用约束',
          `调用约束：${renderType(R, tf)} 须与 ${renderType(R, ta)} -> ${nameT(R, beta)} 合一（实参绑定到形参）`,
          tf,
          { kind: 'fun', param: ta, ret: beta },
          [ctx.tvBirth.get(beta)],
        );
      } catch (e) {
        if (e instanceof U.UnifyError) throw appError(ctx, node, e, tf, ta);
        throw e;
      }
      log(ctx, `调用结果类型：${renderType(R, beta)}`);
      return beta;
    }
    case 'neg': {
      const te = inferNode(ctx, env, node.expr);
      const unit = birthUVarMono(ctx, node, '取负单位变量', '取负运算：引入结果单位变量');
      const t = { kind: 'num', unit };
      try {
        constrainUnify(ctx, node, '取负约束', `取负运算要求数值类型：${renderType(R, te)} 须为数值`, te, t);
      } catch (e) {
        if (e instanceof U.UnifyError) {
          throw new InferError(`取负运算要求数值类型，但此处为 ${renderType(R, te)}`, [
            spanOf(node.expr, `非数值类型：${renderType(R, te)}`),
          ], seedsOf(e), rootOf(e));
        }
        throw e;
      }
      return t;
    }
    case 'binop':
      return inferBinop(ctx, env, node);
    case 'let': {
      const tv = inferNode(ctx, env, node.value);
      const sc0 = generalize(ctx, env, tv);
      const gen = addFact(
        ctx,
        'generalize',
        'let 泛化（类型方案形成）',
        node,
        `let 绑定「${node.name}」在此处泛化为类型方案 ${renderScheme(R, sc0)}；每次引用独立实例化`,
        [...anchorsType(ctx, tv)],
      );
      const sc = { ...sc0, genFactId: gen.id };
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
    const t = { kind: 'num', unit: birthUVarMono(ctx, node, '加减结果单位变量', `「${node.op}」结果单位变量`) };
    log(ctx, `「${node.op}」约束：两侧须为相同单位的数值；左侧 ${renderType(R, tl)}，右侧 ${renderType(R, tr)}`);
    try {
      const fid = constrainUnify(
        ctx,
        node,
        '加减同单位约束',
        `「${node.op}」约束：左侧 ${renderType(R, tl)} 须与结果单位一致`,
        tl,
        t,
      );
      constrainUnify(
        ctx,
        node,
        '加减同单位约束',
        `「${node.op}」约束：右侧 ${renderType(R, tr)} 须与结果单位一致（左右单位因此必须相同）`,
        tr,
        t,
        [fid],
      );
    } catch (e) {
      if (e instanceof U.UnifyError) throw binopError(ctx, node, e, tl, tr);
      throw e;
    }
    log(ctx, `「${node.op}」结果类型：${renderType(R, t)}`);
    return t;
  }
  // 乘除：组合单位
  const ua = birthUVarMono(ctx, node, '乘除左单位变量', `「${node.op}」：左操作数单位变量`);
  const ub = birthUVarMono(ctx, node, '乘除右单位变量', `「${node.op}」：右操作数单位变量`);
  try {
    constrainUnify(ctx, node, '乘除数值约束', `「${node.op}」要求左操作数为数值：${renderType(R, tl)}`, tl, { kind: 'num', unit: ua });
    constrainUnify(ctx, node, '乘除数值约束', `「${node.op}」要求右操作数为数值：${renderType(R, tr)}`, tr, { kind: 'num', unit: ub });
  } catch (e) {
    if (e instanceof U.UnifyError) throw binopError(ctx, node, e, tl, tr);
    throw e;
  }
  const ru = node.op === '*' ? U.monoMul(ua, ub) : U.monoDiv(ua, ub);
  const cf = addFact(
    ctx,
    'combine',
    '单位组合',
    node,
    `「${node.op}」单位组合：${renderMono(R, ua)} ${node.op} ${renderMono(R, ub)} ⇒ ${renderMono(R, ru)}`,
    [...anchorsType(ctx, { kind: 'num', unit: ua }), ...anchorsType(ctx, { kind: 'num', unit: ub })],
  );
  U.tagMono(ru, cf.id);
  log(ctx, `「${node.op}」单位组合：${renderMono(R, ua)} ${node.op} ${renderMono(R, ub)} ⇒ ${renderMono(R, ru)}`);
  return { kind: 'num', unit: ru };
}

function seedsOf(e) {
  if (!e || e.factId === undefined) return null;
  return new Set([e.factId, ...(e.anchors || [])]);
}

function rootOf(e) {
  return e && e.factId !== undefined ? e.factId : null;
}

/* ---------------- 错误加工（消息保持、携带切片种子） ---------------- */

function binopError(ctx, node, e, tl, tr) {
  const R = ctx.R;
  const seeds = seedsOf(e);
  if (e.kind === 'unit-mismatch') {
    // 直接冲突：保留「两个操作数」定位契约；切片另附完整跨宏依据
    return new InferError(
      `单位不匹配：「${node.op}」要求两侧单位相同，但左操作数为 ${renderType(R, tl)}、右操作数为 ${renderType(R, tr)}`,
      [spanOf(node.left, `左操作数：${renderType(R, tl)}`), spanOf(node.right, `右操作数：${renderType(R, tr)}`)],
      seeds,
      rootOf(e),
    );
  }
  if (e.kind === 'type-mismatch') {
    const badLeft = prune(tl).kind !== 'num';
    const badT = badLeft ? tl : tr;
    return new InferError(
      `「${node.op}」的操作数须为数值类型，但${badLeft ? '左' : '右'}侧为 ${renderType(R, badT)}`,
      [spanOf(badLeft ? node.left : node.right, `非数值类型：${renderType(R, badT)}`)],
      seeds,
      rootOf(e),
    );
  }
  return enrichUnify(ctx, e, node);
}

function appError(ctx, node, e, tf, ta) {
  const R = ctx.R;
  const seeds = seedsOf(e);
  if (e.kind === 'occurs') {
    return new InferError(
      `无限类型：类型变量 ${nameT(R, e.v)} 出现在 ${renderType(R, e.t)} 中，自应用无法构造有限类型（occurs check 失败）`,
      [spanOf(node, '自应用调用'), spanOf(node.func, '被调用表达式'), spanOf(node.arg, '实参')],
      seeds,
      rootOf(e),
    );
  }
  if (e.kind === 'type-mismatch') {
    return new InferError(
      `类型不匹配：试图调用非函数类型 ${renderType(R, tf)}`,
      [spanOf(node.func, `非函数类型：${renderType(R, tf)}`), spanOf(node.arg, `实参：${renderType(R, ta)}`)],
      seeds,
      rootOf(e),
    );
  }
  if (e.kind === 'unit-mismatch') {
    return new InferError(
      `单位不匹配：实参单位与形参要求不符（${renderMono(R, e.u1)} 与 ${renderMono(R, e.u2)}）`,
      [spanOf(node.arg, `实参：${renderType(R, ta)}`), spanOf(node.func, `形参要求：${renderType(R, tf)}`)],
      seeds,
      rootOf(e),
    );
  }
  return enrichUnify(ctx, e, node);
}

function enrichUnify(ctx, e, node) {
  const R = ctx.R;
  const seeds = seedsOf(e);
  switch (e.kind) {
    case 'occurs':
      return new InferError(
        `无限类型：类型变量 ${nameT(R, e.v)} 出现在 ${renderType(R, e.t)} 中（occurs check 失败）`,
        null,
        seeds,
        rootOf(e),
      );
    case 'type-mismatch':
      return new InferError(
        `类型不匹配：${renderType(R, e.t1)} 与 ${renderType(R, e.t2)} 无法统一`,
        null,
        seeds,
        rootOf(e),
      );
    case 'unit-mismatch':
      return new InferError(
        `单位不匹配：${renderMono(R, e.u1)} 与 ${renderMono(R, e.u2)} 无法统一`,
        null,
        seeds,
        rootOf(e),
      );
    case 'occurs-unit':
      return new InferError('无限单位类型：单位变量出现在其自身定义中（occurs check 失败）', null, seeds, rootOf(e));
    default:
      return new InferError(`类型错误：${e.message}`, [spanOf(node, '错误位置')], seeds, rootOf(e));
  }
}

/* ---------------- 最小冲突依据切片 ---------------- */

/**
 * 从种子事实出发沿依赖边反向闭包：
 *  - deps：该步归并所依据的前序事实（出生、前一条约束、泛化点、同一约束
 *    内在先的绑定等）；
 *  - 出生事实 -> 该变量的绑定事实（单位/类型经哪一步被传递）；
 *  - 实例化新鲜变量出生 -> 实例化点 -> let 泛化点（跨宏调用）。
 * 闭包内每个事实都能沿依赖到达种子，删去任一项都会断开传播链，
 * 因此即为最小冲突依据。
 */
function buildSlice(ctx, seeds) {
  const needed = new Set();
  const wl = [];
  const push = (id) => {
    if (id !== null && id !== undefined && !needed.has(id) && ctx.factById.has(id)) wl.push(id);
  };
  for (const s of seeds || []) push(s);
  while (wl.length) {
    const id = wl.pop();
    if (needed.has(id)) continue;
    needed.add(id);
    const f = ctx.factById.get(id);
    for (const d of f.deps) push(d);
    if (f.tvar) {
      push(ctx.tvBirth.get(f.tvar));
      push(ctx.tvBind.get(f.tvar));
    }
    if (f.uvar) {
      push(ctx.uvBirth.get(f.uvar));
      push(ctx.uvBind.get(f.uvar));
    }
  }
  const facts = [...needed]
    .map((id) => ctx.factById.get(id))
    .sort((a, b) => a.seq - b.seq || a.id - b.id);
  return { needed, facts };
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

function snippetAt(source, start, end) {
  const s = source.slice(start, end).replace(/\s+/g, ' ').trim();
  return s.length > 60 ? `${s.slice(0, 57)}…` : s;
}

function fmtSpan(lc, source, s) {
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
    snippet: snippetAt(source, s.start, s.end),
  };
}

function fmtSpans(source, spans) {
  const lc = lineColIndex(source);
  return (spans || []).map((s) => fmtSpan(lc, source, s));
}

/** 把切片组织为 API 形状：源码片段 + 按推导顺序的步骤（依赖边另附）。 */
function formatSlice(ctx, source, slice, rootFactId) {
  const lc = lineColIndex(source);
  const facts = slice.facts.map((f) => {
    const a = lc(f.start);
    return {
      id: f.id,
      kind: f.kind,
      role: f.role,
      label: f.label,
      deps: f.deps.filter((d) => slice.needed.has(d)),
      start: f.start,
      end: f.end,
      snippet: snippetAt(source, f.start, f.end),
      line: a.line,
      col: a.col,
    };
  });
  // 源码片段：切片内事实触及的互不相同区间（嵌套区间各自保留）
  const fragMap = new Map();
  for (const f of slice.facts) {
    const key = `${f.start}:${f.end}`;
    let g = fragMap.get(key);
    if (!g) {
      g = { start: f.start, end: f.end, factIds: [], roles: [] };
      fragMap.set(key, g);
    }
    g.factIds.push(f.id);
    if (!g.roles.includes(f.role)) g.roles.push(f.role);
  }
  const fragments = [...fragMap.values()]
    .sort((a, b) => a.start - b.start || b.end - a.end)
    .map((g) => ({
      ...fmtSpan(lc, source, g),
      label: g.roles.join('、'),
      factIds: g.factIds,
    }));
  return { rootFactId, facts, fragments, steps: facts.map((f) => f.id) };
}

function errorResult(source, message, spans, slice = null) {
  // 出错响应不携带任何成功结论（expressions 等），由页面清除旧结论
  const out = { ok: false, error: { message, spans: fmtSpans(source, spans) } };
  if (slice) out.error.slice = slice;
  return out;
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
  const ctx = newCtx();
  let last;
  try {
    last = inferProgram(ctx, prog.statements);
  } catch (e) {
    if (e instanceof InferError) {
      if (e.seeds && e.seeds.size) {
        const slice = formatSlice(ctx, source, buildSlice(ctx, e.seeds), e.rootId);
        const spans = e.spans.length ? e.spans : slice.fragments.map((f) => ({ start: f.start, end: f.end, label: f.label }));
        return errorResult(source, e.message, spans, slice);
      }
      return errorResult(source, e.message, e.spans);
    }
    if (e instanceof U.UnifyError) {
      const ie = enrichUnify(ctx, e, { span: { start: 0, end: source.length } });
      if (ie.seeds && ie.seeds.size) {
        const slice = formatSlice(ctx, source, buildSlice(ctx, ie.seeds), ie.rootId);
        return errorResult(source, ie.message, slice.fragments, slice);
      }
      return errorResult(source, ie.message, ie.spans);
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
