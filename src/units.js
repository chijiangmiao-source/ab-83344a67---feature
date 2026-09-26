'use strict';

/**
 * 单位（量纲）单项式：基本单位与单位变量的整数次幂乘积。
 *   bases: Map<string, number>  例如 { m: 1, s: -1 } 表示 m/s
 *   vars:  Map<object, number>  单位变量（可泛化、可合一）
 *   bp/vp: 与 bases/vars 平行的来源令牌集合（provenance），
 *          只随结构传播，不参与相等判断与合一；令牌对单位层不透明（事实图 id）。
 */

class UnifyError extends Error {
  constructor(kind, data) {
    super(kind);
    this.name = 'UnifyError';
    this.kind = kind;
    Object.assign(this, data);
  }
}

function monoUnit() {
  return { bases: new Map(), vars: new Map(), bp: new Map(), vp: new Map() };
}

function mergeProv(map, key, prov) {
  if (!prov || prov.size === 0) return;
  const set = map.get(key);
  if (!set) map.set(key, new Set(prov));
  else for (const p of prov) set.add(p);
}

function monoBase(name, exp = 1, prov = null) {
  const m = monoUnit();
  if (exp !== 0) {
    m.bases.set(name, exp);
    mergeProv(m.bp, name, prov);
  }
  return m;
}

function monoVar(v, exp = 1, prov = null) {
  const m = monoUnit();
  if (exp !== 0) {
    m.vars.set(v, exp);
    mergeProv(m.vp, v, prov);
  }
  return m;
}

function addBase(m, b, e) {
  const ne = (m.bases.get(b) || 0) + e;
  if (ne === 0) {
    m.bases.delete(b);
    m.bp.delete(b);
  } else m.bases.set(b, ne);
}

function addVar(m, v, e) {
  const ne = (m.vars.get(v) || 0) + e;
  if (ne === 0) {
    m.vars.delete(v);
    m.vp.delete(v);
  } else m.vars.set(v, ne);
}

/** 把 src 的来源按指数倍并入 dst（指数只做符号传递，令牌去重）。 */
function addProvInto(dst, src) {
  for (const [b, ps] of src.bp) if (dst.bases.has(b)) mergeProv(dst.bp, b, ps);
  for (const [v, ps] of src.vp) if (dst.vars.has(v)) mergeProv(dst.vp, v, ps);
}

function addInto(dst, src, k) {
  for (const [b, e] of src.bases) addBase(dst, b, k * e);
  for (const [v, e] of src.vars) addVar(dst, v, k * e);
  addProvInto(dst, src);
}

function monoMul(a, b) {
  const r = monoUnit();
  addInto(r, a, 1);
  addInto(r, b, 1);
  return r;
}

function monoDiv(a, b) {
  const r = monoUnit();
  addInto(r, a, 1);
  addInto(r, b, -1);
  return r;
}

function monoPow(a, k) {
  const r = monoUnit();
  addInto(r, a, k);
  return r;
}

/** 把来源令牌贴到单项式的每一项（单位组合 / 结果单位事实用）。 */
function tagMono(m, token) {
  for (const b of m.bases.keys()) mergeProv(m.bp, b, [token]);
  for (const v of m.vars.keys()) mergeProv(m.vp, v, [token]);
  return m;
}

/** 归约（zonk）：递归展开已绑定的单位变量，来源随展开传播。 */
function resolveMono(m) {
  const r = monoUnit();
  addResolved(r, m, 1);
  return r;
}

/** 把令牌集合贴到单项式的每一个现存项。 */
function tagAll(mono, tokens) {
  if (!tokens || tokens.size === 0) return;
  for (const ps of mono.bp.values()) for (const t of tokens) ps.add(t);
  for (const ps of mono.vp.values()) for (const t of tokens) ps.add(t);
}

function addResolved(dst, m, k) {
  for (const [b, e] of m.bases) {
    addBase(dst, b, k * e);
    if (m.bp.has(b) && dst.bases.has(b)) mergeProv(dst.bp, b, m.bp.get(b));
  }
  for (const [v, e] of m.vars) {
    if (v.instance) {
      // 展开为临时单项式后整体并入：变量自身来源与该出现点来源随展开传播
      const sub = monoPow(resolveMono(v.instance), k * e);
      const extra = new Set(m.vp.get(v) || []);
      if (v.prov && v.prov.size) for (const p of v.prov) extra.add(p);
      tagAll(sub, extra);
      addInto(dst, sub, 1);
    } else {
      addVar(dst, v, k * e);
      if (m.vp.has(v)) mergeProv(dst.vp, v, m.vp.get(v));
      if (v.prov && v.prov.size) mergeProv(dst.vp, v, v.prov);
    }
  }
}

/** 收集归约后单项式中全部来源令牌。 */
function collectProv(m) {
  const r = resolveMono(m);
  const out = new Set();
  for (const ps of r.bp.values()) for (const p of ps) out.add(p);
  for (const ps of r.vp.values()) for (const p of ps) out.add(p);
  return out;
}

function monoEqual(a, b) {
  if (a.bases.size !== b.bases.size || a.vars.size !== b.vars.size) return false;
  for (const [k, e] of a.bases) if (b.bases.get(k) !== e) return false;
  for (const [v, e] of a.vars) if (b.vars.get(v) !== e) return false;
  return true;
}

/** 若单项式仅为一个一次单位变量，返回该变量。 */
function bareVar(m) {
  if (m.bases.size === 0 && m.vars.size === 1) {
    const [[v, e]] = m.vars;
    if (e === 1) return v;
  }
  return null;
}

function occursUVar(v, m) {
  return resolveMono(m).vars.has(v);
}

/**
 * 单位合一：在整数指数阿贝尔群上求解。
 * 失败抛出 UnifyError('unit-mismatch' | 'occurs-unit')。
 * onBind(v) 在单位变量被求解绑定（含方程消元）时回调，供推断层记录绑定事实。
 */
function unifyMonos(u1, u2, onBind = null) {
  const a = resolveMono(u1);
  const b = resolveMono(u2);
  if (monoEqual(a, b)) return;
  const av = bareVar(a);
  if (av) {
    if (occursUVar(av, b)) throw new UnifyError('occurs-unit', { v: av, u: b });
    av.instance = b;
    if (onBind) onBind(av);
    return;
  }
  const bv = bareVar(b);
  if (bv) {
    if (occursUVar(bv, a)) throw new UnifyError('occurs-unit', { v: bv, u: a });
    bv.instance = a;
    if (onBind) onBind(bv);
    return;
  }
  // 方程 a * b^-1 = 1：选取一个变量求解 v^e = R^-1（要求 R 的指数均可被 e 整除）
  const eq = monoDiv(a, b);
  let best = null;
  for (const [v, e] of eq.vars) {
    if (best === null || Math.abs(e) < Math.abs(best.e)) best = { v, e };
  }
  if (best) {
    const { v, e } = best;
    const r = monoUnit();
    let solvable = true;
    for (const [bn, be] of eq.bases) {
      if (be % e !== 0) { solvable = false; break; }
      addBase(r, bn, -be / e);
    }
    if (solvable) {
      for (const [v2, e2] of eq.vars) {
        if (v2 === v) continue;
        if (e2 % e !== 0) { solvable = false; break; }
        addVar(r, v2, -e2 / e);
      }
    }
    if (solvable) {
      v.instance = r;
      if (onBind) onBind(v);
      return;
    }
  }
  throw new UnifyError('unit-mismatch', { u1: a, u2: b });
}

/** 以 uMap 中的单项式替换量化单位变量（实例化用），来源随替换传播。 */
function substMono(m, uMap) {
  const rm = resolveMono(m);
  const r = monoUnit();
  for (const [b, e] of rm.bases) {
    addBase(r, b, e);
    if (rm.bp.has(b)) mergeProv(r.bp, b, rm.bp.get(b));
  }
  for (const [v, e] of rm.vars) {
    const rep = uMap.get(v);
    if (rep) addInto(r, rep, e);
    else {
      addVar(r, v, e);
      if (rm.vp.has(v)) mergeProv(r.vp, v, rm.vp.get(v));
    }
  }
  return r;
}

function renderMono(m, nameU) {
  const r = resolveMono(m);
  const parts = [];
  const bases = [...r.bases.entries()].sort((x, y) => (x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : 0));
  for (const [b, e] of bases) parts.push(e === 1 ? b : `${b}^${e}`);
  for (const [v, e] of r.vars) {
    const n = nameU(v);
    parts.push(e === 1 ? n : `${n}^${e}`);
  }
  return parts.length ? parts.join('*') : '1';
}

module.exports = {
  UnifyError,
  monoUnit,
  monoBase,
  monoVar,
  monoMul,
  monoDiv,
  monoPow,
  tagMono,
  resolveMono,
  collectProv,
  monoEqual,
  unifyMonos,
  substMono,
  renderMono,
};
