'use strict';

/**
 * 单位（量纲）单项式：基本单位与单位变量的整数次幂乘积。
 *   bases: Map<string, number>  例如 { m: 1, s: -1 } 表示 m/s
 *   vars:  Map<object, number>  单位变量（可泛化、可合一）
 *   src:   Set<number>          来源锚点（parser 中单位基元的源码区间 id）
 *   why:   Set<number>          传播到该单项式的来源事实 id（绑定/实例化/组合）
 * src 与 why 均随乘除/代换一路传播，供冲突依据切片追溯。
 */

class UnifyError extends Error {
  constructor(kind, data) {
    super(kind);
    this.name = 'UnifyError';
    this.kind = kind;
    Object.assign(this, data);
  }
}

function monoUnit(src = null, why = null) {
  return { bases: new Map(), vars: new Map(), src: new Set(src || []), why: new Set(why || []) };
}

function monoBase(name, exp = 1, src = null) {
  const m = monoUnit(src);
  if (exp !== 0) m.bases.set(name, exp);
  return m;
}

function monoVar(v, exp = 1, src = null) {
  const m = monoUnit(src);
  if (exp !== 0) m.vars.set(v, exp);
  return m;
}

function addBase(m, b, e, src = null, why = null) {
  const ne = (m.bases.get(b) || 0) + e;
  if (ne === 0) m.bases.delete(b);
  else m.bases.set(b, ne);
  if (src) for (const s of src) m.src.add(s);
  if (why) for (const w of why) m.why.add(w);
}

function addVar(m, v, e, src = null, why = null) {
  const ne = (m.vars.get(v) || 0) + e;
  if (ne === 0) m.vars.delete(v);
  else m.vars.set(v, ne);
  if (src) for (const s of src) m.src.add(s);
  if (why) for (const w of why) m.why.add(w);
}

function addInto(dst, src, k) {
  for (const [b, e] of src.bases) addBase(dst, b, k * e, src.src, src.why);
  for (const [v, e] of src.vars) addVar(dst, v, k * e, src.src, src.why);
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

/** 归约（zonk）：递归展开已绑定的单位变量。 */
function resolveMono(m) {
  const r = monoUnit(m.src, m.why);
  addResolved(r, m, 1);
  return r;
}

function addResolved(dst, m, k) {
  for (const [b, e] of m.bases) addBase(dst, b, k * e, m.src, m.why);
  for (const [v, e] of m.vars) {
    if (v.instance) {
      addResolved(dst, v.instance, k * e);
      // 经已绑定变量传播：变量自身的来源事实（绑定/实例化/求解）一并带入
      for (const w of v.why) dst.why.add(w);
    } else {
      addVar(dst, v, k * e, m.src, m.why);
    }
  }
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
 * onBind({ v, unit })：某单位变量被求解为 unit 时回调（供推断器登记来源事实）。
 * 失败抛出 UnifyError('unit-mismatch' | 'occurs-unit')。
 */
function unifyMonos(u1, u2, onBind = null) {
  const a = resolveMono(u1);
  const b = resolveMono(u2);
  if (monoEqual(a, b)) return;
  const av = bareVar(a);
  if (av) {
    if (occursUVar(av, b)) throw new UnifyError('occurs-unit', { v: av, u: b });
    av.instance = b;
    if (onBind) onBind({ v: av, unit: b });
    return;
  }
  const bv = bareVar(b);
  if (bv) {
    if (occursUVar(bv, a)) throw new UnifyError('occurs-unit', { v: bv, u: a });
    bv.instance = a;
    if (onBind) onBind({ v: bv, unit: a });
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
    const r = monoUnit(eq.src, eq.why);
    let solvable = true;
    for (const [bn, be] of eq.bases) {
      if (be % e !== 0) { solvable = false; break; }
      addBase(r, bn, -be / e, eq.src, eq.why);
    }
    if (solvable) {
      for (const [v2, e2] of eq.vars) {
        if (v2 === v) continue;
        if (e2 % e !== 0) { solvable = false; break; }
        addVar(r, v2, -e2 / e, eq.src, eq.why);
      }
    }
    if (solvable) {
      v.instance = r;
      if (onBind) onBind({ v, unit: r });
      return;
    }
  }
  throw new UnifyError('unit-mismatch', { u1: a, u2: b });
}

/** 以 uMap 中的单项式替换量化单位变量（实例化用）。 */
function substMono(m, uMap) {
  const rm = resolveMono(m);
  const r = monoUnit(rm.src, rm.why);
  for (const [b, e] of rm.bases) addBase(r, b, e, rm.src, rm.why);
  for (const [v, e] of rm.vars) {
    const rep = uMap.get(v);
    if (rep) addInto(r, rep, e);
    else addVar(r, v, e, rm.src, rm.why);
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
  resolveMono,
  monoEqual,
  unifyMonos,
  substMono,
  renderMono,
};
