'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const { runInference } = require('../src/infer');

const IDENTITY_SCRIPT = `// 恒等宏跨量纲复用
sensor len : m;
sensor tim : s;
let id = fun x -> x;
let a = id len;
let b = id tim;
id len * id tim
`;

test('恒等宏跨量纲复用：两次实例化互不影响', () => {
  const r = runInference(IDENTITY_SCRIPT);
  assert.equal(r.ok, true);
  const typesOf = (s) => r.expressions.filter((e) => e.snippet === s).map((e) => e.type);
  assert.ok(typesOf('id len').length > 0);
  assert.ok(typesOf('id len').every((t) => t === 'num<m>'), '宏作用于长度读数应为 num<m>');
  assert.ok(typesOf('id tim').length > 0);
  assert.ok(typesOf('id tim').every((t) => t === 'num<s>'), '宏作用于时间读数应为 num<s>');
  assert.equal(r.output, 'num<m*s>');
  const idGen = r.generalizable.find((g) => g.name === 'id');
  assert.ok(idGen, 'id 应有类型方案');
  assert.match(idGen.scheme, /^∀ /);
  assert.equal(idGen.quantified.length, 1);
});

test('异单位相加：定位两个操作数且不保留成功结论', () => {
  const src = 'sensor a : m;\nsensor b : s;\na + b\n';
  const r = runInference(src);
  assert.equal(r.ok, false);
  assert.match(r.error.message, /单位不匹配/);
  assert.equal(r.error.spans.length, 2);
  const covered = r.error.spans.map((s) => src.slice(s.start, s.end));
  assert.deepEqual(covered, ['a', 'b']);
  assert.match(r.error.spans[0].label, /左操作数/);
  assert.match(r.error.spans[1].label, /右操作数/);
  assert.equal(r.expressions, undefined, '出错响应不得携带旧的成功结论');
});

test('自应用：稳定的无限类型错误与相关位置', () => {
  const src = 'let f = fun x -> x x;\nf\n';
  const r1 = runInference(src);
  const r2 = runInference(src);
  assert.equal(r1.ok, false);
  assert.match(r1.error.message, /无限类型/);
  assert.match(r1.error.message, /occurs check/);
  assert.ok(r1.error.spans.length >= 1, '应给出错误位置');
  const xx = r1.error.spans[0];
  assert.equal(src.slice(xx.start, xx.end), 'x x');
  assert.deepEqual(r1.error, r2.error, '重复推断错误应完全一致（稳定）');
});

test('未定义标识符：报错并定位', () => {
  const src = 'foo + 1\n';
  const r = runInference(src);
  assert.equal(r.ok, false);
  assert.match(r.error.message, /未定义标识符「foo」/);
  assert.equal(src.slice(r.error.spans[0].start, r.error.spans[0].end), 'foo');
});

test('乘除组合单位', () => {
  assert.equal(runInference('sensor a : m;\nsensor b : s;\na * b\n').output, 'num<m*s>');
  assert.equal(runInference('sensor a : m;\nsensor b : s;\na / b\n').output, 'num<m*s^-1>');
  assert.equal(runInference('sensor a : m;\na * a\n').output, 'num<m^2>');
  assert.equal(runInference('sensor a : m;\na / a\n').output, 'num<1>');
});

test('加减接受相同单位', () => {
  assert.equal(runInference('sensor a : m;\nsensor b : m;\na + b\n').output, 'num<m>');
  assert.equal(runInference('sensor a : m;\nsensor b : m;\na - b\n').output, 'num<m>');
});

test('数值字面量单位多态；带单位标注的字面量', () => {
  const r = runInference('let f = fun x -> x + 1;\nf\n');
  assert.equal(r.ok, true);
  const m = r.output.match(/^num<('u\d+)> -> num<('u\d+)>$/);
  assert.ok(m, `输出应为单位多态函数，实际：${r.output}`);
  assert.equal(m[1], m[2], '加减要求两侧单位一致');
  assert.equal(runInference('3.5<m/s>\n').output, 'num<m*s^-1>');
  assert.equal(runInference('9.8<m/s^2>\n').output, 'num<m*s^-2>');
});

test('let 多态：同一宏用于具体量纲与多态字面量', () => {
  const r = runInference('sensor a : m;\nlet id = fun x -> x;\nlet p = id a;\nlet q = id 1.5;\nq\n');
  assert.equal(r.ok, true);
  assert.match(r.output, /^num<'u\d+>$/);
  const p = r.generalizable.find((g) => g.name === 'p');
  assert.equal(p.scheme, 'num<m>');
  assert.equal(p.quantified.length, 0);
});

test('高阶单位多态：fun x -> x * x', () => {
  const r = runInference('sensor a : m;\nlet sq = fun x -> x * x;\nsq a\n');
  assert.equal(r.ok, true);
  assert.equal(r.output, 'num<m^2>');
  const sq = r.generalizable.find((g) => g.name === 'sq');
  assert.match(sq.scheme, /^∀ 'u\d+\. num<'u\d+> -> num<'u\d+\^2>$/);
});

test('传感器复合单位声明', () => {
  assert.equal(runInference('sensor v : m/s;\nv\n').output, 'num<m*s^-1>');
  assert.equal(runInference('sensor a : m^2;\na\n').output, 'num<m^2>');
  assert.equal(runInference('sensor x : 1;\nx\n').output, 'num<1>');
});

test('let-in 表达式形式', () => {
  const r = runInference('let id = fun x -> x in id 1\n');
  assert.equal(r.ok, true);
  assert.match(r.output, /^num<'u\d+>$/);
});

test('调用非函数：类型不匹配并定位', () => {
  const r = runInference('sensor a : m;\na a\n');
  assert.equal(r.ok, false);
  assert.match(r.error.message, /类型不匹配|非函数/);
  assert.ok(r.error.spans.length >= 1);
});

test('实参单位与形参不符：单位不匹配', () => {
  const r = runInference('sensor a : m;\nsensor b : s;\nlet f = fun x -> x + a;\nf b\n');
  assert.equal(r.ok, false);
  assert.match(r.error.message, /单位不匹配/);
});

test('解析错误定位', () => {
  const r = runInference('let = 1;\n');
  assert.equal(r.ok, false);
  assert.ok(r.error.spans.length >= 1);
});

test('成功表达式携带约束归并依据（事件）', () => {
  const r = runInference(IDENTITY_SCRIPT);
  const app = r.expressions.find((e) => e.snippet === 'id len');
  assert.ok(app, '应存在调用表达式 id len');
  assert.ok(app.events.some((s) => /约束|合一/.test(s)), '调用节点应记录合一约束');
  assert.ok(app.events.some((s) => /最终归约类型：num<m>/.test(s)));
  const idRef = r.expressions.find((e) => e.kind === '标识符' && e.snippet === 'id');
  assert.ok(idRef.events.some((s) => /实例化/.test(s)), '宏引用应记录方案实例化');
});

test('推断确定性：同一脚本两次结果完全一致', () => {
  const a = runInference(IDENTITY_SCRIPT);
  const b = runInference(IDENTITY_SCRIPT);
  assert.deepEqual(a, b);
});

/* ---------------- 冲突依据切片 ---------------- */

const INDIRECT_SCRIPT = `sensor len : m;
sensor tim : s;
let id = fun x -> x;
id len + id tim
`;

test('恒等宏间接传递相加：切片含两份传感器声明、相应调用与相加位置', () => {
  const r = runInference(INDIRECT_SCRIPT);
  assert.equal(r.ok, false);
  assert.match(r.error.message, /单位不匹配/);
  assert.ok(r.error.slice, '失败响应应携带冲突依据切片');
  const frags = r.error.slice.fragments.map((f) => INDIRECT_SCRIPT.slice(f.start, f.end));
  for (const need of ['sensor len : m', 'sensor tim : s', 'id len', 'id tim', 'id len + id tim']) {
    assert.ok(frags.includes(need), `切片必须包含「${need}」，实际：${JSON.stringify(frags)}`);
  }
  // 宏定义与实例化边也在切片中（跨宏调用传播链由此贯通）
  assert.ok(frags.includes('let id = fun x -> x'), '切片应包含宏定义（let 泛化点）');
  assert.ok(frags.includes('fun x -> x'), '切片应包含宏函数体');
  const kinds = new Set(r.error.slice.facts.map((f) => f.kind));
  assert.ok(kinds.has('instantiate'), '切片应含宏实例化事实');
  assert.ok(kinds.has('generalize'), '切片应含 let 泛化事实');
  assert.ok(kinds.has('constraint'), '切片应含合一约束事实');
  // 主定位仍保持「两个操作数」契约
  assert.equal(r.error.spans.length, 2);
  assert.equal(INDIRECT_SCRIPT.slice(r.error.spans[0].start, r.error.spans[0].end), 'id len');
  assert.equal(INDIRECT_SCRIPT.slice(r.error.spans[1].start, r.error.spans[1].end), 'id tim');
  assert.equal(r.expressions, undefined, '出错响应不得携带旧的成功结论');
});

test('冲突切片按推导顺序展示且从首次不可合一处反向归并', () => {
  const r = runInference(INDIRECT_SCRIPT);
  const { facts, steps, rootFactId } = r.error.slice;
  assert.deepEqual(steps, facts.map((f) => f.id), '步骤即按推导顺序排列的事实');
  const seqs = facts.map((f) => f.id);
  assert.deepEqual(seqs, [...seqs].sort((a, b) => a - b), '推导顺序按事实登记先后');
  const root = facts.find((f) => f.id === rootFactId);
  assert.ok(root, '切片应标注首次不可合一的根约束');
  assert.equal(root.kind, 'constraint');
  assert.match(root.label, /须与结果单位一致/);
  // 每个事实都能沿依赖边到达根（反向闭包性质：无悬挂事实）
  const byId = new Map(facts.map((f) => [f.id, f]));
  const reachesRoot = (id, seen = new Set()) => {
    if (id === rootFactId) return true;
    if (seen.has(id)) return false;
    seen.add(id);
    const f = byId.get(id);
    return facts.some((g) => g.deps.includes(id) && reachesRoot(g.id, seen));
  };
  for (const f of facts) assert.ok(reachesRoot(f.id), `事实 #${f.id} 应有路径到达冲突根`);
});

test('冲突切片最小性：无关声明与无关宏不进入切片', () => {
  const src = `sensor z : m/s;
let g = fun y -> y * y;
sensor len : m;
sensor tim : s;
let id = fun x -> x;
id len + id tim
`;
  const r = runInference(src);
  assert.equal(r.ok, false);
  const frags = r.error.slice.fragments.map((f) => src.slice(f.start, f.end));
  assert.ok(!frags.some((s) => s.includes('sensor z')), '无关传感器声明不得进入切片');
  assert.ok(!frags.some((s) => s.includes('let g')), '无关宏定义不得进入切片');
  assert.ok(frags.includes('sensor len : m') && frags.includes('sensor tim : s'));
});

test('自应用：切片稳定返回函数体、参数绑定及调用位置', () => {
  const src = 'let f = fun x -> x x;\nf\n';
  const r1 = runInference(src);
  const r2 = runInference(src);
  assert.equal(r1.ok, false);
  assert.ok(r1.error.slice, '自应用失败应携带切片');
  const frags = r1.error.slice.fragments.map((f) => src.slice(f.start, f.end));
  assert.ok(frags.includes('fun x -> x x'), '切片应包含形成循环的函数体');
  assert.ok(frags.includes('x'), '切片应包含参数绑定');
  assert.ok(frags.includes('x x'), '切片应包含调用位置');
  const roles = new Set(r1.error.slice.facts.map((f) => f.role));
  assert.ok([...roles].some((s) => /参数绑定/.test(s)));
  assert.ok([...roles].some((s) => /函数体/.test(s)));
  assert.deepEqual(r1.error, r2.error, '自应用切片应稳定一致');
});

test('切片步骤携带依赖边，可复核跨宏传播链', () => {
  const r = runInference(INDIRECT_SCRIPT);
  const { facts } = r.error.slice;
  const inst = facts.filter((f) => f.kind === 'instantiate');
  assert.equal(inst.length, 2, '两次宏引用各有一条实例化事实');
  const gen = facts.find((f) => f.kind === 'generalize');
  for (const i of inst) assert.ok(i.deps.includes(gen.id), '实例化边应指向 let 泛化点');
  // 传感器声明是切片叶子（无依赖的来源）
  const sensors = facts.filter((f) => f.kind === 'sensor');
  assert.equal(sensors.length, 2);
  for (const s of sensors) assert.deepEqual(s.deps, []);
});

test('直接异单位相加：切片同样覆盖两个声明与相加位置', () => {
  const src = 'sensor a : m;\nsensor b : s;\na + b\n';
  const r = runInference(src);
  assert.equal(r.ok, false);
  const frags = r.error.slice.fragments.map((f) => src.slice(f.start, f.end));
  for (const need of ['sensor a : m', 'sensor b : s', 'a + b']) {
    assert.ok(frags.includes(need), `切片必须包含「${need}」`);
  }
});
