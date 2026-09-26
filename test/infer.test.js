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

/* ---------------- 冲突依据切片审计 ---------------- */

const INDIRECT_SCRIPT = `// 长度与时间经恒等宏间接传递后相加
sensor len : m;
sensor tim : s;
let id = fun x -> x;
id len + id tim
`;

test('切片：长度与时间经恒等宏间接相加，含两份声明、相应调用与相加位置', () => {
  const r = runInference(INDIRECT_SCRIPT);
  assert.equal(r.ok, false);
  assert.match(r.error.message, /单位不匹配/);
  const slice = r.error.slice;
  assert.ok(slice, '失败结果应携带冲突依据切片');
  const texts = slice.fragments.map((f) => f.text);
  assert.ok(texts.includes('sensor len : m'), '切片须含长度传感器声明');
  assert.ok(texts.includes('sensor tim : s'), '切片须含时间传感器声明');
  assert.ok(texts.includes('id len'), '切片须含长度侧宏调用');
  assert.ok(texts.includes('id tim'), '切片须含时间侧宏调用');
  assert.ok(texts.includes('+'), '切片须含相加位置');
  assert.ok(texts.includes('let id = fun x -> x'), '切片须含宏定义（let 泛化）');
  // 两个操作数各自的调用都在，而不是只剩最后一个操作符
  const roles = slice.fragments.map((f) => f.role);
  assert.equal(roles.filter((x) => x === '宏调用').length, 2);
  assert.ok(roles.includes('相加位置'));
});

test('切片：按推导顺序呈现 let 泛化与每次实例化', () => {
  const r = runInference(INDIRECT_SCRIPT);
  const kinds = r.error.slice.steps.map((s) => s.kind);
  // 泛化恰有一次，两次引用各自实例化（新鲜变量、互不影响）
  assert.equal(kinds.filter((k) => k === 'generalize').length, 1);
  assert.equal(kinds.filter((k) => k === 'instantiate').length, 2);
  // 步骤严格按推导顺序（factId 升序）
  const ids = r.error.slice.steps.map((s) => s.factId);
  assert.deepEqual(ids, [...ids].sort((a, b) => a - b));
  // 每个实例化步骤都有其前提（泛化事实），来源可追溯
  for (const s of r.error.slice.steps.filter((x) => x.kind === 'instantiate')) {
    const gen = r.error.slice.steps.find((g) => g.kind === 'generalize');
    assert.ok(s.deps.includes(gen.factId), '实例化须依赖 let 泛化事实');
  }
});

test('切片：点选片段的传播链跨宏调用到达冲突，且不串入另一侧', () => {
  const r = runInference(INDIRECT_SCRIPT);
  const slice = r.error.slice;
  const byText = (t) => slice.fragments.find((f) => f.text === t);
  const lenChain = byText('sensor len : m').chain;
  const timChain = byText('sensor tim : s').chain;
  // 两条链都抵达同一冲突点（相加约束）
  assert.ok(lenChain.some((c) => c.isGoal), '长度声明链应到达冲突点');
  assert.ok(timChain.some((c) => c.isGoal), '时间声明链应到达冲突点');
  // 链中含跨宏环节：实例化 与 调用
  const kinds = (c) => c.map((x) => x.kind);
  assert.ok(kinds(lenChain).includes('instantiate'), '长度链经过实例化');
  assert.ok(kinds(lenChain).includes('app'), '长度链经过宏调用');
  assert.ok(kinds(timChain).includes('instantiate'), '时间链经过实例化');
  // 严格按推导顺序
  const sorted = (c) => [...c.map((x) => x.factId)].sort((a, b) => a - b);
  assert.deepEqual(lenChain.map((x) => x.factId), sorted(lenChain));
  // 长度侧链不含时间侧独有的调用（按 detail 中 num<s> 判定）；冲突点描述同时含两侧，故排除
  const nonGoal = (c) => c.filter((x) => !x.isGoal);
  assert.ok(!nonGoal(lenChain).some((c) => /num<s>/.test(c.detail)), '长度侧链不应串入时间侧调用');
  assert.ok(!nonGoal(timChain).some((c) => /num<m>/.test(c.detail) && /须与/.test(c.detail)), '时间侧链不应串入长度侧调用');
  // 相加位置是两条链的汇合点：其链覆盖两侧
  const plusChain = byText('+').chain;
  assert.ok(plusChain.some((c) => /num<m>/.test(c.detail)) && plusChain.some((c) => /num<s>/.test(c.detail)));
});

test('切片最小性：无关声明不入片（不按文本邻近、不试探脚本）', () => {
  const src = 'sensor a : m;\nsensor b : s;\nsensor noise : m;\nlet unused = fun z -> z;\na + b\n';
  const r = runInference(src);
  assert.equal(r.ok, false);
  const texts = r.error.slice.fragments.map((f) => f.text);
  assert.ok(!texts.some((t) => t.includes('noise')), '无关传感器声明不应进入冲突切片');
  assert.ok(!texts.some((t) => t.includes('unused')), '无关宏定义不应进入冲突切片');
  assert.ok(texts.includes('sensor a : m'));
  assert.ok(texts.includes('sensor b : s'));
});

test('切片：单态 let 别名多跳传播仍可回溯到两份声明', () => {
  const src = 'sensor a : m;\nsensor b : s;\nlet p = a;\nlet q = b;\np + q\n';
  const r = runInference(src);
  assert.equal(r.ok, false);
  const texts = r.error.slice.fragments.map((f) => f.text);
  assert.ok(texts.includes('sensor a : m') && texts.includes('sensor b : s'));
  assert.ok(texts.includes('let p = a') && texts.includes('let q = b'));
  assert.ok(texts.includes('+'));
});

test('切片：自应用稳定返回函数体、参数绑定与调用位置', () => {
  const src = 'let f = fun x -> x x;\nf\n';
  const r1 = runInference(src);
  const r2 = runInference(src);
  assert.equal(r1.ok, false);
  const slice = r1.error.slice;
  assert.ok(slice, '自应用应携带切片');
  const frags = slice.fragments;
  assert.ok(frags.some((f) => f.text === 'fun x -> x x' && f.role === '函数体'), '须含形成循环的函数体');
  assert.ok(frags.some((f) => f.role === '参数绑定' && f.text === 'x'), '须含参数绑定 x');
  assert.ok(frags.some((f) => f.text === 'x x' && f.role === '宏调用'), '须含自应用调用位置');
  // 冲突点为该调用约束，参数绑定链可一步到达
  const bindFrag = frags.find((f) => f.role === '参数绑定');
  assert.ok(bindFrag.chain.some((c) => c.isGoal));
  // 稳定一致
  assert.deepEqual(r1.error, r2.error);
});

test('切片：全部片段带源码区间，可供页面高亮', () => {
  const r = runInference(INDIRECT_SCRIPT);
  for (const f of r.error.slice.fragments) {
    assert.ok(Number.isInteger(f.start) && Number.isInteger(f.end) && f.end > f.start);
    assert.equal(INDIRECT_SCRIPT.slice(f.start, f.end).replace(/\s+/g, ' ').trim(), f.text);
    assert.ok(Array.isArray(f.chain) && f.chain.length > 0);
  }
  assert.match(r.error.slice.conflict, /首次不可合一/);
});
