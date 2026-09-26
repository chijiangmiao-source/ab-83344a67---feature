'use strict';

const EXAMPLES = {
  identity: `// 校准宏：恒等宏跨量纲复用
sensor len : m;
sensor tim : s;
let id = fun x -> x;
let a = id len;
let b = id tim;
id len * id tim
`,
  conflict: `// 异单位相加：应定位两个操作数
sensor a : m;
sensor b : s;
a + b
`,
  indirect: `// 恒等宏间接传递：长度与时间经宏实例化后相加
sensor len : m;
sensor tim : s;
let id = fun x -> x;
id len + id tim
`,
  omega: `// 自应用：occurs check 触发无限类型错误
let f = fun x -> x x;
f
`,
  units: `sensor d : m;
sensor t : s;
let v = d / t;
let sq = fun x -> x * x;
sq d * v
`,
};

const sourceEl = document.getElementById('source');
const runBtn = document.getElementById('run');
const exampleSel = document.getElementById('example');
const resultsEl = document.getElementById('results');
const errorEl = document.getElementById('error-panel');
const rowsEl = document.getElementById('expr-rows');
const evidenceEl = document.getElementById('evidence');
const outputEl = document.getElementById('output-type');
const genEl = document.getElementById('gen-vars');

let lastResult = null;
let lastError = null;

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  }[c]));
}

/** 清除旧结论：提交新推断、编辑脚本或切换示例时调用。 */
function clearPanels() {
  lastResult = null;
  lastError = null;
  resultsEl.classList.add('hidden');
  errorEl.classList.add('hidden');
  errorEl.innerHTML = '';
  rowsEl.innerHTML = '';
  evidenceEl.innerHTML = '';
  evidenceEl.classList.add('hidden');
}

async function runInfer() {
  clearPanels();
  let res;
  try {
    const r = await fetch('/api/infer', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ source: sourceEl.value }),
    });
    res = await r.json();
  } catch (e) {
    showError({ message: `请求失败：${e.message}`, spans: [] });
    return;
  }
  if (res.ok) showResults(res);
  else showError(res.error);
}

function showResults(res) {
  lastResult = res;
  resultsEl.classList.remove('hidden');
  outputEl.textContent = res.output;

  genEl.innerHTML = '';
  if (!res.generalizable.length) {
    genEl.innerHTML = '<p class="dim">（无 let 绑定，无可泛化类型变量）</p>';
  } else {
    for (const g of res.generalizable) {
      const div = document.createElement('div');
      div.className = 'gen-item';
      const q = g.quantified.length ? g.quantified.join('、') : '（单态，无可泛化变量）';
      div.innerHTML =
        `<code>${escapeHtml(g.name)} : ${escapeHtml(g.scheme)}</code>` +
        `<span class="dim">可泛化变量：${escapeHtml(q)}</span>`;
      genEl.appendChild(div);
    }
  }

  rowsEl.innerHTML = '';
  for (const e of res.expressions) {
    const tr = document.createElement('tr');
    tr.dataset.id = e.id;
    tr.innerHTML =
      `<td class="pos">${e.line}:${e.col}</td>` +
      `<td><code>${escapeHtml(e.snippet)}</code></td>` +
      `<td>${escapeHtml(e.kind)}</td>` +
      `<td><code class="ty">${escapeHtml(e.type)}</code></td>`;
    tr.addEventListener('click', () => selectExpr(e.id));
    rowsEl.appendChild(tr);
  }
}

function selectExpr(id) {
  for (const tr of rowsEl.children) tr.classList.toggle('selected', Number(tr.dataset.id) === id);
  const e = lastResult.expressions.find((x) => x.id === id);
  if (!e) return;
  evidenceEl.classList.remove('hidden');
  const steps = e.events.length
    ? `<ol>${e.events.map((s) => `<li>${escapeHtml(s)}</li>`).join('')}</ol>`
    : '<p class="dim">（该表达式无额外约束步骤）</p>';
  evidenceEl.innerHTML =
    `<h3>约束归并依据：<code>${escapeHtml(e.snippet)}</code> ⇒ <code class="ty">${escapeHtml(e.type)}</code></h3>${steps}`;
}

/* ---------------- 失败：冲突依据切片 ---------------- */

const FACT_KIND_TAG = {
  sensor: '传感器声明',
  literal: '字面量单位',
  generalize: 'let 泛化',
  instantiate: '宏实例化',
  ref: '引用',
  combine: '单位组合',
  constraint: '合一约束',
  bind: '类型合一',
  ubind: '单位合一',
  tvar: '类型变量',
  uvar: '单位变量',
  fun: '函数体',
};

function showError(err) {
  // 出错时不保留任何旧结论：结果区已清空，仅展示错误与冲突源码定位
  lastError = err;
  errorEl.classList.remove('hidden');
  const source = sourceEl.value;
  let html = `<h2>推断失败</h2><p class="err-msg">${escapeHtml(err.message)}</p>`;
  html += '<p class="dim">存在错误：此前的推断结论已清除，不会保留。</p>';
  if (err.spans && err.spans.length) {
    html += '<h3>冲突源码定位</h3>';
    html += `<div class="src-view"><pre>${markedSource(source, err.spans)}</pre></div>`;
    html += '<ul class="legend">' + err.spans.map((s, i) =>
      `<li><span class="chip mk${i % 6}">${i + 1}</span> 第 ${s.startLine} 行第 ${s.startCol} 列` +
      `${s.label ? `：${escapeHtml(s.label)}` : ''}</li>`).join('') + '</ul>';
  }
  if (err.slice) html += renderSlice(err.slice);
  errorEl.innerHTML = html;
  bindSliceEvents(err.slice);
}

function renderSlice(slice) {
  const source = sourceEl.value;
  let html = '<div class="slice-box">';
  html += '<h3>冲突依据切片（最小依据：删去任一项都不再构成此矛盾）</h3>';
  html += '<p class="dim">高亮片段为共同导致冲突的全部声明、宏定义与调用；按推导顺序展示它们如何一步步约束到首次不可合一。点选任一片段或步骤可查看其跨宏调用传播链。</p>';
  html += `<div class="src-view slice-view"><pre>${markedSliceSource(source, slice)}</pre></div>`;
  html += '<div class="slice-cols"><div>';
  html += '<h4>推导顺序（从来源到首次不可合一）</h4>';
  html += `<ol class="slice-steps">${slice.facts.map((f) => renderStep(f, slice)).join('')}</ol>`;
  html += '</div><div id="chain-panel" class="chain-panel hidden"></div></div>';
  html += '</div>';
  return html;
}

function renderStep(f, slice) {
  const isRoot = f.id === slice.rootFactId;
  const tag = FACT_KIND_TAG[f.kind] || f.kind;
  return `<li data-fid="${f.id}" class="step-${escapeHtml(f.kind)}${isRoot ? ' step-root' : ''}">` +
    `<span class="step-tag">${escapeHtml(tag)}</span>` +
    `<span class="step-pos">第 ${f.line} 行</span>` +
    `<span class="step-label">${escapeHtml(f.label)}</span>` +
    (isRoot ? '<span class="root-badge">首次不可合一</span>' : '') +
    '</li>';
}

/** 切片源码高亮：每个区间可点选，data-fids 关联该区间的全部事实。 */
function markedSliceSource(source, slice) {
  const frags = slice.fragments;
  const bounds = new Set([0, source.length]);
  for (const s of frags) {
    bounds.add(Math.max(0, Math.min(s.start, source.length)));
    bounds.add(Math.max(0, Math.min(s.end, source.length)));
  }
  const pts = [...bounds].sort((a, b) => a - b);
  let html = '';
  for (let i = 0; i < pts.length - 1; i++) {
    const a = pts[i];
    const b = pts[i + 1];
    const text = escapeHtml(source.slice(a, b));
    const cover = frags.find((s) => s.start <= a && b <= s.end);
    if (!cover) { html += text; continue; }
    html += `<mark class="slice-mark" data-start="${cover.start}" data-end="${cover.end}"` +
      ` title="${escapeHtml(cover.label)}">${text}</mark>`;
  }
  return html;
}

/** 按区间拆分源码并叠加高亮（支持嵌套区间）。 */
function markedSource(source, spans) {
  const bounds = new Set([0, source.length]);
  for (const s of spans) {
    bounds.add(Math.max(0, Math.min(s.start, source.length)));
    bounds.add(Math.max(0, Math.min(s.end, source.length)));
  }
  const pts = [...bounds].sort((a, b) => a - b);
  let html = '';
  for (let i = 0; i < pts.length - 1; i++) {
    const a = pts[i];
    const b = pts[i + 1];
    const text = escapeHtml(source.slice(a, b));
    const covering = [];
    spans.forEach((s, idx) => {
      if (s.start <= a && b <= s.end) covering.push(idx);
    });
    if (!covering.length) html += text;
    else html += `<mark class="${covering.map((i2) => `mk${i2 % 6}`).join(' ')}">${text}</mark>`;
  }
  return html;
}

/** 沿依赖边反向（数据传播方向：来源 → 合一 → 冲突）求起点到冲突点的传播链。 */
function computeChain(slice, originIds) {
  const byId = new Map(slice.facts.map((f) => [f.id, f]));
  const rev = new Map(); // 被依赖事实 -> 依赖它的事实
  for (const f of slice.facts) {
    for (const d of f.deps) {
      if (!byId.has(d)) continue;
      if (!rev.has(d)) rev.set(d, []);
      rev.get(d).push(f.id);
    }
  }
  const chain = new Set(originIds);
  const macro = new Set(); // 调用点处汇入的宏实例化/泛化支路
  const wl = [...originIds];
  const addMacroUpstream = (fact) => {
    // 沿该约束的上游找到宏实例化与 let 泛化点（跨宏调用的另一侧支路）
    const stack = [...fact.deps];
    const seen = new Set();
    while (stack.length) {
      const id = stack.pop();
      if (seen.has(id)) continue;
      seen.add(id);
      const f = byId.get(id);
      if (!f) continue;
      if (f.kind === 'instantiate' || f.kind === 'generalize') macro.add(id);
      for (const d of f.deps) stack.push(d);
    }
  };
  while (wl.length) {
    const id = wl.pop();
    const f = byId.get(id);
    if (f && f.kind === 'constraint') addMacroUpstream(f);
    for (const nxt of rev.get(id) || []) {
      if (!chain.has(nxt)) { chain.add(nxt); wl.push(nxt); }
    }
  }
  return { chain, macro };
}

function bindSliceEvents(slice) {
  if (!slice) return;
  const view = errorEl.querySelector('.slice-view');
  if (view) {
    view.querySelectorAll('.slice-mark').forEach((m) => {
      m.addEventListener('click', () => {
        const frag = slice.fragments.find(
          (s) => s.start === Number(m.dataset.start) && s.end === Number(m.dataset.end),
        );
        if (frag) selectOrigins(slice, frag.factIds, frag);
      });
    });
  }
  errorEl.querySelectorAll('.slice-steps li').forEach((li) => {
    li.addEventListener('click', () => {
      const fid = Number(li.dataset.fid);
      const f = slice.facts.find((x) => x.id === fid);
      selectOrigins(slice, [fid], f ? { start: f.start, end: f.end, label: f.role } : null);
    });
  });
}

function selectOrigins(slice, originIds, frag) {
  const { chain, macro } = computeChain(slice, originIds);
  // 高亮：源码区 + 步骤列表
  errorEl.querySelectorAll('.slice-mark').forEach((m) => {
    const f2 = slice.fragments.find(
      (s) => s.start === Number(m.dataset.start) && s.end === Number(m.dataset.end),
    );
    const onChain = f2 && f2.factIds.some((id) => chain.has(id) || macro.has(id));
    const isOrigin = f2 && f2.factIds.some((id) => originIds.includes(id));
    m.classList.toggle('on-chain', !!onChain);
    m.classList.toggle('origin', !!isOrigin);
  });
  errorEl.querySelectorAll('.slice-steps li').forEach((li) => {
    const fid = Number(li.dataset.fid);
    li.classList.toggle('on-chain', chain.has(fid) || macro.has(fid));
    li.classList.toggle('origin', originIds.includes(fid));
  });
  renderChainPanel(slice, originIds, chain, macro, frag);
}

function renderChainPanel(slice, originIds, chain, macro, frag) {
  const panel = errorEl.querySelector('#chain-panel');
  if (!panel) return;
  panel.classList.remove('hidden');
  const byId = new Map(slice.facts.map((f) => [f.id, f]));
  const ordered = [...chain].map((id) => byId.get(id)).filter(Boolean).sort((a, b) => a.id - b.id);
  const macroFacts = [...macro]
    .filter((id) => !chain.has(id))
    .map((id) => byId.get(id))
    .filter(Boolean)
    .sort((a, b) => a.id - b.id);
  const originSnippet = frag
    ? sourceEl.value.slice(frag.start, frag.end).replace(/\s+/g, ' ').trim()
    : '';
  let html = '<h4>跨宏调用传播链</h4>';
  if (originSnippet) html += `<p class="dim">起点：<code>${escapeHtml(originSnippet)}</code></p>`;
  html += '<ol class="chain-list">';
  const renderItem = (f, isMacroHop) => {
    const isOrigin = originIds.includes(f.id);
    const isRoot = f.id === slice.rootFactId;
    const badges = [];
    if (isOrigin) badges.push('<span class="origin-badge">所选片段</span>');
    if (f.kind === 'instantiate') badges.push('<span class="inst-badge">跨宏调用</span>');
    if (f.kind === 'generalize') badges.push('<span class="gen-badge">宏定义泛化</span>');
    if (isMacroHop) badges.push('<span class="inst-badge">宏支路汇入</span>');
    if (isRoot) badges.push('<span class="root-badge">冲突点</span>');
    return `<li class="${isRoot ? 'chain-root' : ''}">${badges.join(' ')}` +
      `<code>${escapeHtml(f.snippet)}</code><span class="step-label">${escapeHtml(f.label)}</span></li>`;
  };
  // 按推导顺序交错展示：宏支路事实排在其汇入的约束之前
  const merged = [...ordered, ...macroFacts].sort((a, b) => a.id - b.id);
  for (const f of merged) html += renderItem(f, macro.has(f.id) && !chain.has(f.id));
  html += '</ol>';
  const macroHops = merged.filter((f) => f.kind === 'instantiate').length;
  if (macroHops > 0) {
    html += `<p class="dim">该传播链经过 ${macroHops} 次宏实例化（每次引用独立刷新类型/单位变量，来源沿实例化边追溯到 let 泛化点）。</p>`;
  }
  panel.innerHTML = html;
}

exampleSel.addEventListener('change', () => {
  sourceEl.value = EXAMPLES[exampleSel.value] || '';
  clearPanels();
});
sourceEl.addEventListener('input', clearPanels);
runBtn.addEventListener('click', runInfer);

sourceEl.value = EXAMPLES.identity;
