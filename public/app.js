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
  indirect: `// 长度与时间经恒等宏间接传递后相加：切片须含两份声明、两次调用与相加位置
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

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  }[c]));
}

/** 清除旧结论：提交新推断、编辑脚本或切换示例时调用。 */
function clearPanels() {
  lastResult = null;
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

function showError(err) {
  // 出错时不保留任何旧结论：结果区已清空，仅展示错误与冲突依据切片
  errorEl.classList.remove('hidden');
  const source = sourceEl.value;
  let html = `<h2>推断失败</h2><p class="err-msg">${escapeHtml(err.message)}</p>`;
  html += '<p class="dim">存在错误：此前的推断结论已清除，不会保留。</p>';
  if (err.slice && err.slice.fragments && err.slice.fragments.length) {
    html += renderSlice(err.slice, source);
  } else if (err.spans && err.spans.length) {
    html += `<div class="src-view"><pre>${markedSource(source, err.spans)}</pre></div>`;
    html += '<ul class="legend">' + err.spans.map((s, i) =>
      `<li><span class="chip mk${i % 6}">${i + 1}</span> 第 ${s.startLine} 行第 ${s.startCol} 列` +
      `${s.label ? `：${escapeHtml(s.label)}` : ''}</li>`).join('') + '</ul>';
  }
  errorEl.innerHTML = html;
  if (err.slice && err.slice.fragments && err.slice.fragments.length) {
    bindSliceInteractions(errorEl, err.slice);
  }
}

/* ---------------- 冲突依据切片审计视图 ---------------- */

const ROLE_LABEL = {
  '传感器声明': '传感器声明',
  'let 绑定': '宏定义（let 泛化）',
  '函数体': '函数体',
  '参数绑定': '参数绑定',
  '宏引用': '宏引用（实例化）',
  '宏调用': '宏调用',
  '冲突运算': '冲突运算',
  '相加位置': '相加位置',
  '单位组合位置': '组合位置',
  '数值': '数值',
  '取负': '取负',
};

function roleClass(role) {
  return 'role-' + ({
    '传感器声明': 'sensor',
    'let 绑定': 'let',
    '函数体': 'fun',
    '参数绑定': 'bind',
    '宏引用': 'ref',
    '宏调用': 'call',
    '冲突运算': 'expr',
    '相加位置': 'op',
    '单位组合位置': 'op',
    '数值': 'literal',
    '取负': 'neg',
  }[role] || 'other');
}

function renderSlice(slice, source) {
  let html = '<div class="slice-audit">';
  html += `<h3>冲突依据切片审计</h3>`;
  html += `<p class="slice-head"><strong>${escapeHtml(slice.headline)}</strong></p>`;
  html += `<p class="slice-conflict">${escapeHtml(slice.conflict)}</p>`;
  html += '<p class="dim">下列片段为从首次不可合一处反向归并出的最小冲突依据（删除任一项约束链即断裂），' +
    '已全部高亮；点击任一片段可查看其跨宏调用传播链。</p>';

  // 源码视图：嵌套片段按最内层可点选
  html += `<div class="src-view slice-src"><pre>${renderSliceSource(source, slice.fragments)}</pre></div>`;

  // 片段清单（与源码高亮双向联动）
  html += '<div class="frag-list">';
  slice.fragments.forEach((f, i) => {
    html += `<button type="button" class="frag-chip ${roleClass(f.role)}" data-frag="${i}">` +
      `<span class="frag-role">${escapeHtml(ROLE_LABEL[f.role] || f.role)}</span>` +
      `<code>${escapeHtml(f.text)}</code>` +
      `<span class="dim">${f.startLine}:${f.startCol}</span></button>`;
  });
  html += '</div>';

  // 左：按推导顺序的约束步骤；右：选中片段的传播链
  html += '<div class="slice-cols">';
  html += '<div class="slice-steps"><h4>推导顺序：各来源如何约束到冲突</h4><ol>';
  slice.steps.forEach((s, i) => {
    html += `<li class="step-item${s.isGoal ? ' goal' : ''}" data-step="${i}">` +
      `<span class="step-title">${escapeHtml(s.title)}${s.isGoal ? '（冲突点）' : ''}</span>` +
      `<span class="step-detail">${escapeHtml(s.detail)}</span></li>`;
  });
  html += '</ol></div>';
  html += '<div class="slice-chain" id="slice-chain"><h4>传播链</h4>' +
    '<p class="dim">点选上方任一高亮片段，查看它经哪些实例化与调用传播到冲突。</p></div>';
  html += '</div></div>';
  return html;
}

/** 按片段区间切分源码并叠加可点选高亮（嵌套时取最短/最内层片段为主）。 */
function renderSliceSource(source, fragments) {
  const bounds = new Set([0, source.length]);
  for (const f of fragments) {
    bounds.add(Math.max(0, Math.min(f.start, source.length)));
    bounds.add(Math.max(0, Math.min(f.end, source.length)));
  }
  const pts = [...bounds].sort((a, b) => a - b);
  let html = '';
  for (let i = 0; i < pts.length - 1; i++) {
    const a = pts[i];
    const b = pts[i + 1];
    const text = escapeHtml(source.slice(a, b));
    // 覆盖此段的片段：取区间最短者（最内层）作为点击目标
    let best = -1;
    const covering = [];
    fragments.forEach((f, idx) => {
      if (f.start <= a && b <= f.end) {
        covering.push(idx);
        if (best === -1 || (f.end - f.start) < (fragments[best].end - fragments[best].start)) best = idx;
      }
    });
    if (!covering.length || best === -1) {
      html += text;
    } else {
      const f = fragments[best];
      html += `<mark class="slice-mark ${roleClass(f.role)}" data-frag="${best}" title="${escapeHtml(ROLE_LABEL[f.role] || f.role)}">${text}</mark>`;
    }
  }
  return html;
}

function bindSliceInteractions(root, slice) {
  const chainEl = root.querySelector('#slice-chain');

  function selectFrag(idx) {
    const f = slice.fragments[idx];
    if (!f) return;
    root.querySelectorAll('.frag-chip').forEach((el) => el.classList.toggle('selected', Number(el.dataset.frag) === idx));
    root.querySelectorAll('mark.slice-mark').forEach((el) => el.classList.toggle('selected', Number(el.dataset.frag) === idx));

    let html = `<h4>传播链：<code>${escapeHtml(f.text)}</code> <span class="dim">[${escapeHtml(roleLabel(f.role))}]</span></h4>`;
    if (!f.chain || !f.chain.length) {
      html += '<p class="dim">（该片段无进一步传播步骤）</p>';
    } else {
      html += '<ol class="chain-list">';
      f.chain.forEach((c) => {
        html += `<li class="chain-step${c.isGoal ? ' goal' : ''}">` +
          `<span class="step-title">${escapeHtml(c.title)}${c.isGoal ? ' ⬅ 冲突在此显现' : ''}</span>` +
          `<span class="step-detail">${escapeHtml(c.detail)}</span></li>`;
      });
      html += '</ol>';
    }
    chainEl.innerHTML = html;
    chainEl.scrollIntoView({ block: 'nearest' });
  }

  root.querySelectorAll('mark.slice-mark').forEach((el) => {
    el.addEventListener('click', () => selectFrag(Number(el.dataset.frag)));
  });
  root.querySelectorAll('.frag-chip').forEach((el) => {
    el.addEventListener('click', () => selectFrag(Number(el.dataset.frag)));
  });
  // 点击推导步骤：联动到其锚定片段（nodeId 相同的主片段）
  root.querySelectorAll('.step-item').forEach((el) => {
    el.addEventListener('click', () => {
      const s = slice.steps[Number(el.dataset.step)];
      const idx = slice.fragments.findIndex((f) => f.nodeId === s.nodeId && f.role !== '相加位置' && f.role !== '参数绑定');
      if (idx >= 0) selectFrag(idx);
    });
  });

  if (slice.fragments.length) selectFrag(0);
}

function roleLabel(role) {
  return ROLE_LABEL[role] || role;
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

exampleSel.addEventListener('change', () => {
  sourceEl.value = EXAMPLES[exampleSel.value] || '';
  clearPanels();
});
sourceEl.addEventListener('input', clearPanels);
runBtn.addEventListener('click', runInfer);

sourceEl.value = EXAMPLES.identity;
