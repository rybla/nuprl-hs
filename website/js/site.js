(function () {
  const tip = document.getElementById('tip');
  if (!tip) return;

  function row(k, v) {
    if (!v) return '';
    const d = document.createElement('div');
    d.className = 'tip-row';
    d.innerHTML = '<span class="k"></span><span class="v"></span>';
    d.querySelector('.k').textContent = k;
    d.querySelector('.v').textContent = v;
    return d.outerHTML;
  }

  function fill(el) {
    const kind = el.getAttribute('data-kind');
    const note = el.getAttribute('data-note');
    if (!kind && !note) return false;
    tip.innerHTML =
      (kind ? '<div class="tip-kind"></div>' : '') +
      (note ? '<div class="tip-note"></div>' : '') +
      row('uniform', el.getAttribute('data-uniform')) +
      row('unfolds', el.getAttribute('data-unfold')) +
      row('whnf', el.getAttribute('data-whnf')) +
      row('normal', el.getAttribute('data-nf'));
    const k = tip.querySelector('.tip-kind');
    if (k) k.textContent = kind;
    const n = tip.querySelector('.tip-note');
    if (n) n.textContent = note;
    return true;
  }

  function place(ev) {
    const pad = 14;
    let x = ev.clientX + pad;
    let y = ev.clientY + pad;
    tip.hidden = false;
    const r = tip.getBoundingClientRect();
    if (x + r.width > window.innerWidth - 8) x = ev.clientX - r.width - pad;
    if (y + r.height > window.innerHeight - 8) y = ev.clientY - r.height - pad;
    if (x < 8) x = 8;
    if (y < 8) y = 8;
    tip.style.left = x + 'px';
    tip.style.top = y + 'px';
  }

  let pinned = null;
  function show(ev) {
    const el = ev.target.closest('[data-kind]');
    if (!el || pinned) return;
    if (!fill(el)) return;
    place(ev);
  }
  function hide() { if (!pinned) tip.hidden = true; }

  document.addEventListener('mousemove', function (ev) {
    if (pinned) return;
    const el = ev.target.closest('[data-kind]');
    if (!el) { hide(); return; }
    if (!fill(el)) return;
    place(ev);
  });
  document.addEventListener('click', function (ev) {
    const el = ev.target.closest('[data-kind]');
    if (!el) { pinned = null; hide(); return; }
    if (pinned === el) { pinned = null; hide(); return; }
    pinned = el;
    fill(el);
    place(ev);
  });
  document.addEventListener('keydown', function (ev) {
    if (ev.key === 'Escape') { pinned = null; hide(); }
  });

  function all(sel, fn) { document.querySelectorAll(sel).forEach(fn); }
  const expandProofs = document.getElementById('expand-proofs');
  const collapseProofs = document.getElementById('collapse-proofs');
  if (expandProofs) expandProofs.addEventListener('click', function () {
    all('details.pnode', function (d) { d.open = true; });
    all('details.panel.proof-panel', function (d) { d.open = true; });
  });
  if (collapseProofs) collapseProofs.addEventListener('click', function () {
    all('details.pnode', function (d) { d.open = false; });
    const roots = document.querySelectorAll('details.panel.proof-panel > .proof-tree > details.pnode');
    roots.forEach(function (d) { d.open = true; });
  });
  const expandAll = document.getElementById('expand-all');
  if (expandAll) expandAll.addEventListener('click', function () {
    all('details.panel', function (d) { d.open = true; });
  });
  const q = document.getElementById('filter');
  if (q) q.addEventListener('input', function () {
    const s = q.value.toLowerCase().trim();
    all('.card[data-name]', function (c) {
      const n = (c.getAttribute('data-name') || '').toLowerCase();
      c.classList.toggle('hidden', s.length > 0 && n.indexOf(s) < 0);
    });
  });
})();
