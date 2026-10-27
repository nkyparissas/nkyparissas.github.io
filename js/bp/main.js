/* ==========================================================================
   /bp: page controller. Builds the predictor menu and knobs from the
   registry, compiles the source, drives the core cycle by cycle and redraws
   the figures, the log and the statistics.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { compile } = BP.compiler;
	const { Core } = BP.core;
	const { PREDICTORS, findPredictor, defaultKnobs, knobSummary } = BP.registry;
	const { STRESS_NAMES, fmtBytes, hex, brName } = BP.base;
	const { drawFrontEnd } = BP.frontendFigure;
	const { EXAMPLES } = BP.examples;

	const $ = function (id) { return document.getElementById(id); };
	const STATE_KEY = 'bp:state:v1';
	const THEME_KEY = 'bp:theme';
	const LOG_MAX = 400;
	const ANIM_MAX = 16;   // speeds up to this many cycles/s animate every cycle and keep the log

	const SPEEDS = [
		{ v: 1, l: '1 cycle/s' }, { v: 2, l: '2 cycles/s' }, { v: 4, l: '4 cycles/s' }, { v: 8, l: '8 cycles/s' },
		{ v: 16, l: '16 cycles/s' }, { v: 100, l: '100 cycles/s' }, { v: 1000, l: '1k cycles/s' },
		{ v: 10000, l: '10k cycles/s' }, { v: 100000, l: '100k cycles/s' }, { v: Infinity, l: 'max' }
	];

	const FE_KNOBS = [
		{ id: 'depth', label: 'pipeline depth', type: 'int', min: 5, max: 20, def: 7,
			help: 'Stages from Fetch to Execute (inclusive). A mispredict costs depth − 1 cycles.' },
		{ id: 'btb', label: 'BTB', type: 'choice', def: 256,
			options: [{ v: 0, label: 'ideal' }, { v: 16, label: '16 entries' }, { v: 64, label: '64 entries' }, { v: 256, label: '256 entries' }, { v: 1024, label: '1024 entries' }],
			help: 'Branch target buffer (4-way). A miss on a predicted-taken branch is fixed by Decode, 2 cycles later.' },
		{ id: 'history', label: 'history update', type: 'choice', def: 'spec',
			options: [{ v: 'spec', label: 'speculative, repaired' }, { v: 'resolve', label: 'at resolve' }],
			help: 'Speculative: histories take the predicted outcome at fetch and are repaired on a flush. At resolve: ' +
				'histories only see resolved branches, so in-flight ones are missing (Section II-B).' }
	];

	const state = {
		src: EXAMPLES[0].src,
		example: 0,
		bpId: 'PAg',
		knobs: {},
		fe: {},
		speed: 3,
		runs: [],
		zoom: {}
	};

	let program = null, compiledSrc = null, core = null, def = null;
	let playing = false, runToEnd = false, rafId = 0, lastT = 0, acc = 0, recorded = false;
	let asmRows = [], marked = [];
	let zooms = null;

	/* ------------------------------------------------------------- storage */

	function load() {
		try {
			const s = JSON.parse(localStorage.getItem(STATE_KEY) || 'null');
			if (s && typeof s === 'object') {
				['src', 'example', 'bpId', 'knobs', 'fe', 'speed', 'runs', 'zoom'].forEach(function (k) { if (s[k] !== undefined) state[k] = s[k]; });
			}
		} catch (e) { /* private mode, blocked storage: defaults are fine */ }
		if (!findPredictor(state.bpId)) state.bpId = 'PAg';
		if (!(state.speed >= 0 && state.speed < SPEEDS.length)) state.speed = 3;
		if (!Array.isArray(state.runs)) state.runs = [];
		if (!state.knobs || typeof state.knobs !== 'object') state.knobs = {};
		if (!state.zoom || typeof state.zoom !== 'object') state.zoom = {};
	}

	let saveTimer = 0;
	function save() {
		clearTimeout(saveTimer);
		saveTimer = setTimeout(function () {
			try { localStorage.setItem(STATE_KEY, JSON.stringify(state)); } catch (e) { /* ignore */ }
		}, 250);
	}

	// Knob values live in one object per predictor (and one for the front-end) that the
	// widgets edit directly, so these must repair values in place, never replace the object.
	function sanitise(list, k) {
		list.forEach(function (kn) {
			if (kn.type === 'choice') {
				const ok = kn.options.some(function (o) { return (typeof o === 'object' ? o.v : o) === k[kn.id]; });
				if (!ok) k[kn.id] = kn.def;
			} else {
				const v = Number(k[kn.id]);
				const pow2ok = kn.type !== 'pow2' || (v & (v - 1)) === 0;
				if (!(v >= kn.min && v <= kn.max) || !pow2ok) k[kn.id] = kn.def;
				else k[kn.id] = v;
			}
		});
		return k;
	}

	function knobsFor(d) {
		if (!state.knobs[d.id] || typeof state.knobs[d.id] !== 'object') state.knobs[d.id] = defaultKnobs(d);
		return sanitise(d.knobs, state.knobs[d.id]);
	}

	function feKnobs() {
		if (!state.fe || typeof state.fe !== 'object') state.fe = {};
		return sanitise(FE_KNOBS, state.fe);
	}

	/* --------------------------------------------------------------- knobs */

	function el(tag, cls, text) {
		const e = document.createElement(tag);
		if (cls) e.className = cls;
		if (text !== undefined) e.textContent = text;
		return e;
	}

	function knobValueText(kn, v) {
		if (kn.type === 'choice') {
			const o = kn.options.filter(function (x) { return (typeof x === 'object' ? x.v : x) === v; })[0];
			return o && typeof o === 'object' ? o.label : String(v);
		}
		return Number(v).toLocaleString() + (kn.unit ? ' ' + kn.unit : '');
	}

	// Knobs moved away from their default are highlighted, and every knob's tooltip names its default.
	function buildKnobs(container, list, values, onChange) {
		container.innerHTML = '';
		list.forEach(function (kn) {
			const wrap = el('label', 'knob');
			wrap.title = (kn.help ? kn.help + ' ' : '') + 'Default: ' + knobValueText(kn, kn.def) + '.';
			const mark = function () { wrap.classList.toggle('knob-changed', values[kn.id] !== kn.def); };
			mark();
			wrap.appendChild(el('span', 'knob-l', kn.label));
			if (kn.type === 'choice') {
				const sel = el('select', 'sel sel-sm');
				kn.options.forEach(function (o) {
					const v = typeof o === 'object' ? o.v : o;
					const opt = el('option', null, typeof o === 'object' ? o.label : String(o));
					opt.value = String(v);
					if (v === values[kn.id]) opt.selected = true;
					sel.appendChild(opt);
				});
				sel.addEventListener('change', function () {
					const o = kn.options[sel.selectedIndex];
					values[kn.id] = typeof o === 'object' ? o.v : o;
					mark();
					onChange();
				});
				wrap.appendChild(sel);
			} else {
				const pow = kn.type === 'pow2';
				const r = el('input', 'range');
				r.type = 'range';
				r.min = pow ? Math.log2(kn.min) : kn.min;
				r.max = pow ? Math.log2(kn.max) : kn.max;
				r.step = 1;
				r.value = pow ? Math.log2(values[kn.id]) : values[kn.id];
				const out = el('output', 'knob-v', knobValueText(kn, values[kn.id]));
				r.addEventListener('input', function () {
					const v = pow ? Math.pow(2, Number(r.value)) : Number(r.value);
					values[kn.id] = v;
					out.textContent = knobValueText(kn, v);
					mark();
					onChange();
				});
				wrap.appendChild(r);
				wrap.appendChild(out);
			}
			container.appendChild(wrap);
		});
	}

	function atDefaults(list, values) {
		return list.every(function (kn) { return values[kn.id] === kn.def; });
	}

	function updateDefaultsButton() {
		$('btnBpDefaults').disabled = atDefaults(def.knobs, knobsFor(def));
	}

	// Put the selected predictor's knobs back where they started. The widgets edit this
	// object directly, so it is reset in place and the widgets rebuilt from it.
	function restoreDefaults() {
		const k = knobsFor(def);
		def.knobs.forEach(function (kn) { k[kn.id] = kn.def; });
		buildKnobs($('bpKnobs'), def.knobs, k, onKnobChange);
		updateDefaultsButton();
		save();
		resetCore(def.name + ' knobs back to defaults');
	}

	function onKnobChange() {
		updateDefaultsButton();
		save();
		resetCore('knobs changed');
	}

	/* -------------------------------------------------------------- setup */

	function buildMenus() {
		const sel = $('bpSel');
		const groups = {};
		PREDICTORS.forEach(function (d) {
			if (!groups[d.group]) {
				groups[d.group] = el('optgroup');
				groups[d.group].label = d.group;
				sel.appendChild(groups[d.group]);
			}
			const o = el('option', null, d.name + ' — ' + d.title);
			o.value = d.id;
			groups[d.group].appendChild(o);
		});
		sel.value = state.bpId;
		sel.addEventListener('change', function () {
			state.bpId = sel.value;
			zooms.bp.resetPan();
			save();
			selectPredictor();
			resetCore('predictor changed');
		});

		const ex = $('exampleSel');
		ex.appendChild(el('option', null, 'Examples…'));
		EXAMPLES.forEach(function (e, i) {
			const o = el('option', null, e.name);
			o.value = String(i);
			ex.appendChild(o);
		});
		ex.addEventListener('change', function () {
			const i = Number(ex.value);
			if (!(i >= 0)) return;
			state.src = EXAMPLES[i].src;
			state.example = i;
			$('src').value = state.src;
			ex.selectedIndex = 0;
			onSourceInput();
			doCompile();
		});

		const sp = $('speedSel');
		SPEEDS.forEach(function (s, i) {
			const o = el('option', null, s.l);
			o.value = String(i);
			sp.appendChild(o);
		});
		sp.value = String(state.speed);
		sp.addEventListener('change', function () { state.speed = Number(sp.value); save(); acc = 0; });

		buildKnobs($('feKnobs'), FE_KNOBS, feKnobs(), onKnobChange);
	}

	function selectPredictor() {
		def = findPredictor(state.bpId);
		const k = knobsFor(def);
		$('bpKnobTitle').textContent = def.name;
		buildKnobs($('bpKnobs'), def.knobs, k, onKnobChange);
		updateDefaultsButton();
		$('bpTitle').textContent = 'Direction predictor · ' + def.name + ' (' + def.figure + ')';
		$('bpAbout').textContent = def.about;
	}

	/* ----------------------------------------------------------- zoom, pan */

	// Each figure sits in a clipping viewport. The figure element keeps its zoom and pan while
	// the SVG inside it is replaced every cycle: it is sized to zoom x the fitted width and
	// shifted by the pan offset. Zooming out shrinks the viewport with the figure; zooming in
	// keeps the fitted height and the figure is dragged around inside it. The fitted width is
	// never below MIN_W, so on a phone the figure pans sideways rather than shrinking its text.
	const ZOOM_MIN = 0.5, ZOOM_MAX = 4, ZOOM_STEP = 1.25, MIN_W = 560;

	function clampZoom(k) { return Math.min(ZOOM_MAX, Math.max(ZOOM_MIN, Number(k) || 1)); }

	function makeZoom(key, view, fig, label) {
		let k = clampZoom(state.zoom[key]), x = 0, y = 0, g = null, drag = null;

		// Geometry of the current SVG at zoom k: figure size and the viewport height it needs.
		function measure() {
			const svg = fig.querySelector('svg');
			const vb = svg && svg.viewBox && svg.viewBox.baseVal;
			if (!vb || !vb.width) return null;
			const vw = view.clientWidth, base = Math.max(vw, MIN_W), ar = vb.height / vb.width;
			const fw = base * k, fh = fw * ar;
			return { vw: vw, fw: fw, fh: fh, vh: Math.min(fh, base * ar) };
		}

		function apply() {
			g = measure();
			label.textContent = Math.round(k * 100) + '%';
			if (!g) {   // nothing drawn yet: plain layout
				fig.style.width = fig.style.transform = view.style.height = '';
				view.classList.remove('pannable', 'pan-x');
				return;
			}
			x = Math.min(Math.max(0, x), Math.max(0, g.fw - g.vw));
			y = Math.min(Math.max(0, y), Math.max(0, g.fh - g.vh));
			const panX = g.fw > g.vw + 0.5, panY = g.fh > g.vh + 0.5;
			fig.style.width = g.fw + 'px';
			fig.style.transform = 'translate(' + (panX ? -x : (g.vw - g.fw) / 2) + 'px,' + (-y) + 'px)';
			view.style.height = g.vh + 'px';
			view.classList.toggle('pannable', panX || panY);
			view.classList.toggle('pan-x', panX && !panY);
		}

		// Zoom to nk, keeping the figure point under (cx, cy) (viewport pixels) where it is.
		function set(nk, cx, cy) {
			nk = clampZoom(nk);
			if (g) {
				if (cx === undefined) { cx = g.vw / 2; cy = g.vh / 2; }
				const left = g.fw > g.vw ? -x : (g.vw - g.fw) / 2;
				const r = nk / k;
				x = (cx - left) * r - cx;
				y = (cy + y) * r - cy;
			}
			k = nk;
			state.zoom[key] = k;
			save();
			apply();
		}

		function fit() { x = y = 0; set(1); }

		view.addEventListener('pointerdown', function (e) {
			if (e.button !== 0 || !view.classList.contains('pannable')) return;
			if (e.pointerType === 'mouse') e.preventDefault();   // no text selection while dragging
			drag = { id: e.pointerId, sx: e.clientX, sy: e.clientY, x: x, y: y };
			try { view.setPointerCapture(e.pointerId); } catch (err) { /* pointer already gone */ }
			view.classList.add('dragging');
		});
		view.addEventListener('pointermove', function (e) {
			if (!drag || e.pointerId !== drag.id) return;
			x = drag.x - (e.clientX - drag.sx);
			y = drag.y - (e.clientY - drag.sy);
			apply();
		});
		const end = function (e) {
			if (drag && e.pointerId === drag.id) { drag = null; view.classList.remove('dragging'); }
		};
		view.addEventListener('pointerup', end);
		view.addEventListener('pointercancel', end);
		// Ctrl + scroll (and a trackpad pinch, which arrives as one) zooms; plain scrolling still scrolls the page.
		view.addEventListener('wheel', function (e) {
			if (!(e.ctrlKey || e.metaKey) || !g) return;
			e.preventDefault();
			const r = view.getBoundingClientRect();
			const d = e.deltaY * (e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? 400 : 1);
			set(k * Math.exp(-d * 0.0025), e.clientX - r.left, e.clientY - r.top);
		}, { passive: false });
		view.addEventListener('dblclick', fit);

		return {
			apply: apply,
			fit: fit,
			zoomBy: function (f) { set(k * f); },
			resetPan: function () { x = y = 0; }
		};
	}

	function setupZoom() {
		zooms = {
			fe: makeZoom('fe', $('feView'), $('feFig'), $('feZoomFit')),
			bp: makeZoom('bp', $('bpView'), $('bpFig'), $('bpZoomFit'))
		};
		['fe', 'bp'].forEach(function (z) {
			$(z + 'ZoomOut').addEventListener('click', function () { zooms[z].zoomBy(1 / ZOOM_STEP); });
			$(z + 'ZoomIn').addEventListener('click', function () { zooms[z].zoomBy(ZOOM_STEP); });
			$(z + 'ZoomFit').addEventListener('click', function () { zooms[z].fit(); });
		});
		window.addEventListener('resize', function () { zooms.fe.apply(); zooms.bp.apply(); });
	}

	/* --------------------------------------------------------------- compile */

	function doCompile() {
		stop();
		const src = $('src').value;
		state.src = src;
		save();
		try {
			program = compile(src);
			compiledSrc = src;
			$('btnCompile').classList.remove('stale');
			buildAsm();
			buildGutter();
			status('Compiled: ' + program.instrs.length + ' instructions, ' + program.branches.length + ' conditional branch' +
				(program.branches.length === 1 ? '' : 'es') + '.', 'ok');
			setErrorLine(0);
			resetCore(null);
		} catch (e) {
			program = null;
			core = null;
			compiledSrc = null;
			$('asm').innerHTML = '';
			$('asmMeta').textContent = '';
			asmRows = [];
			buildGutter();
			setErrorLine(e.line || 0);
			status('Compile error' + (e.line ? ' (line ' + e.line + ')' : '') + ': ' + e.message, 'bad');
			renderAll(false);
		}
	}

	function buildAsm() {
		const box = $('asm');
		box.innerHTML = '';
		asmRows = [];
		const frag = document.createDocumentFragment();
		program.listing.forEach(function (l) {
			if (l.kind === 'label') {
				frag.appendChild(el('div', 'al al-label', l.name + ':'));
				return;
			}
			const ins = program.instrs[l.i];
			const row = el('div', 'al');
			row.appendChild(el('span', 'al-pc', hex(ins.pc, 16)));
			const txt = el('span', 'al-ins' + (ins.kind === 'cond' ? ' al-br' : ''), ins.text);
			row.appendChild(txt);
			row.appendChild(el('span', 'al-tag', ins.brId >= 0 ? brName(ins.brId) : ins.note ? '; ' + ins.note : ''));
			row.appendChild(el('span', 'al-st', ''));
			row.title = 'line ' + ins.line;
			row.dataset.line = String(ins.line);
			row.addEventListener('mouseenter', function () { hoverLine(ins.line); });
			row.addEventListener('mouseleave', function () { hoverLine(0); });
			frag.appendChild(row);
			asmRows[l.i] = row;
		});
		box.appendChild(frag);
		$('asmMeta').textContent = program.instrs.length + ' instructions · text at ' + hex(program.instrs[0].pc, 16);
	}

	/* ---------------------------------------------------------------- editor */

	const LINE_H = 20;
	let hlLines = [];

	function onSourceInput() {
		const src = $('src').value;
		state.src = src;
		save();
		const n = src.split('\n').length;
		$('src').style.height = (n * LINE_H + 16) + 'px';
		buildHighlight(n);
		buildGutter();
		const stale = program === null || src !== compiledSrc;
		$('btnCompile').classList.toggle('stale', stale && src !== compiledSrc);
		if (src !== compiledSrc && compiledSrc !== null) status('Source changed: press Compile (Ctrl+Enter) to rebuild.', 'warn');
	}

	function buildHighlight(n) {
		const hl = $('edHl');
		hl.innerHTML = '';
		hlLines = [];
		for (let i = 0; i < n; i++) {
			const d = el('div', 'hl');
			hl.appendChild(d);
			hlLines.push(d);
		}
	}

	function buildGutter() {
		const n = $('src').value.split('\n').length;
		const labels = {};
		if (program && compiledSrc === $('src').value) {
			program.branches.forEach(function (b) { (labels[b.line] = labels[b.line] || []).push(b.label); });
		}
		const g = $('gutter');
		g.innerHTML = '';
		for (let i = 1; i <= n; i++) {
			const d = el('div', 'gl');
			d.appendChild(el('span', 'gl-br', labels[i] ? labels[i].join(' ') : ''));
			d.appendChild(el('span', 'gl-n', String(i)));
			g.appendChild(d);
		}
	}

	let errLine = 0;
	function setErrorLine(l) {
		errLine = l;
		hlLines.forEach(function (d, i) { d.classList.toggle('err', i + 1 === l); });
	}

	function hoverLine(l) {
		hlLines.forEach(function (d, i) { d.classList.toggle('hover', i + 1 === l); });
	}

	/* ------------------------------------------------------------------ run */

	function resetCore(reason) {
		stop();
		recordRun();
		core = null;
		recorded = false;
		const k = knobsFor(def);
		const err = def.validate(k);
		$('budget').classList.toggle('bad', !!err);
		if (err) {
			$('budget').textContent = def.name + ': ' + err;
			status('Invalid configuration: ' + err, 'bad');
			renderAll(false);
			return;
		}
		if (!program) { renderAll(false); updateBudget(def.create(k, {})); return; }
		core = new Core(program, def, k, feKnobs());
		updateBudget(core.bp);
		$('log').innerHTML = '';
		logRows = 0;
		if (reason) logNote('Reset (' + reason + '): ' + def.name + ' ' + knobSummary(def, k));
		renderAll(false);
		if (reason) status('Reset: ' + reason + '.', 'ok');
	}

	function updateBudget(bp) {
		$('budget').textContent = def.name + ' · storage ' + fmtBytes(bp.storageBits()) + ' · ' + bp.latency + '-cycle lookup';
	}

	function recordRun() {
		if (!core || recorded || core.cycle === 0) return;
		recorded = true;
		const s = core.summary();
		state.runs.unshift({
			bp: core.def.name,
			knobs: knobSummary(core.def, core.knobs),
			fe: 'depth ' + core.fe.depth + ', BTB ' + (core.fe.btb || 'ideal') + ', ' + core.fe.history,
			budget: fmtBytes(core.bp.storageBits()),
			acc: s.accuracy, mpki: s.mpki, ipc: s.ipc, cycles: s.cycles, branches: s.branches,
			done: core.done && !core.error
		});
		if (state.runs.length > 15) state.runs.length = 15;
		save();
		renderRuns();
	}

	function ensureCore() {
		if (!program || $('src').value !== compiledSrc) doCompile();
		return !!core;
	}

	function stepOnce() {
		if (!ensureCore()) return;
		stop();
		if (core.done) { status('The run has finished; press Reset to run again.', 'warn'); return; }
		core.logOn = true;
		core.step();
		renderAll(true, 1000);
		if (core.done) finish();
	}

	function play(toEnd) {
		if (!ensureCore()) return;
		if (core.done) resetCore('replay');
		if (!core) return;
		playing = true;
		runToEnd = !!toEnd;
		$('btnPlay').setAttribute('aria-pressed', 'true');
		$('btnPlay').textContent = 'Pause';
		lastT = performance.now();
		acc = 0;
		rafId = requestAnimationFrame(frame);
	}

	function stop() {
		if (!playing) return;
		playing = false;
		runToEnd = false;
		cancelAnimationFrame(rafId);
		$('btnPlay').setAttribute('aria-pressed', 'false');
		$('btnPlay').textContent = 'Play';
		if (core) {
			core.logOn = true;
			renderAll(false);
		}
	}

	function frame(t) {
		if (!playing || !core) return;
		const dt = Math.min(250, t - lastT);
		lastT = t;
		const sp = runToEnd ? Infinity : SPEEDS[state.speed].v;
		if (sp <= ANIM_MAX) {
			core.logOn = true;
			acc += (sp * dt) / 1000;
			if (acc >= 1) {
				acc = Math.min(acc - 1, 1);
				core.step();
				renderAll(true, 1000 / sp);
			}
		} else {
			core.logOn = false;
			const t0 = performance.now();
			let budget = sp === Infinity ? Infinity : (acc += (sp * dt) / 1000);
			while (!core.done && budget >= 1 && performance.now() - t0 < 14) {
				const n = Math.min(512, Math.floor(budget));
				const did = core.run(n);
				if (sp !== Infinity) { acc -= did; budget = acc; }
			}
			renderAll(false);
		}
		if (core.done) { finish(); return; }
		rafId = requestAnimationFrame(frame);
	}

	function finish() {
		const wasPlaying = playing;
		stop();
		if (!wasPlaying) renderAll(false);
		const s = core.summary();
		if (core.error) {
			status('Stopped: ' + core.error.message + (core.error.line ? ' (line ' + core.error.line + ')' : ''), 'bad');
		} else {
			status('Finished in ' + s.cycles.toLocaleString() + ' cycles: accuracy ' + pct(s.accuracy) + ', MPKI ' + s.mpki.toFixed(2) + ', IPC ' + s.ipc.toFixed(3) + '.', 'ok');
			const vals = program.scalars.map(function (v) { return v.name + ' = ' + core.m.read(v.name); });
			if (vals.length) logNote('Final values: ' + vals.join(', '));
		}
		recordRun();
	}

	/* -------------------------------------------------------------- render */

	function pct(x) { return (Math.round(x * 10000) / 100).toFixed(2) + '%'; }

	function status(msg, kind) {
		const s = $('status');
		s.textContent = msg;
		s.className = 'status-msg' + (kind ? ' st-' + kind : '');
	}

	// flow: animate this cycle's data movement over `period` ms (the time until the next cycle).
	function renderAll(flow, period) {
		renderFigures(flow, period);
		renderLog();
		renderStats();
		renderMarks(flow);
		$('btnStep').disabled = !program;
		$('btnPlay').disabled = !program;
		$('btnRun').disabled = !program;
	}

	function renderFigures(flow, period) {
		// The staggered wire animation must finish before the next redraw; below ~90 ms it is skipped.
		const budget = Math.min(900, (period || 1000) * 0.8);
		const anim = !!flow && budget >= 90;
		['feFig', 'bpFig'].forEach(function (id) {
			$(id).classList.toggle('flow', anim);
			$(id).style.setProperty('--flow', Math.round(budget) + 'ms');
		});
		if (core) {
			$('feFig').innerHTML = drawFrontEnd(core, def);
			$('bpFig').innerHTML = core.bp.figure(core.predView());
			const wrong = core.st.filter(function (u) { return u && u.wrong; }).length;
			$('cycleMeta').textContent = 'cycle ' + core.cycle.toLocaleString() + (wrong ? ' · ' + wrong + ' wrong-path in flight' : '') +
				(core.done ? ' · finished' : '');
			$('bpMeta').textContent = 'stress: ' + core.bp.tables().map(function (t) { return t.name + ' ' + STRESS_NAMES[t.level]; }).join(', ');
		} else {
			const k = knobsFor(def);
			if (!def.validate(k)) {
				const bp = def.create(k, {});
				$('bpFig').innerHTML = bp.figure({ read: null, upd: null });
			} else {
				$('bpFig').innerHTML = '';
			}
			$('feFig').innerHTML = '<p class="fig-empty">Compile a program to start the front-end.</p>';
			$('cycleMeta').textContent = '';
			$('bpMeta').textContent = '';
		}
		zooms.fe.apply();
		zooms.bp.apply();
	}

	let logRows = 0;
	function logLine(c, cls, stage, text) {
		const box = $('log');
		const row = el('div', 'lg lg-' + cls);
		row.appendChild(el('span', 'lg-c', c === null ? '' : 'c' + c));
		row.appendChild(el('span', 'lg-s', stage));
		row.appendChild(el('span', 'lg-t', text));
		box.appendChild(row);
		logRows++;
		while (logRows > LOG_MAX) { box.removeChild(box.firstChild); logRows--; }
	}

	function logNote(text) { logLine(null, 'note', '', text); scrollLog(); }

	function scrollLog() { const b = $('log'); b.scrollTop = b.scrollHeight; }

	let pausedNote = false;
	function renderLog() {
		if (!core) return;
		if (!core.logOn && playing) {
			if (!pausedNote) { logNote('Log paused above ' + ANIM_MAX + ' cycles/s; it resumes when you pause or step.'); pausedNote = true; }
			$('logMeta').textContent = 'paused at this speed';
			return;
		}
		pausedNote = false;
		$('logMeta').textContent = '';
		if (!core.log.length) return;
		const items = core.log.splice(0, core.log.length);
		const start = Math.max(0, items.length - LOG_MAX);
		for (let i = start; i < items.length; i++) logLine(items[i].c, items[i].cls, items[i].stage, items[i].text);
		scrollLog();
	}

	function tile(v, k, cls) {
		return '<div class="tile' + (cls ? ' ' + cls : '') + '"><div class="tile-v">' + v + '</div><div class="tile-k">' + k + '</div></div>';
	}

	function renderStats() {
		const box = $('stats');
		if (!core) { box.innerHTML = '<p class="fig-empty">No run yet.</p>'; $('perBranch').innerHTML = ''; return; }
		const s = core.summary();
		let h = '<div class="tiles">';
		h += tile(s.branches ? pct(s.accuracy) : '—', 'accuracy', 'tile-main');
		h += tile(s.mpki.toFixed(2), 'MPKI');
		h += tile(s.mispred.toLocaleString() + ' / ' + s.branches.toLocaleString(), 'mispredicted');
		h += tile(s.ipc.toFixed(3), 'IPC');
		h += tile(s.cycles.toLocaleString(), 'cycles');
		h += tile(s.retired.toLocaleString(), 'instructions');
		h += tile(s.squashed.toLocaleString(), 'wrong-path squashed');
		h += tile(s.lost.toLocaleString(), 'cycles lost');
		h += tile(s.btbMiss.toLocaleString(), 'BTB misses');
		h += tile(s.latencyBubbles.toLocaleString(), 'lookup bubbles');
		h += '</div><div class="tables">';
		core.bp.tables().forEach(function (t) {
			h += '<div class="trow"><span class="chip s' + t.level + '">' + STRESS_NAMES[t.level] + '</span><b>' + t.name + '</b> ' +
				'<span class="dim">' + t.size.toLocaleString() + ' entries · ' + t.describe() + '</span></div>';
		});
		h += '</div>';
		box.innerHTML = h;

		const pb = core.stats.perBranch;
		let t = '<table class="tbl"><thead><tr><th>branch</th><th>PC</th><th>line</th><th>executed</th><th>taken</th><th>mispredicted</th><th>accuracy</th></tr></thead><tbody>';
		program.branches.forEach(function (b, i) {
			const x = pb[i];
			const a = x.n ? 1 - x.mis / x.n : 0;
			t += '<tr data-line="' + b.line + '"><td class="mono">' + b.label + '</td><td class="mono">' + hex(b.pc, 16) + '</td><td>' + b.line + '</td><td>' + x.n.toLocaleString() +
				'</td><td>' + (x.n ? Math.round((100 * x.taken) / x.n) + '%' : '—') + '</td><td>' + x.mis.toLocaleString() +
				'</td><td><span class="bar"><i style="width:' + (a * 100).toFixed(1) + '%"></i></span> ' + (x.n ? pct(a) : '—') + '</td></tr>';
		});
		t += '</tbody></table>';
		$('perBranch').innerHTML = t;
	}

	function renderRuns() {
		const box = $('runs');
		if (!state.runs.length) { box.innerHTML = '<p class="fig-empty">Finished (and interrupted) runs are listed here, newest first.</p>'; return; }
		let best = -1;
		state.runs.forEach(function (r) { if (r.done && r.acc > best) best = r.acc; });
		let t = '<table class="tbl"><thead><tr><th>predictor</th><th>knobs</th><th>front-end</th><th>storage</th><th>accuracy</th><th>MPKI</th><th>IPC</th><th>cycles</th></tr></thead><tbody>';
		state.runs.forEach(function (r) {
			t += '<tr' + (r.done && r.acc === best ? ' class="best"' : '') + '><td><b>' + r.bp + '</b>' + (r.done ? '' : ' <span class="dim">(partial)</span>') +
				'</td><td class="mono">' + r.knobs + '</td><td class="dim">' + r.fe + '</td><td>' + r.budget + '</td><td>' + pct(r.acc) +
				'</td><td>' + r.mpki.toFixed(2) + '</td><td>' + r.ipc.toFixed(3) + '</td><td>' + r.cycles.toLocaleString() + '</td></tr>';
		});
		box.innerHTML = t + '</tbody></table>';
	}

	// Highlight the instructions in flight in the assembly, and their source lines.
	function renderMarks(flow) {
		marked.forEach(function (r) { r.classList.remove('m-f', 'm-x', 'm-p', 'm-w', 'm-sq'); r.lastChild.textContent = ''; });
		marked = [];
		hlLines.forEach(function (d) { d.classList.remove('cur-f', 'cur-x'); });
		if (!core || !asmRows.length) return;
		const ev = core.ev;
		const mark = function (u, stage, squashed) {
			const i = (u.pc - program.instrs[0].pc) >>> 2;
			const row = asmRows[i];
			if (!row) return;
			const D = core.D;
			row.classList.add(stage === 0 ? 'm-f' : stage === D - 1 ? 'm-x' : 'm-p');
			if (u.wrong) row.classList.add('m-w');
			if (squashed) row.classList.add('m-sq');
			const tag = row.lastChild;
			tag.textContent = (tag.textContent ? tag.textContent + ' ' : '') + (stage === 0 ? 'F' : stage === D - 1 ? 'X' : stage === 2 ? 'D' : String(stage + 1));
			marked.push(row);
			if (!u.wrong && !squashed) {
				const hl = hlLines[u.ins.line - 1];
				if (hl && stage === D - 1) hl.classList.add('cur-x');
				if (hl && stage === 0) hl.classList.add('cur-f');
			}
		};
		core.st.forEach(function (u, i) { if (u) mark(u, i, false); });
		if (ev) ev.squashed.forEach(function (q) { mark(q.u, q.stage, true); });
		if (flow && ev && ev.fetched) {
			const row = asmRows[(ev.fetched.pc - program.instrs[0].pc) >>> 2];
			const box = $('asm');
			if (row) {
				const top = row.offsetTop;
				if (top < box.scrollTop + 20 || top > box.scrollTop + box.clientHeight - 40) box.scrollTop = top - box.clientHeight / 3;
			}
		}
	}

	/* --------------------------------------------------------------- theme */

	function syncTheme() {
		const attr = document.documentElement.getAttribute('data-theme');
		const dark = attr ? attr === 'dark' : window.matchMedia('(prefers-color-scheme: dark)').matches;
		$('themeIco').textContent = dark ? '☾' : '☀';
		$('btnTheme').setAttribute('aria-label', dark ? 'Switch to light theme' : 'Switch to dark theme');
	}

	function toggleTheme() {
		const attr = document.documentElement.getAttribute('data-theme');
		const dark = attr ? attr === 'dark' : window.matchMedia('(prefers-color-scheme: dark)').matches;
		const t = dark ? 'light' : 'dark';
		document.documentElement.setAttribute('data-theme', t);
		try { localStorage.setItem(THEME_KEY, t); } catch (e) { /* ignore */ }
		syncTheme();
	}

	/* ---------------------------------------------------------------- wire */

	function typing(e) {
		const t = e.target;
		return t && (t.tagName === 'TEXTAREA' || t.tagName === 'INPUT' || t.tagName === 'SELECT');
	}

	function init() {
		load();
		setupZoom();
		buildMenus();
		selectPredictor();
		$('src').value = state.src;
		onSourceInput();
		renderRuns();

		$('src').addEventListener('input', onSourceInput);
		$('src').addEventListener('keydown', function (e) {
			if (e.key === 'Tab') {
				e.preventDefault();
				const ta = e.target, a = ta.selectionStart, b = ta.selectionEnd;
				ta.value = ta.value.slice(0, a) + '    ' + ta.value.slice(b);
				ta.selectionStart = ta.selectionEnd = a + 4;
				onSourceInput();
			}
			if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); doCompile(); }
		});
		$('btnCompile').addEventListener('click', doCompile);
		$('btnStep').addEventListener('click', stepOnce);
		$('btnPlay').addEventListener('click', function () { if (playing) stop(); else play(false); });
		$('btnRun').addEventListener('click', function () { play(true); });
		$('btnReset').addEventListener('click', function () { resetCore('reset'); });
		$('btnClearRuns').addEventListener('click', function () { state.runs = []; save(); renderRuns(); });
		$('btnBpDefaults').addEventListener('click', restoreDefaults);
		$('btnTheme').addEventListener('click', toggleTheme);
		$('btnHelp').addEventListener('click', function () { $('helpModal').hidden = false; $('helpClose').focus({ preventScroll: true }); });
		$('helpClose').addEventListener('click', function () { $('helpModal').hidden = true; });
		$('helpX').addEventListener('click', function () { $('helpModal').hidden = true; });
		$('helpModal').addEventListener('click', function (e) { if (e.target === $('helpModal')) $('helpModal').hidden = true; });
		window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', syncTheme);
		syncTheme();

		document.addEventListener('keydown', function (e) {
			if (e.key === 'Escape') { $('helpModal').hidden = true; return; }
			if (typing(e) || e.ctrlKey || e.metaKey || e.altKey) return;
			if (e.target.tagName === 'BUTTON' && (e.key === ' ' || e.key === 'Enter')) return;
			if (e.key === ' ' || e.key === 's') { e.preventDefault(); stepOnce(); }
			else if (e.key === 'p') { if (playing) stop(); else play(false); }
			else if (e.key === 'e') play(true);
			else if (e.key === 'r') resetCore('reset');
			else if (e.key === '?') $('helpModal').hidden = false;
		});

		doCompile();
		BP.started = true;   // read by the start-up watchdog in bp.html
	}

	init();

})(window.BP = window.BP || {});
