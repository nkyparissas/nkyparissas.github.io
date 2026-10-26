/* ==========================================================================
   /bp: the CPU front-end as a block diagram, redrawn every cycle.

   PC feeds the direction predictor, the BTB and the I-cache; the next-PC mux
   chooses PC+4, the BTB target, a Decode redirect or an Execute redirect.
   Wires that carried something this cycle are drawn solid and animated;
   wrong-path instructions are hatched; squashed ones are struck out.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { hex, brName } = BP.base;
	const S = BP.svg;

	function short(u) {
		const ins = u.ins;
		const op = ins.text.split(' ')[0];
		return hex(u.pc, 16) + ' ' + op + (ins.brId >= 0 ? ' ' + brName(ins.brId) : '');
	}

	// One pipeline box with its instruction (or bubble).
	function stageBox(x, y, w, h, title, u, squashed, extra) {
		let s = S.rect(x, y, w, h, 'fe-box');
		if (u && u.wrong) s += S.rect(x, y, w, h, 'fe-hatch');
		if (squashed) s += S.rect(x, y, w, h, 'fe-squash');
		s += S.t(x + 8, y + 15, title, 'fe-title');
		if (u) {
			s += S.t(x + 8, y + 33, short(u), 'mono' + (squashed ? ' fe-struck' : u.wrong ? ' fe-wrong' : ''));
		} else {
			s += S.t(x + 8, y + 33, 'bubble', 'dim');
		}
		if (extra) s += extra;
		return s;
	}

	function drawFrontEnd(core, def) {
		const ev = core.ev || { mux: 'seq', squashed: [] };
		const D = core.D;
		const st = core.st;
		const sq = {};
		ev.squashed.forEach(function (q) { sq[q.stage] = q.u; });
		const at = function (i) { return sq[i] || st[i]; };
		const level = core.bp.maxLevel();
		const on = function (b, seq) { return b ? { on: true, seq: seq } : { dim: true }; };

		// Pipeline box geometry.
		const BY = 180, BH = 46;
		const boxes = [{ i: 1, x: 338, w: 116, title: 'Fetch queue' }, { i: 2, x: 476, w: 104, title: 'Decode' }];
		let x = 602;
		if (D > 5) { boxes.push({ i: -1, x: x, w: 112, title: core.names.slice(3, D - 2).join(', ') }); x += 134; }
		boxes.push({ i: D - 2, x: x, w: 104, title: 'Issue' });
		x += 126;
		boxes.push({ i: D - 1, x: x, w: 124, title: 'Execute' });
		const W = x + 124 + 22;
		const ex = boxes[boxes.length - 1], dec = boxes[1];
		const exCx = ex.x + ex.w / 2, decCx = dec.x + 40;

		let s = '';
		const fetched = ev.fetched;
		const pred = ev.predicted;

		// Update path: Execute back to the direction predictor (drawn first so the loop can bridge it).
		const upOn = !!ev.resolved;
		s += S.wire([[ex.x + ex.w, BY + 23], [W - 8, BY + 23], [W - 8, 10], [185, 10], [185, 36]], 'up', on(upOn, 5));
		if (ev.resolved) {
			const r = ev.resolved.u;
			s += S.val(W - 14, 22, 'train predictor: ' + brName(r.ins.brId) + ' was ' + (r.actualTaken ? 'T' : 'NT'), 'up', 'end');
		}
		// Next-PC loop: mux output back into PC, bridging the update wire.
		const loopOn = !!(fetched || ev.redirect || ev.decodeRedirect);
		s += S.wire([[302, 100], [318, 100], [318, 26], [55, 26], [55, 93]], 'ink', loopOn ? { on: true, seq: 4 } : {});
		s += S.rect(180, 21, 10, 10, 'fe-bridge');
		s += '<path d="M185,21 L185,31" class="w w-up' + (upOn ? ' on' : ' dim') + '"/>';
		s += S.t(196, 22, 'next PC ' + hex(core.pc, 16), 'mono dim');

		// PC register.
		s += S.rect(20, 95, 70, 44, 'fe-box');
		s += S.t(30, 112, 'PC', 'fe-title');
		s += S.t(30, 130, fetched ? hex(fetched.pc, 16) : hex(core.pc, 16), fetched ? 'mono' + (fetched.wrong ? ' fe-wrong' : '') : 'mono dim');

		// Fan-out bus.
		s += S.wire([[90, 117], [104, 117]], 'ink', { arrow: false });
		s += '<path d="M104,62 L104,200" class="w w-ink"/>';
		s += S.wire([[104, 62], [118, 62]], pred ? 'rd' : 'ink', on(!!pred, 0));
		s += S.wire([[104, 120], [118, 120]], 'ink', fetched && (fetched.ins.kind === 'cond' || fetched.ins.kind === 'jump') ? { on: true, seq: 0 } : {});
		s += S.wire([[104, 200], [118, 200]], 'ink', fetched ? { on: true, seq: 0 } : {});

		// Direction predictor, tinted by its most stressed table.
		s += S.rect(120, 38, 130, 48, 'cell s' + level);
		s += S.t(130, 56, 'Direction BP', 'fe-title');
		s += S.t(130, 74, def.name + (core.bp.latency > 1 ? ' · ' + core.bp.latency + '-cycle' : ''), 'mono');
		// BTB.
		s += S.rect(120, 100, 130, 40, 'fe-box');
		s += S.t(130, 116, core.btb.ideal ? 'BTB (ideal)' : 'BTB (' + core.btb.entries + ')', 'fe-title');
		if (ev.btb) s += S.t(130, 132, ev.btb.hit ? 'hit → ' + hex(ev.btb.target, 16) : 'miss', 'mono' + (ev.btb.hit ? '' : ' v-rx'));
		// I-cache, holding the instruction fetched this cycle.
		s += S.rect(120, 180, 130, 40, 'fe-box');
		if (fetched && fetched.wrong) s += S.rect(120, 180, 130, 40, 'fe-hatch');
		s += S.t(130, 196, 'I-cache', 'fe-title');
		s += S.t(130, 212, fetched ? short(fetched) : (ev.stall ? 'stall: ' + ev.stall : '—'), fetched ? 'mono' + (fetched.wrong ? ' fe-wrong' : '') : 'dim');

		// Next-PC mux and its inputs.
		s += '<path d="M282,50 L302,62 L302,138 L282,150 Z" class="muxbox"/>';
		s += S.t(256, 163, 'nPC', 'dim');
		s += S.wire([[250, 62], [280, 62]], pred ? 'rd' : 'ink', on(!!pred, 1));
		if (pred) s += S.val(256, 56, pred.predTaken ? 'T' : 'NT', 'rd');
		s += S.wire([[250, 120], [280, 120]], ev.mux === 'btb' ? 'rd' : 'ink', ev.mux === 'btb' ? { on: true, seq: 2 } : {});
		s += S.t(256, 94, '+4', 'dim');
		s += S.wire([[262, 100], [280, 100]], 'ink', ev.mux === 'seq' && fetched ? { on: true, seq: 2 } : {});

		// Execute redirect and Decode redirect into the mux.
		s += S.wire([[exCx, BY], [exCx, 160], [296, 160], [296, 144]], 'rx', on(!!ev.redirect, 1));
		if (ev.redirect) {
			s += S.val(exCx - 6, 154, 'redirect ' + hex(ev.redirect.target, 16) + ' · flush ' + ev.squashed.length, 'rx', 'end');
		}
		s += S.wire([[decCx, BY], [decCx, 170], [288, 170], [288, 149]], 'dr', on(!!ev.decodeRedirect, 1));

		// I-cache to the fetch queue, then stage to stage.
		s += S.wire([[250, 200], [336, 200]], 'ink', fetched ? { on: true, seq: 1 } : {});
		for (let b = 0; b < boxes.length; b++) {
			const bx = boxes[b];
			let u = null, sqd = false, extra = '';
			if (bx.i >= 0) {
				u = at(bx.i);
				sqd = !!sq[bx.i];
			} else {
				let n = 0, wrong = 0, sqn = 0;
				for (let i = 3; i <= D - 3; i++) {
					const v = at(i);
					if (v) { n++; if (v.wrong) wrong++; if (sq[i]) sqn++; }
				}
				s += S.rect(bx.x, BY, bx.w, BH, 'fe-box');
				if (wrong) s += S.rect(bx.x, BY, bx.w, BH, 'fe-hatch');
				if (sqn) s += S.rect(bx.x, BY, bx.w, BH, 'fe-squash');
				s += S.t(bx.x + 8, BY + 15, (D - 5) + ' more stage' + (D - 5 > 1 ? 's' : ''), 'fe-title');
				s += S.t(bx.x + 8, BY + 33, sqn ? sqn + ' squashed' : n + ' in flight', 'mono' + (sqn ? ' fe-struck' : ''));
			}
			if (bx.i >= 0) {
				if (bx.i === D - 1 && u && ev.resolved && ev.resolved.u === u) {
					const r = ev.resolved.u;
					extra = S.t(bx.x + bx.w - 8, BY + 15, r.dirMis ? '✗ ' + (r.predTaken ? 'T' : 'NT') + '→' + (r.actualTaken ? 'T' : 'NT') : '✓', r.dirMis ? 'fe-bad' : 'fe-good', { 'text-anchor': 'end' });
				}
				s += stageBox(bx.x, BY, bx.w, BH, bx.title, u, sqd, extra);
				if (bx.i === D - 1 && ev.redirect) s += S.rect(bx.x, BY, bx.w, BH, 'fe-alarm');
			}
			if (b < boxes.length - 1) {
				const nx = boxes[b + 1].x;
				s += S.wire([[bx.x + bx.w, BY + 23], [nx - 2, BY + 23]], 'ink', {});
			}
		}

		// Stage labels.
		s += S.t(20, BY + BH + 30, 'Fetch: predict + fetch', 'dim');
		boxes.forEach(function (bx) {
			s += S.t(bx.x, BY + BH + 30, bx.i >= 0 ? 'stage ' + (bx.i + 1) : 'stages 4–' + (D - 2), 'dim');
		});
		return S.svg(W, 262, s, 'CPU front-end');
	}

	BP.frontendFigure = { drawFrontEnd };

})(window.BP = window.BP || {});
