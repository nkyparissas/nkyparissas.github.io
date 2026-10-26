/* ==========================================================================
   /bp: the 2-bit counter (2bc) baseline of Section III, drawn as the survey's
   Fig. 6(c): branch address bits pick one N-bit counter.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, CounterTable, log2, hex, pcField, brName, interferenceText } = BP.base;
	const { callouts } = BP.figure;
	const S = BP.svg;

	class Bimodal extends Predictor {
		constructor(knobs, opts) {
			super(knobs, opts);
			this.rows = knobs.rows;
			this.ib = log2(knobs.rows);
			this.tbl = new CounterTable(knobs.rows, knobs.n, 'Counter table');
			this.latency = 1;
		}

		tables() { return [this.tbl]; }
		storageBits() { return this.rows * this.k.n; }

		lookup(pc, br) {
			const idx = (pc >>> 2) & (this.rows - 1);
			const rd = this.tbl.read(idx, br);
			return { taken: rd.taken, idx: idx, ctr: rd.v, alias: rd.alias, prev: rd.prev, priv: rd.privTaken };
		}

		shiftHistory() { /* no history */ }

		train(p, taken, mis) {
			const before = this.tbl.ctr[p.idx];
			const after = this.tbl.train(p.idx, taken, p.br);
			const inter = this.tbl.noteOutcome(p.taken, p.priv, taken);
			return { idx: p.idx, before: before, after: after, inter: inter };
		}

		describePredict(p) {
			let s = pcField(2, this.ib) + ' = ' + hex(p.idx, this.ib) + ' → ctr[' + hex(p.idx, this.ib) + '] = ' + this.tbl.fmt(p.ctr);
			if (p.alias) s += ' (last trained by ' + brName(p.prev) + ': aliasing)';
			return { text: s + ' → predict ' + (p.taken ? 'T' : 'NT'), warn: p.alias };
		}

		describeUpdate(u) {
			let s = 'ctr[' + hex(u.idx, this.ib) + '] ' + this.tbl.fmt(u.before) + '→' + this.tbl.fmt(u.after);
			s += interferenceText(u.inter, u.p.br, u.p.prev, u.taken);
			return { text: s, warn: u.inter === 'destructive' };
		}

		warnings(p) {
			return p.alias ? ['ctr[' + hex(p.idx, this.ib) + '] last trained by ' + brName(p.prev) + ': aliasing'] : [];
		}

		figure(view) {
			const p = view.read, u = view.upd;
			const rOn = !!(p && view.readNow), uOn = !!(u && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const n = this.k.n;
			const w = Math.max(56, 28 * n);
			const col = S.column({
				x: 300, y: 110, w: w, rh: 28, gap: 38, sub: n, level: this.tbl.level,
				read: p ? 1 : -1, readTxt: p ? this.tbl.fmt(p.ctr) : null, seqRead: 1,
				write: u ? (p && u.idx === p.idx ? 1 : 2) : -1, writeTxt: u ? '→' + this.tbl.fmt(u.after) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
			});
			const ry = col.rowY(1);
			let s = S.figLabel(10, 8, '2bc');
			s += S.t(60, 84, 'Branch address', 'tx');
			s += S.wire([[110, 92], [110, ry], [298, ry]], 'rd', p ? { on: rOn, dim: !rOn, seq: 0 } : { dim: true });
			s += S.tick(200, ry, 'h', 'a = ' + this.ib);
			if (p) s += S.val(130, ry + 40, pcField(2, this.ib) + ' = ' + hex(p.idx, this.ib), rk);
			s += col.svg;
			s += S.wire([[col.cx, col.bottom], [col.cx, col.bottom + 46]], 'rd', p ? { on: rOn, dim: !rOn, seq: 2 } : { dim: true });
			s += S.t(col.cx + 10, col.bottom + 30, n + ' prediction bit' + (n > 1 ? 's' : ''), 'tx');
			if (p) s += S.val(col.cx + 10, col.bottom + 46, 'ctr ' + this.tbl.fmt(p.ctr) + ' → ' + (p.taken ? 'taken' : 'not taken'), rk);
			if (u) {
				const wy = col.rowY(p && u.idx === p.idx ? 1 : 2);
				s += S.wire([[620, wy], [col.right + 2, wy]], 'up', { on: uOn, dim: !uOn, seq: 4 });
				s += S.val(col.right + 14, wy - 8, 'train ' + this.tbl.fmt(u.before) + '→' + this.tbl.fmt(u.after), uk);
			}
			s += S.t(420, 352, this.tbl.describe(), 'dim');
			s += callouts(view, this);
			return S.svg(680, 362, s, '2-bit counter predictor');
		}
	}

	const BIMODAL = {
		id: '2bc',
		name: '2bc',
		title: 'Saturating counters indexed by address',
		group: 'III · Baseline, Fig. 6(c)',
		figure: 'Fig. 6(c)',
		knobs: [
			{ id: 'rows', label: 'counters', type: 'pow2', min: 16, max: 65536, def: 1024,
				help: 'Number of counters; log2 of this many low address bits index the table.' },
			{ id: 'n', label: 'N · counter bits', type: 'int', min: 1, max: 4, def: 2,
				help: 'Width of each saturating counter.' }
		],
		validate: function () { return null; },
		create: function (k, opts) { return new Bimodal(k, opts); },
		about: 'The simplest dynamic predictor: some branch address bits pick an N-bit saturating counter, whose top bit is the prediction. ' +
			'No history at all, so it learns each branch\'s bias but not its patterns.'
	};

	BP.bimodal = { BIMODAL };

})(window.BP = window.BP || {});
