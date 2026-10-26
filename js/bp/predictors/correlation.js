/* ==========================================================================
   /bp: Pan et al.'s (K,N) correlation predictor, survey Fig. 6(d).

   A K-bit shift register holds the outcomes of the last K branches. It splits
   each branch's history into 2^K subhistories; every address row holds one
   N-bit counter per subhistory. All 2^K counters of the row are read in
   parallel and the shift register drives the mux that picks one.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, CounterTable, GlobalHistory, log2, hex, bin, pcField, brName, interferenceText } = BP.base;
	const { callouts } = BP.figure;
	const S = BP.svg;

	class Correlation extends Predictor {
		constructor(knobs, opts) {
			super(knobs, opts);
			this.rows = knobs.rows;
			this.ib = log2(knobs.rows);
			this.K = knobs.K;
			this.sr = new GlobalHistory(knobs.K, 'shift register');
			this.tbl = new CounterTable(knobs.rows << knobs.K, knobs.n, 'Counter rows');
			this.latency = 1;
		}

		tables() { return [this.tbl]; }
		storageBits() { return this.tbl.size * this.k.n + this.K; }

		lookup(pc, br) {
			const row = (pc >>> 2) & (this.rows - 1);
			const sub = this.sr.v;
			const idx = (row << this.K) | sub;
			const rd = this.tbl.read(idx, br);
			return { taken: rd.taken, row: row, sub: sub, idx: idx, ctr: rd.v, alias: rd.alias, prev: rd.prev, priv: rd.privTaken };
		}

		shiftHistory(p, bit, undo) { p.newSub = this.sr.shift(bit, undo, p.seq); }

		train(p, taken, mis) {
			const before = this.tbl.ctr[p.idx];
			const after = this.tbl.train(p.idx, taken, p.br);
			const inter = this.tbl.noteOutcome(p.taken, p.priv, taken);
			return { idx: p.idx, row: p.row, sub: p.sub, before: before, after: after, histWritten: !this.spec || mis, newSub: p.newSub, inter: inter };
		}

		describePredict(p) {
			let s = pcField(2, this.ib) + ' = ' + hex(p.row, this.ib) + ' → row ' + hex(p.row, this.ib) +
				' (all ' + (1 << this.K) + ' counters read) · shift reg = ' + bin(p.sub, this.K) +
				' → subhistory ' + bin(p.sub, this.K) + ': ctr ' + this.tbl.fmt(p.ctr);
			if (p.alias) s += ' (last trained by ' + brName(p.prev) + ': aliasing)';
			return { text: s + ' → predict ' + (p.taken ? 'T' : 'NT'), warn: p.alias };
		}

		describeUpdate(u) {
			let s = 'row ' + hex(u.row, this.ib) + ', subhistory ' + bin(u.sub, this.K) + ': ' +
				this.tbl.fmt(u.before) + '→' + this.tbl.fmt(u.after);
			if (u.histWritten) s += ' · shift reg ← ' + (u.taken ? 1 : 0) + ' = ' + bin(u.newSub, this.K) + (u.repaired ? ' (repaired)' : '');
			s += interferenceText(u.inter, u.p.br, u.p.prev, u.taken);
			return { text: s, warn: u.inter === 'destructive' };
		}

		warnings(p) {
			return p.alias ? ['row ' + hex(p.row, this.ib) + ', subhistory ' + bin(p.sub, this.K) + ' last trained by ' + brName(p.prev) + ': aliasing'] : [];
		}

		figure(view) {
			const p = view.read, u = view.upd;
			const rOn = !!(p && view.readNow), uOn = !!(u && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const K = this.K, n = this.k.n, G = 1 << K;
			const sel = p ? p.sub : (u ? u.sub : 0);
			// Which subhistory groups to draw: all of them up to 4, else first, selected, ..., last.
			let groups;
			if (G <= 4) groups = Array.from({ length: G }, function (_, i) { return i; });
			else {
				groups = [0];
				if (sel !== 0 && sel !== G - 1) groups.push(sel);
				else groups.push(1);
				groups.push(-1);
				groups.push(G - 1);
			}
			const gw = Math.max(K > 4 ? 52 : 46, 24 * n), gap = 14;
			let x = 150;
			let s = S.figLabel(10, 8, '(' + K + ',' + n + ') corr.');
			const centres = [];
			const wsub = u ? u.sub : -1;
			const rowSame = p && u && u.row === p.row;
			groups.forEach((g) => {
				if (g < 0) {
					s += '<path d="M' + (x - 4) + ',165 L' + (x + 22) + ',165" class="gapline"/>';
					x += 30;
					return;
				}
				const isSel = p && g === sel;
				const c = S.column({
					x: x, y: 110, w: gw, rh: 26, gap: 36, sub: n, level: this.tbl.level,
					read: p ? 1 : -1, readCls: isSel ? 'h' : 'q', seqRead: 1,
					readTxt: isSel ? this.tbl.fmt(p.ctr) : null,
					write: u && g === wsub ? (rowSame ? 1 : 2) : -1, writeTxt: u && g === wsub ? '→' + this.tbl.fmt(u.after) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
				});
				s += c.svg;
				s += S.t(x + 2, 102, bin(g, K), 'mono dim');
				if (u && g === wsub) {
					s += S.wire([[x + gw - 7, 62], [x + gw - 7, 108]], 'up', { on: uOn, dim: !uOn, seq: 4 });
					s += S.val(x + gw - 1, 70, 'train ' + this.tbl.fmt(u.before) + '→' + this.tbl.fmt(u.after), uk);
				}
				centres.push({ cx: c.cx, bottom: c.bottom, sel: isSel, ry: c.rowY(1) });
				x += gw + gap;
			});
			const ry = centres[0].ry;
			s += S.t(26, 78, 'Branch address', 'tx');
			s += S.wire([[80, 86], [80, ry], [148, ry]], 'rd', p ? { on: rOn, dim: !rOn, seq: 0 } : { dim: true });
			s += S.tick(114, ry, 'h', 'a');
			if (p) s += S.val(16, ry + 46, pcField(2, this.ib) + ' = ' + hex(p.row, this.ib), rk);

			// Counter outputs into the mux.
			const my = 272, mh = 24;
			const mx1 = centres[0].cx - 14, mx2 = centres[centres.length - 1].cx + 14;
			centres.forEach(function (c) {
				s += S.wire([[c.cx, c.bottom], [c.cx, my]], 'rd', p ? { on: rOn && c.sel, dim: !(rOn && c.sel), seq: 2, arrow: false } : { dim: true, arrow: false });
			});
			s += S.mux(mx1, mx2, my, mh, 14);
			const mcx = (mx1 + mx2) / 2;
			s += S.wire([[mcx, my + mh], [mcx, my + mh + 26]], 'rd', p ? { on: rOn, dim: !rOn, seq: 3 } : { dim: true });
			s += S.t(mcx + 10, my + mh + 22, n + ' prediction bit' + (n > 1 ? 's' : ''), 'tx');
			if (p) s += S.val(mcx + 10, my + mh + 38, 'ctr ' + this.tbl.fmt(p.ctr) + ' → ' + (p.taken ? 'taken' : 'not taken'), rk);

			// K-bit shift register selects the counter.
			const ch = 14, y0 = my + mh / 2 - (K * ch) / 2;
			const bits = bin(p ? p.sub : this.sr.v, K);
			for (let i = 0; i < K; i++) {
				s += S.reg({ x: 40, y: y0 + i * ch, w: 20, h: ch, txt: bits[i], on: rOn, seq: 1 });
			}
			if (u && u.histWritten) s += S.rect(37, y0 - 3, 26, K * ch + 6, 'cell-w');
			s += S.wire([[60, my + mh / 2], [mx1 + 5, my + mh / 2]], 'rd', p ? { on: rOn, dim: !rOn, seq: 2 } : { dim: true });
			s += S.t(10, y0 + K * ch + 18, K + '-bit shift reg', 'tx sm');
			s += S.t(420, 352, this.tbl.describe(), 'dim');
			s += callouts(view, this, 150);
			return S.svg(680, 362, s, 'Correlation predictor');
		}
	}

	const CORRELATION = {
		id: 'corr',
		name: '(K,N) correlation',
		title: 'Pan et al.: subhistories selected by a K-bit shift register',
		group: 'III-A · Correlation (Pan et al.), Fig. 6(d)',
		figure: 'Fig. 6(d)',
		knobs: [
			{ id: 'rows', label: 'counter rows', type: 'pow2', min: 16, max: 4096, def: 256,
				help: 'Rows indexed by branch address; each row holds 2^K counters.' },
			{ id: 'K', label: 'K · shift register bits', type: 'int', min: 1, max: 6, def: 2,
				help: 'Outcomes of the last K branches; they split each branch\'s history into 2^K subhistories.' },
			{ id: 'n', label: 'N · counter bits', type: 'int', min: 1, max: 4, def: 2,
				help: 'Width of each counter (the paper\'s figure uses N = 2).' }
		],
		validate: function () { return null; },
		create: function (k, opts) { return new Correlation(k, opts); },
		about: 'Pan et al. observe that a branch is often decided by the branches just before it (Fig. 6(a)). The last K outcomes ' +
			'split each branch\'s history into 2^K subhistories, each predicted by its own N-bit counter.'
	};

	BP.correlation = { CORRELATION };

})(window.BP = window.BP || {});
