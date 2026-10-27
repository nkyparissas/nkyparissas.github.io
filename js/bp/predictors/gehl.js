/* ==========================================================================
   /bp: Seznec's GEHL predictor (survey Section III-E, Table IV).

   M tables of signed counters. T0 is indexed by the branch address; Ti
   (i >= 1) by a hash of the address and the newest L(i) global outcomes,
   with L(i) = floor(alpha^(i-1) * L(1) + 0.5), a geometric series. One
   counter C(i) is read from each table and
       Sum = M/2 + sum of C(i);   predict taken when Sum >= 0.
   Every counter is trained only on a misprediction or when |Sum| is at or
   below a threshold theta. As in O-GEHL, theta adapts so that updates on
   mispredictions and on low-confidence correct predictions stay balanced.
   O-GEHL's dynamic history length fitting and path history are not modelled.

   Interference is judged on the sum, not on each counter: sharing in Ti was
   destructive when the branch's own counter in its place would have turned
   a wrong sum into a right one.

   The survey has no figure for GEHL; the panel follows Fig. 9's notation
   with an adder in place of the tag comparators and muxes.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, CounterTable, LongHistory, geometric, hex, brName } = BP.base;
	const { callouts } = BP.figure;
	const S = BP.svg;

	const MAX_HIST = 2048;
	const TC_MAX = 63, TC_MIN = -64;   // 7-bit threshold-adaptation counter

	function lengths(k) { return [0].concat(geometric(k.M - 1, k.L1, k.alpha)); }
	function sgn(c) { return (c >= 0 ? '+' : '−') + Math.abs(c); }

	class GEHL extends Predictor {
		constructor(knobs, opts) {
			super(knobs, opts);
			this.M = knobs.M;
			this.lt = knobs.lt;
			this.mask = (1 << knobs.lt) - 1;
			this.L = lengths(knobs);
			this.hist = new LongHistory(this.L[this.M - 1], 'GHR');
			this.folds = this.L.map(function (L) { return L ? this.hist.addFold(L, knobs.lt) : null; }, this);
			this.T = this.L.map(function (_, i) { return new CounterTable(1 << knobs.lt, knobs.cb, 'T' + i); });
			this.adapt = knobs.adapt === 'on';
			this.theta = knobs.M;
			this.tc = 0;
			this.latency = 1;
		}

		tables() { return this.T; }
		storageBits() { return this.M * (1 << this.lt) * this.k.cb + this.L[this.M - 1] + (this.adapt ? 7 + 8 : 0); }

		index(word, i) {
			if (!i) return word & this.mask;
			return (word ^ (word >>> (Math.abs(this.lt - i) + 1)) ^ this.folds[i].comp) & this.mask;
		}

		lookup(pc, br) {
			const word = pc >>> 2;
			const p = { ix: [], ctr: [], c: [], own: [], alias: [], prev: [], recent: this.hist.text(Math.min(16, this.L[this.M - 1])) };
			let sum = this.M / 2;
			for (let i = 0; i < this.M; i++) {
				const ix = this.index(word, i);
				const rd = this.T[i].read(ix, br);
				const c = this.T[i].signed(rd.v);
				p.ix.push(ix);
				p.ctr.push(rd.v);
				p.c.push(c);
				p.own.push(this.T[i].signed(rd.pv));   // the branch's private counter, for interference
				p.alias.push(rd.alias);
				p.prev.push(rd.prev);
				sum += c;
			}
			p.sum = sum;
			p.taken = sum >= 0;
			return p;
		}

		shiftHistory(p, bit, undo) { this.hist.shift(bit, undo, p.seq); }

		train(p, taken, mis) {
			const wrong = p.taken !== taken;
			const low = Math.abs(p.sum) <= this.theta;
			const u = { wrong: wrong, low: low, go: wrong || low, theta: this.theta, after: [], inter: [], histWritten: !this.spec || mis };
			for (let i = 0; i < this.M; i++) {
				// No single counter decides here, the sum does: sharing in Ti was destructive when the branch's
				// own (private) counter in its place would have turned the sum from wrong to right.
				u.inter.push(this.T[i].noteOutcome(p.taken, p.sum - p.c[i] + p.own[i] >= 0, taken));
				u.after.push(u.go ? this.T[i].train(p.ix[i], taken, p.br) : p.ctr[i]);
			}
			if (this.adapt) {
				if (wrong) {
					if (++this.tc >= TC_MAX) { this.theta++; this.tc = 0; }
				} else if (low) {
					if (--this.tc <= TC_MIN) { this.theta = Math.max(1, this.theta - 1); this.tc = 0; }
				}
			}
			u.thetaAfter = this.theta;
			return u;
		}

		cList(arr) { return arr.map(sgn).join(' '); }

		describePredict(p) {
			let s = 'T0..T' + (this.M - 1) + ' = ' + this.cList(p.c) + ' (L = ' + this.L.join(', ') + ') → Sum = ' + (this.M / 2) + ' + ' +
				(p.sum - this.M / 2) + ' = ' + p.sum + (p.taken ? ' ≥ 0' : ' < 0') + ' → predict ' + (p.taken ? 'T' : 'NT');
			const a = [];
			for (let i = 0; i < this.M; i++) if (p.alias[i]) a.push('T' + i + ' ← ' + brName(p.prev[i]));
			if (a.length) s += ' (entries last trained by another branch: ' + a.slice(0, 4).join(', ') + (a.length > 4 ? ', …' : '') + ')';
			return { text: s, warn: false };
		}

		describeUpdate(u) {
			const p = u.p;
			let s;
			if (u.wrong) s = 'mispredicted → all ' + this.M + ' counters trained toward ' + (u.taken ? 'T' : 'NT');
			else if (u.low) s = 'correct but |Sum| = ' + Math.abs(p.sum) + ' ≤ θ = ' + u.theta + ' → all counters trained';
			else s = 'correct and |Sum| = ' + Math.abs(p.sum) + ' > θ = ' + u.theta + ' → no update';
			if (u.go) s += ' (now ' + this.cList(u.after.map(function (v, i) { return this.T[i].signed(v); }, this)) + ')';
			if (u.thetaAfter !== u.theta) s += ' · threshold θ ' + u.theta + ' → ' + u.thetaAfter;
			if (u.histWritten) s += ' · GHR ← ' + (u.taken ? 1 : 0) + (u.repaired ? ' (repaired)' : '');
			const d = [];
			for (let i = 0; i < this.M; i++) if (u.inter[i] === 'destructive') d.push('T' + i);
			if (d.length) s += ' · aliasing in ' + d.join(', ') + ' flipped the sum (destructive interference)';
			return { text: s, warn: d.length > 0 && u.wrong };
		}

		warnings(p) {
			let worst = -1;
			for (let i = 0; i < this.M; i++) if (p.alias[i] && (worst < 0 || this.T[i].level > this.T[worst].level)) worst = i;
			return worst >= 0 ? ['T' + worst + ' entry ' + hex(p.ix[worst], this.lt) + ' last trained by ' + brName(p.prev[worst])] : [];
		}

		figure(view) {
			const p = view.read, u = view.upd;
			const rOn = !!(p && view.readNow), uOn = !!(u && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const fl = function (seq) { return p ? { on: rOn, dim: !rOn, seq: seq } : { dim: true }; };
			const M = this.M, X0 = 150, X1 = 650, slot = (X1 - X0) / M, w = Math.min(46, slot - 12);
			const PY = 76, HY = 104, TOP = 160, RH = 26, GAP = 28, AY = 336;
			let s = S.figLabel(10, 8, 'GEHL');

			s += S.t(16, PY + 4, 'PC', 'tx');
			s += S.reg({ x: 16, y: HY - 12, w: 120, h: 24, txt: p ? p.recent : this.hist.text(Math.min(16, this.L[M - 1])), on: rOn, seq: 0,
				write: u && u.histWritten, seqWrite: 4, readDim: !rOn, writeDim: !uOn });
			s += S.t(16, HY + 30, 'Global history', 'tx sm');
			const cxs = [];
			for (let i = 0; i < M; i++) cxs.push(Math.round(X0 + i * slot + slot / 2));
			s += S.wire([[40, PY], [cxs[M - 1] - 8, PY]], 'rd', Object.assign(fl(0), { arrow: false }));
			s += S.wire([[136, HY], [cxs[M - 1] + 8, HY]], 'rd', Object.assign(fl(0), { arrow: false }));

			const sameIdx = function (i) { return p && u && u.p.ix[i] === p.ix[i]; };
			for (let i = 0; i < M; i++) {
				const cx = cxs[i], x = cx - w / 2;
				if (i === 0) {
					s += S.wire([[cx, PY], [cx, TOP - 2]], 'rd', fl(1));
					s += S.dot(cx, PY, rOn ? 'rd' : 'ink');
				} else {
					s += S.wire([[cx - 8, PY], [cx - 8, 120]], 'rd', fl(1));
					s += S.wire([[cx + 8, HY], [cx + 8, 120]], 'rd', fl(1));
					if (i < M - 1) { s += S.dot(cx - 8, PY, rOn ? 'rd' : 'ink'); s += S.dot(cx + 8, HY, rOn ? 'rd' : 'ink'); }
					s += S.hashBox(x, 122, w, 16, 'H');
					s += S.wire([[cx, 138], [cx, TOP - 2]], 'rd', fl(1));
				}
				const wrote = u && u.go;
				const col = S.column({
					x: x, y: TOP, w: w, rh: RH, gap: GAP, level: this.T[i].level,
					read: p ? 1 : -1, readTxt: p ? sgn(p.c[i]) : null, seqRead: 2,
					write: wrote ? (sameIdx(i) ? 1 : 2) : -1, writeTxt: wrote && w >= 30 ? sgn(this.T[i].signed(u.after[i])) : null,
					seqWrite: 4, readDim: !rOn, writeDim: !uOn
				});
				s += col.svg;
				if (p && p.alias[i] && this.T[i].level >= 2) s += S.t(cx - 6, TOP - 4, '⚠', 'warn-glyph');
				s += S.t(x, col.bottom + 14, 'T' + i, 'tx sm');
				if (slot >= 50) s += S.t(x, col.bottom + 27, 'L=' + this.L[i], 'dim');
				s += S.wire([[cx, col.bottom], [cx, AY - 2]], 'rd', fl(3));
				if (wrote) s += S.wire([[x + w - 5, AY - 6], [x + w - 5, col.bottom + 2]], 'up', { on: uOn, dim: !uOn, seq: 4 });
			}

			// Adder and sign.
			s += S.fnBox(X0, AY, X1 - X0, 26, ['Sum = M/2 + Σ C(i)'], p && rOn ? 'op-on' : '');
			s += S.wire([[400, AY + 26], [400, AY + 50]], 'rd', fl(4));
			if (p) s += S.val(408, AY + 46, 'Sum = ' + p.sum + (p.taken ? ' ≥ 0 → taken' : ' < 0 → not taken'), rk);
			s += S.t(16, AY + 14, 'θ = ' + this.theta, 'mono');
			if (u) {
				const why = u.wrong ? 'update: mispredicted' : u.low ? 'update: |Sum| ≤ θ' : 'no update: confident';
				s += S.val(16, AY + 46, why + (u.thetaAfter !== u.theta ? ' · θ ' + u.theta + '→' + u.thetaAfter : ''), uk);
			}
			let worst = 0, tot = 0;
			this.T.forEach(function (t, i) {
				tot += t.occupancy;
				if (t.destructive / (t.resolves || 1) > this.T[worst].destructive / (this.T[worst].resolves || 1)) worst = i;
			}, this);
			s += S.t(16, AY + 70, 'tables ' + Math.round((100 * tot) / M) + '% used on average · most interference in T' + worst + ': ' + this.T[worst].describe(), 'dim');
			s += callouts(view, this);
			return S.svg(680, AY + 78, s, 'GEHL predictor');
		}
	}

	const ALPHAS = [1.5, 2, 2.5, 3];

	const GEHL_DEF = {
		id: 'GEHL',
		name: 'GEHL',
		title: 'Geometric history lengths, summed signed counters',
		group: 'III-E · Geometric history lengths: GEHL (Table IV), TAGE (Fig. 9)',
		figure: 'Table IV',
		knobs: [
			{ id: 'M', label: 'M · tables', type: 'int', min: 4, max: 12, def: 8, help: 'Number of tables T0..T(M-1); T0 uses no history.' },
			{ id: 'lt', label: 'entries per table (log2)', type: 'int', min: 4, max: 14, def: 10, help: 'Each table has 2^value counters.' },
			{ id: 'L1', label: 'L(1) · shortest history', type: 'int', min: 1, max: 8, def: 2, help: 'History length of T1.' },
			{ id: 'alpha', label: 'α · length ratio', type: 'choice', options: ALPHAS, def: 2, help: 'L(i) = floor(α^(i-1) · L(1) + 0.5).' },
			{ id: 'cb', label: 'counter bits', type: 'int', min: 3, max: 6, def: 4, help: 'Width of each signed counter.' },
			{ id: 'adapt', label: 'adaptive θ', type: 'choice', options: [{ v: 'on', label: 'on (O-GEHL)' }, { v: 'off', label: 'off (θ = M)' }], def: 'on',
				help: 'Adapt the update threshold so updates on mispredictions and on low-confidence hits stay balanced.' }
		],
		validate: function (k) {
			const L = lengths(k);
			return L[k.M - 1] > MAX_HIST ? 'the longest history would be ' + L[k.M - 1].toLocaleString() + ' bits (limit ' + MAX_HIST + ')' : null;
		},
		create: function (k, opts) { return new GEHL(k, opts); },
		about: 'Seznec\'s GEHL reads one signed counter from each of M tables, whose history lengths grow geometrically, and adds them up. ' +
			'Most of the storage serves short histories, yet one table can still see a correlation 2^(M-2)·L(1) branches back. ' +
			'Counters are only trained on a misprediction or a low-confidence sum, which keeps them from saturating on easy branches.'
	};

	BP.gehl = { GEHL: GEHL_DEF, MAX_HIST };

})(window.BP = window.BP || {});
