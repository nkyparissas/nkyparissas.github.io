/* ==========================================================================
   /bp: Michaud et al.'s skewed predictor, gskew (survey Section III-C).

   Three tag-less banks of counters are indexed by three different skewing
   functions of the same (address, history) vector, and a majority vote
   decides. Two vectors that collide in one bank do not collide in the
   other two (with these functions this is exact unless i = 2 mod 3, where
   three difference patterns are the exception), so one aliased bank is
   simply outvoted.

   The skewing functions are those of the original paper: with the vector
   split into two n-bit halves V1 (address) and V2 (history), and
   H(y_n..y_1) = (y_n XOR y_1, y_n, ..., y_2),
     f0 = H(V1) ^ H'(V2) ^ V2,  f1 = H(V1) ^ H'(V2) ^ V1,  f2 = H'(V1) ^ H(V2) ^ V2
   where H' is the inverse of H.

   Interference is judged on the vote: aliasing in a bank was destructive
   only when the bank's vote from the branch's own counter would have turned
   a wrong majority into a right one.

   Update: "total" trains every bank; "partial" leaves a bank that voted
   wrong alone when the vote was right, so it can keep serving the other
   branch it was trained by (the paper finds this better).

   The survey has no figure for it; the panel follows Fig. 9's notation.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, CounterTable, GlobalHistory, hex, binShort, pcField, brName } = BP.base;
	const { callouts } = BP.figure;
	const S = BP.svg;

	const NB = 3;

	class Skewed extends Predictor {
		constructor(knobs, opts) {
			super(knobs, opts);
			this.n = knobs.i;
			this.h = knobs.h;
			this.mask = (1 << knobs.i) - 1;
			this.partial = knobs.update === 'partial';
			this.ghr = new GlobalHistory(Math.max(1, knobs.h), 'GHR');
			this.banks = [];
			for (let b = 0; b < NB; b++) this.banks.push(new CounterTable(1 << knobs.i, knobs.n, 'Bank ' + b));
			this.latency = 1;
		}

		tables() { return this.banks; }
		storageBits() { return NB * this.banks[0].size * this.k.n + this.h; }

		H(y) { const n = this.n; return (y >>> 1) | ((((y >>> (n - 1)) ^ y) & 1) << (n - 1)); }
		Hinv(z) { const n = this.n; return ((z << 1) & this.mask) | (((z >>> (n - 1)) ^ (z >>> (n - 2))) & 1); }

		// Bank indices for one branch address and history.
		indices(pc, hist) {
			const v1 = (pc >>> 2) & this.mask, v2 = hist & this.mask;
			const a = this.H(v1) ^ this.Hinv(v2);
			return [a ^ v2, a ^ v1, this.Hinv(v1) ^ this.H(v2) ^ v2];
		}

		lookup(pc, br) {
			const hist = this.h ? this.ghr.v & ((1 << this.h) - 1) : 0;
			const ix = this.indices(pc, hist);
			const p = { hist: hist, addr: (pc >>> 2) & this.mask, ix: ix, ctr: [], votes: [], priv: [], alias: [], prev: [] };
			let nT = 0;
			for (let b = 0; b < NB; b++) {
				const rd = this.banks[b].read(ix[b], br);
				p.ctr.push(rd.v);
				p.votes.push(rd.taken);
				p.priv.push(rd.privTaken);
				p.alias.push(rd.alias);
				p.prev.push(rd.prev);
				if (rd.taken) nT++;
			}
			p.taken = nT * 2 > NB;
			return p;
		}

		shiftHistory(p, bit, undo) {
			p.newHist = this.ghr.shift(bit, undo, p.seq) & ((1 << this.h) - 1);
		}

		train(p, taken, mis) {
			const right = p.taken === taken;
			const u = { before: p.ctr.slice(), after: [], trained: [], inter: [], histWritten: !this.spec || mis, newHist: p.newHist };
			for (let b = 0; b < NB; b++) {
				// Aliasing in one bank only matters if it swung the vote: compare with the vote this bank
				// would have cast from the branch's own (private) counter.
				const v = p.votes.slice();
				v[b] = p.priv[b];
				const alt = v.filter(Boolean).length * 2 > NB;
				u.inter.push(this.banks[b].noteOutcome(p.taken, alt, taken));
				const go = !this.partial || !right || p.votes[b] === taken;
				u.trained.push(go);
				u.after.push(go ? this.banks[b].train(p.ix[b], taken, p.br) : p.ctr[b]);
			}
			return u;
		}

		fmtBanks(arr, f) { return arr.map(f).join(', '); }

		describePredict(p) {
			const self = this;
			let s = 'f0, f1, f2 of ' + pcField(2, this.n) + ' = ' + hex(p.addr, this.n) + ' and GHR ' + (this.h ? binShort(p.hist, this.h, 16) : '—') +
				' → banks [' + this.fmtBanks(p.ix, function (i) { return hex(i, self.n); }) + '] = ' +
				this.fmtBanks(p.ctr, function (v) { return self.banks[0].fmt(v); }) + ' → votes ' +
				this.fmtBanks(p.votes, function (v) { return v ? 'T' : 'NT'; }) + ' → predict ' + (p.taken ? 'T' : 'NT');
			const a = [];
			for (let b = 0; b < NB; b++) if (p.alias[b]) a.push('bank ' + b + ' last trained by ' + brName(p.prev[b]));
			if (a.length) s += ' (' + a.join('; ') + ')';
			return { text: s, warn: false };
		}

		describeUpdate(u) {
			const p = u.p, self = this;
			let s = 'banks ' + this.fmtBanks([0, 1, 2], function (b) { return self.banks[b].fmt(u.before[b]) + '→' + self.banks[b].fmt(u.after[b]); });
			const skipped = [];
			for (let b = 0; b < NB; b++) if (!u.trained[b]) skipped.push(b);
			if (skipped.length) s += ' · partial update: bank ' + skipped.join(', ') + ' voted wrong but was outvoted, so it is left as it is';
			else if (this.partial && p.taken !== u.taken) s += ' · vote was wrong: every bank trained';
			if (u.histWritten && this.h) s += ' · GHR ← ' + (u.taken ? 1 : 0) + (u.repaired ? ' (repaired)' : '');
			let warn = false;
			for (let b = 0; b < NB; b++) {
				if (u.inter[b] === 'destructive') {
					s += ' · bank ' + b + ': aliasing with ' + brName(p.prev[b]) + ' swung the vote (destructive interference)';
					warn = true;
				}
			}
			return { text: s, warn: warn };
		}

		warnings(p) {
			const w = [];
			for (let b = 0; b < NB; b++) {
				if (p.alias[b] && p.votes[b] !== p.taken) w.push('bank ' + b + ' (last trained by ' + brName(p.prev[b]) + ') dissents and is outvoted');
			}
			if (!w.length) for (let b = 0; b < NB; b++) if (p.alias[b]) { w.push('bank ' + b + ' entry last trained by ' + brName(p.prev[b])); break; }
			return w;
		}

		figure(view) {
			const p = view.read, u = view.upd;
			const rOn = !!(p && view.readNow), uOn = !!(u && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const fl = function (seq) { return p ? { on: rOn, dim: !rOn, seq: seq } : { dim: true }; };
			const CX = [230, 360, 490], TOP = 176, RH = 28, GAP = 34;
			const AY = 90, HY = 116;   // address and history buses
			let s = S.figLabel(10, 8, 'gskew');

			// Inputs.
			s += S.t(16, AY - 8, 'Branch address', 'tx');
			s += S.wire([[16, AY], [CX[2] - 12, AY]], 'rd', Object.assign(fl(0), { arrow: false }));
			if (p) s += S.val(130, AY - 8, pcField(2, this.n) + ' = ' + hex(p.addr, this.n), rk);
			s += S.reg({ x: 16, y: HY - 13, w: 110, h: 26, txt: this.h ? binShort(p ? p.hist : this.ghr.v & ((1 << this.h) - 1), this.h, 12) : '—', on: rOn, seq: 0,
				write: u && u.histWritten, seqWrite: 4, readDim: !rOn, writeDim: !uOn });
			s += S.t(16, HY + 30, 'Global history', 'tx sm');
			s += S.wire([[126, HY], [CX[2] + 12, HY]], 'rd', Object.assign(fl(0), { arrow: false }));

			const sameIdx = function (b) { return p && u && u.p.ix[b] === p.ix[b]; };
			for (let b = 0; b < NB; b++) {
				const cx = CX[b];
				s += S.wire([[cx - 12, AY], [cx - 12, 134]], 'rd', fl(1));
				s += S.wire([[cx + 12, HY], [cx + 12, 134]], 'rd', fl(1));
				if (b < NB - 1) { s += S.dot(cx - 12, AY, rOn ? 'rd' : 'ink'); s += S.dot(cx + 12, HY, rOn ? 'rd' : 'ink'); }
				s += S.hashBox(cx - 30, 136, 60, 20, 'f' + b);
				s += S.wire([[cx, 156], [cx, TOP - 2]], 'rd', fl(1));
				const wrote = u && u.trained[b];
				const col = S.column({
					x: cx - 30, y: TOP, w: 60, rh: RH, gap: GAP, level: this.banks[b].level,
					read: p ? 1 : -1, readTxt: p ? this.banks[b].fmt(p.ctr[b]) : null, seqRead: 2,
					write: wrote ? (sameIdx(b) ? 1 : 2) : -1, writeTxt: wrote ? '→' + this.banks[b].fmt(u.after[b]) : null,
					seqWrite: 4, readDim: !rOn, writeDim: !uOn
				});
				s += col.svg;
				if (p) s += S.val(cx + 34, TOP - 6, hex(p.ix[b], this.n), rk);
				if (p && p.alias[b]) s += S.t(cx - 48, col.rowY(1) + 5, '⚠', 'warn-glyph');
				s += S.tEnd(cx - 36, col.rowY(0) + 4, 'bank ' + b, 'tx sm');
				s += S.wire([[cx, col.bottom], [cx, 342]], 'rd', fl(3));
				if (p) s += S.val(cx + 6, 338, p.votes[b] ? 'T' : 'NT', rk);
				if (u) {
					const wy = col.rowY(sameIdx(b) ? 1 : 2);
					if (wrote) {
						s += S.wire([[cx + 48, 342], [cx + 48, wy], [cx + 32, wy]], 'up', { on: uOn, dim: !uOn, seq: 4 });
					} else {
						s += S.val(cx + 36, col.rowY(2) + 4, 'kept', uk);
					}
				}
			}

			// Majority vote.
			s += S.fnBox(CX[0] - 30, 344, CX[2] - CX[0] + 60, 26, ['majority vote'], p && rOn ? 'op-on' : '');
			s += S.wire([[CX[2] + 30, 357], [CX[2] + 66, 357]], 'rd', fl(4));
			if (p) s += S.val(CX[2] + 70, 361, '→ ' + (p.taken ? 'taken' : 'not taken'), rk);
			if (u) s += S.val(CX[2] + 70, 341, this.partial ? 'partial update' : 'total update', uk);
			const pct = function (x) { return (Math.round(x * 1000) / 10) + '%'; };
			const per = function (f) { return this.banks.map(f).join(' / '); }.bind(this);
			s += S.t(16, 392, 'banks 0 / 1 / 2:  ' + per(function (t) { return pct(t.occupancy); }) + ' used  ·  ' +
				per(function (t) { return pct(t.destructive / (t.resolves || 1)); }) + ' destructive  ·  ' +
				per(function (t) { return pct(t.constructive / (t.resolves || 1)); }) + ' constructive', 'dim');
			s += callouts(view, this);
			return S.svg(680, 400, s, 'Skewed predictor');
		}
	}

	const GSKEW = {
		id: 'gskew',
		name: 'gskew',
		title: 'Three skewed banks and a majority vote',
		group: 'III-C · Multiple indexing functions (Michaud et al.)',
		figure: 'Sec. III-C',
		knobs: [
			{ id: 'i', label: 'i · bank index bits', type: 'int', min: 2, max: 16, def: 9, help: 'Each of the three banks has 2^i counters.' },
			{ id: 'h', label: 'h · history bits', type: 'int', min: 0, max: 16, def: 9, help: 'Global history length (at most i): V2 in the skewing functions.' },
			{ id: 'n', label: 'N · counter bits', type: 'int', min: 1, max: 4, def: 2, help: 'Width of each counter.' },
			{ id: 'update', label: 'update policy', type: 'choice', options: [{ v: 'partial', label: 'partial' }, { v: 'total', label: 'total' }], def: 'partial',
				help: 'Total: train all three banks. Partial: when the vote was right, leave a bank that voted wrong alone.' }
		],
		validate: function (k) { return k.h > k.i ? 'the history cannot be longer than a bank index (h ≤ i)' : null; },
		create: function (k, opts) { return new Skewed(k, opts); },
		about: 'Michaud et al. treat aliasing like cache conflicts and borrow the skewed-associative cache: three tag-less banks indexed by ' +
			'different hash functions of the same address and history, then a majority vote. A pair of branches that collide in one bank ' +
			'do not collide in the others, so the vote hides most conflict aliasing; three banks of 2^i match one bank about twice as large.'
	};

	BP.skewed = { GSKEW };

})(window.BP = window.BP || {});
