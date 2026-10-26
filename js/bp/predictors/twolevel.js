/* ==========================================================================
   /bp: Yeh and Patt's two-level predictors, [G/P/S]A[g/p/s] (survey Fig. 4,
   Table II, Section III-A).

   Level 1 (history):  G one global BHR; P a per-address BHR table indexed by
                       Addr(B); S a per-set BHR table indexed by SetH(B), the
                       block of code the branch lives in.
   Level 2 (pattern):  g one PHT; p one PHT per address, picked by Addr(B);
                       s one PHT per set, picked by SetP(B) (low address bits).
   The k history bits index into the chosen PHT, whose entry is an N-bit
   saturating counter.

   P and S read two tables in series (BHR, then PHT), so they are charged two
   cycles of lookup latency; G reads a register and a table, one cycle.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, CounterTable, HistoryTable, GlobalHistory, log2, hex, bin, binShort, pcField, brName, interferenceText } = BP.base;
	const { callouts } = BP.figure;
	const S = BP.svg;

	const MAX_PHT = 1 << 22;
	const DEF_K = { GAg: 10, GAs: 8, GAp: 8, PAg: 8, PAs: 6, PAp: 6, SAg: 8, SAs: 6, SAp: 6 };

	const TITLE = {
		GAg: 'Global history, one global PHT',
		GAs: 'Global history, per-set PHTs',
		GAp: 'Global history, per-address PHTs',
		PAg: 'Per-address history, one global PHT',
		PAs: 'Per-address history, per-set PHTs',
		PAp: 'Per-address history, per-address PHTs',
		SAg: 'Per-set history, one global PHT',
		SAs: 'Per-set history, per-set PHTs',
		SAp: 'Per-set history, per-address PHTs'
	};

	function knobsFor(v) {
		const H = v[0], L = v[2];
		const ks = [];
		if (H === 'P') {
			ks.push({ id: 'rows', label: 'BHR table entries', type: 'pow2', min: 16, max: 4096, def: 256,
				help: 'Number of history registers in the per-address BHR table.' });
			ks.push({ id: 'ways', label: 'BHR table ways', type: 'choice', options: [1, 2, 4, 8], def: 1,
				help: '1 = direct-mapped and tag-less (rows are shared). More = set-associative with tags and LRU.' });
		}
		if (H === 'S') {
			ks.push({ id: 'setSize', label: 'set = code block of', type: 'pow2', min: 64, max: 4096, def: 1024, unit: 'B',
				help: 'Branches in the same aligned block share a set (the paper uses 1 KB, i.e. 256 instructions).' });
			ks.push({ id: 'i', label: 'i · SetH(B) bits', type: 'int', min: 1, max: 10, def: 4,
				help: 'Bits of the block number that index the per-set BHR table (2^i registers).' });
		}
		ks.push({ id: 'k', label: 'k · history bits', type: 'int', min: 1, max: H === 'G' ? 18 : 14, def: DEF_K[v],
			help: 'Length of each branch history register; the PHT has 2^k entries.' });
		if (L === 's') {
			ks.push({ id: 'm', label: 'm · SetP(B) bits', type: 'int', min: 1, max: 10, def: 4,
				help: 'Low address bits that pick one of 2^m per-set PHTs.' });
		}
		if (L === 'p') {
			ks.push({ id: 'ap', label: 'a · Addr(B) bits for PHT', type: 'int', min: 1, max: 10, def: 6,
				help: 'Low address bits that pick one of 2^a per-address PHTs.' });
		}
		ks.push({ id: 'n', label: 'N · counter bits', type: 'int', min: 1, max: 4, def: 2,
			help: 'Width of each saturating counter in the PHT (1 = last outcome, 2 = the classic 2-bit counter).' });
		return ks;
	}

	function selBits(v, k) { return v[2] === 'g' ? 0 : v[2] === 's' ? k.m : k.ap; }

	class TwoLevel extends Predictor {
		constructor(v, knobs, opts) {
			super(knobs, opts);
			this.v = v;
			this.H = v[0];
			this.L = v[2];
			this.kb = knobs.k;
			if (this.H === 'G') this.ghr = new GlobalHistory(knobs.k, 'Global BHR');
			if (this.H === 'P') {
				this.sets = knobs.rows / knobs.ways;
				this.idxBits = log2(this.sets);
				this.bht = new HistoryTable(this.sets, knobs.ways, knobs.k, 'Per-addr BHR table');
			}
			if (this.H === 'S') {
				this.setShift = log2(knobs.setSize);
				this.idxBits = knobs.i;
				this.bht = new HistoryTable(1 << knobs.i, 1, knobs.k, 'Per-set BHR table');
			}
			this.sb = selBits(v, knobs);
			this.nPHT = 1 << this.sb;
			this.pht = new CounterTable(this.nPHT << knobs.k, knobs.n,
				this.L === 'g' ? 'Global PHT' : this.L === 's' ? 'Per-set PHTs' : 'Per-addr PHTs');
			this.latency = this.H === 'G' ? 1 : 2;
		}

		tables() { return this.bht ? [this.bht, this.pht] : [this.pht]; }

		storageBits() {
			let b = this.pht.size * this.k.n;
			if (this.H === 'G') b += this.kb;
			if (this.H === 'P') {
				const tagBits = this.k.ways > 1 ? Math.max(0, 30 - this.idxBits) : 0;
				b += this.k.rows * (this.kb + tagBits);
			}
			if (this.H === 'S') b += (1 << this.k.i) * this.kb;
			return b;
		}

		l1Index(pc) {
			if (this.H === 'P') {
				const word = pc >>> 2;
				return { set: word & (this.sets - 1), tag: word >>> this.idxBits };
			}
			const block = pc >>> this.setShift;
			return { set: block & ((1 << this.k.i) - 1), tag: 0, block: block };
		}

		lookup(pc, br) {
			const word = pc >>> 2;
			let hist, l1 = null;
			if (this.H === 'G') {
				hist = this.ghr.v;
			} else {
				const ix = this.l1Index(pc);
				// Per-set rows are meant to be shared by every branch of a block; only another block is aliasing.
				const key = this.H === 'S' ? ix.block : br;
				l1 = this.bht.lookup(ix.set, ix.tag, br, key);
				l1.tagv = ix.tag;
				l1.key = key;
				hist = l1.hist;
			}
			const sel = this.sb ? (word & (this.nPHT - 1)) : 0;
			const idx = (sel << this.kb) | hist;
			const rd = this.pht.read(idx, br);
			return { taken: rd.taken, hist: hist, sel: sel, idx: idx, ctr: rd.v, phtAlias: rd.alias, phtPrev: rd.prev, phtPriv: rd.privTaken, l1: l1 };
		}

		shiftHistory(p, bit, undo) {
			if (this.H === 'G') {
				p.newHist = this.ghr.shift(bit, undo, p.seq);
			} else {
				const r = this.bht.shiftIn(p.l1.set, p.l1.tagv, bit, p.br, undo, p.seq, p.l1.key);
				p.newHist = r.hist;
			}
		}

		train(p, taken, mis) {
			const before = this.pht.ctr[p.idx];
			const after = this.pht.train(p.idx, taken, p.br);
			const inter = this.pht.noteOutcome(p.taken, p.phtPriv, taken);
			if (this.bht) this.bht.noteResolve(p.l1.alias, mis);
			return { idx: p.idx, sel: p.sel, before: before, after: after, histWritten: !this.spec || mis, newHist: p.newHist, inter: inter };
		}

		/* ---------------------------------------------------------- log text */

		l1Text(p) {
			const k = this.kb;
			if (this.H === 'G') return 'Global BHR = ' + binShort(p.hist, k, 18);
			const l1 = p.l1;
			const field = this.H === 'P' ? pcField(2, this.idxBits) : pcField(this.setShift, this.idxBits);
			const what = this.H === 'P' ? 'Addr(B) = ' : 'SetH(B) = ';
			let s = what + field + ' = ' + hex(l1.set, this.idxBits);
			if (this.bht.tagged) {
				s += ', tag ' + hex(l1.tagv, 8) + ': ';
				if (l1.hit) s += 'hit';
				else if (l1.evict) s += 'miss, set ' + hex(l1.set, this.idxBits) + ' was full (' + this.k.ways + ' ways), evicting ' + brName(l1.prev) + '\'s history';
				else s += 'miss, allocating a fresh history';
			}
			s += ' → BHR ' + hex(l1.set, this.idxBits) + ' = ' + binShort(p.hist, k, 18);
			if (!this.bht.tagged && l1.alias) s += ' (last written by ' + this.ownerName(l1.prev) + ': aliasing)';
			return s;
		}

		// Owner of a BHR row: a branch (per-address) or a code block (per-set).
		ownerName(o) {
			return this.H === 'S' ? 'block ' + hex(o << this.setShift, 16) : brName(o);
		}

		phtName(sel) {
			if (this.L === 'g') return 'PHT';
			return 'PHT' + sel;
		}

		describePredict(p) {
			let s = this.l1Text(p);
			if (this.L !== 'g') {
				const what = this.L === 's' ? 'SetP(B) = ' : 'Addr(B) = ';
				s += ' · ' + what + pcField(2, this.sb) + ' = ' + p.sel + ' → PHT' + p.sel + ' of ' + this.nPHT;
			}
			s += ' → ' + this.phtName(p.sel) + '[' + bin(p.hist, this.kb) + '] = ' + this.pht.fmt(p.ctr);
			if (p.phtAlias) s += ' (last trained by ' + brName(p.phtPrev) + ')';
			s += ' → predict ' + (p.taken ? 'T' : 'NT');
			const warn = !!(p.l1 && p.l1.alias);
			return { text: s, warn: warn };
		}

		describeUpdate(u) {
			const p = u.p;
			let s = this.phtName(p.sel) + '[' + bin(p.hist, this.kb) + '] ' + this.pht.fmt(u.before) + '→' + this.pht.fmt(u.after);
			if (u.histWritten) {
				s += ' · ' + (this.H === 'G' ? 'Global BHR' : 'BHR ' + hex(p.l1.set, this.idxBits)) + ' ← ' +
					(u.taken ? 1 : 0) + ' = ' + binShort(u.newHist, this.kb, 18);
				if (u.repaired) s += ' (speculative history repaired)';
			}
			s += interferenceText(u.inter, p.br, p.phtPrev, u.taken);
			if (u.mis && p.l1 && p.l1.alias) s += ' · history was polluted by ' + this.ownerName(p.l1.prev);
			return { text: s, warn: u.inter === 'destructive' || (u.mis && !!(p.l1 && p.l1.alias)) };
		}

		/* ------------------------------------------------------------ figure */

		figure(view) {
			const p = view.read, u = view.upd;
			const fl = function (now) { return now ? { on: true } : { dim: true }; };
			const rOn = !!(p && view.readNow), uOn = !!(u && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const TOP = 120, RH = 30, GAP = 40;
			const k = this.kb;
			let s = S.figLabel(10, 8, this.v);
			let x1, y1 = TOP + RH + RH / 2;   // level-1 output: BHR read row (row 1)
			const pr = TOP + 2 * RH + RH / 2; // PHT read row (row 2)

			// Level 1.
			if (this.H === 'G') {
				s += S.tMid(115, TOP + 20, 'Global BHR', 'tx');
				const hv = p ? p.hist : this.ghr.v;
				s += S.reg({ x: 40, y: y1 - 16, w: 150, h: 32, txt: binShort(hv, k, 16), on: rOn, seq: 0,
					write: u && u.histWritten, seqWrite: 4, readDim: !rOn, writeDim: !uOn });
				x1 = 190;
				if (u && u.histWritten) {
					s += S.wire([[115, 330], [115, y1 + 18]], 'up', { on: uOn, dim: !uOn, seq: 4 });
					s += S.val(121, 322, 'shift in ' + (u.taken ? 1 : 0), uk);
				}
			} else {
				const isP = this.H === 'P';
				const writeRow = u && u.histWritten ? (p && p.l1.slot === u.p.l1.slot ? 1 : 2) : -1;
				const col = S.column({
					x: 150, y: TOP, w: 100, rh: RH, gap: GAP, level: this.bht.level,
					title: [isP ? 'Per-addr' : 'Per-set', 'BHR table' + (this.bht.tagged ? ' (' + this.k.ways + '-way)' : '')],
					read: p ? 1 : -1, readTxt: p ? binShort(p.hist, k, 9) : null, seqRead: 1,
					write: writeRow, writeTxt: u ? binShort(u.newHist, k, 9) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
				});
				s += col.svg;
				s += S.t(16, y1 + 5, isP ? 'Addr(B)' : 'SetH(B)', 'tx');
				s += S.wire([[80, y1], [148, y1]], 'rd', Object.assign({ seq: 0 }, p ? fl(rOn) : { dim: true }));
				s += S.tick(112, y1, 'h', isP ? 'a' : 'i');
				if (p) s += S.val(16, y1 + 44, (isP ? pcField(2, this.idxBits) : pcField(this.setShift, this.idxBits)) + ' = ' + hex(p.l1.set, this.idxBits), rk);
				if (p && p.l1.alias) s += S.t(126, y1 - 8, '⚠', 'warn-glyph');
				x1 = 250;
				if (u && u.histWritten) {
					s += S.wire([[200, 330], [200, col.bottom + 2]], 'up', { on: uOn, dim: !uOn, seq: 4 });
					s += S.val(206, 322, 'shift in ' + (u.taken ? 1 : 0), uk);
				}
				s += S.t(150, 352, this.bht.describe(), 'dim');
			}

			// k-bit history wire to level 2.
			const kWire = [[x1, y1], [330, y1], [330, pr]];
			let outX;
			const ctrTxt = p ? this.pht.fmt(p.ctr) : null;
			const sameIdx = p && u && u.idx === p.idx;
			if (this.L === 'g') {
				const col = S.column({
					x: 400, y: TOP, w: 70, rh: RH, gap: GAP, level: this.pht.level, title: ['Global PHT'],
					read: p ? 2 : -1, readTxt: ctrTxt, seqRead: 2,
					write: u ? (sameIdx ? 2 : 1) : -1, writeTxt: u ? '→' + this.pht.fmt(u.after) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
				});
				s += col.svg;
				s += S.wire(kWire.concat([[398, pr]]), 'rd', Object.assign({ seq: 1 }, p ? fl(rOn) : { dim: true }));
				s += S.tick(364, pr, 'h', 'k');
				outX = 470;
				if (u) {
					s += S.wire([[435, 330], [435, col.bottom + 2]], 'up', { on: uOn, dim: !uOn, seq: 4 });
					s += S.val(441, 322, 'train ' + this.pht.fmt(u.before) + '→' + this.pht.fmt(u.after), uk);
				}
				s += S.t(400, 352, this.pht.describe(), 'dim');
			} else {
				const isSet = this.L === 's';
				const sameSel = p && u && u.sel === p.sel;
				const b = S.bank({
					x: 360, y: TOP - 10, colW: 44, colGap: 12, rh: RH, gap: GAP, level: this.pht.level,
					readCol: p ? 1 : -1, readRow: 2, readTxt: ctrTxt, seqRead: 2,
					writeCol: u ? (sameSel ? 1 : 2) : -1, writeRow: sameIdx ? 2 : 1,
					writeTxt: u ? '→' + this.pht.fmt(u.after) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn,
					title: isSet ? 'Per-set PHTs' : 'Per-addr PHTs', titleX: 466
				});
				s += b.svg;
				const cx = b.colCx(1);
				s += S.t(352, TOP - 30, isSet ? 'SetP(B)' : 'Addr(B)', 'tx');
				s += S.wire([[cx - 34, TOP - 34], [cx, TOP - 34], [cx, TOP]], 'rd', Object.assign({ seq: 1 }, p ? fl(rOn) : { dim: true }));
				s += S.tick(cx - 14, TOP - 34, 'h', isSet ? 'm' : 'a');
				if (p) s += S.val(352, TOP - 52, pcField(2, this.sb) + ' = ' + p.sel + ' (PHT ' + p.sel + ' of ' + this.nPHT + ')', rk);
				s += S.wire(kWire.concat([[358, pr]]), 'rd', Object.assign({ seq: 1 }, p ? fl(rOn) : { dim: true }));
				s += S.tick(290, y1, 'h', 'k');
				outX = b.right;
				if (u) {
					const ux = sameSel ? cx : b.colCx(2);
					s += S.wire([[ux, 330], [ux, b.bottom + 2]], 'up', { on: uOn, dim: !uOn, seq: 4 });
					s += S.val(ux + 6, 322, 'train ' + this.pht.fmt(u.before) + '→' + this.pht.fmt(u.after), uk);
				}
				s += S.t(360, 352, this.pht.describe(), 'dim');
			}
			if (p) s += S.val(x1 + 8, y1 - 8, binShort(p.hist, k, 10), rk);

			// Prediction out.
			s += S.wire([[outX, pr], [outX + 44, pr]], 'rd', Object.assign({ seq: 3 }, p ? fl(rOn) : { dim: true }));
			if (p) {
				s += S.val(outX + 50, pr - 4, 'ctr ' + ctrTxt, rk);
				s += S.val(outX + 50, pr + 13, '→ ' + (p.taken ? 'taken' : 'not taken'), rk);
			}

			s += callouts(view, this);
			return S.svg(680, 362, s, this.v + ' predictor');
		}
	}

	TwoLevel.prototype.warnings = function (p) {
		const w = [];
		if (p.l1 && p.l1.alias) {
			w.push(this.bht.tagged
				? 'set ' + hex(p.l1.set, this.idxBits) + ' was full: ' + brName(p.l1.prev) + '\'s history evicted'
				: 'BHR ' + hex(p.l1.set, this.idxBits) + ' last written by ' + this.ownerName(p.l1.prev) + ': aliasing');
		} else if (p.phtAlias) {
			w.push(this.phtName(p.sel) + '[' + bin(p.hist, this.kb) + '] last trained by ' + brName(p.phtPrev) + ': shared entry');
		}
		return w;
	};

	function makeDef(v) {
		return {
			id: v,
			name: v,
			title: TITLE[v],
			group: 'III-A · Two-level (Yeh & Patt), Fig. 4',
			figure: 'Fig. 4',
			knobs: knobsFor(v),
			validate: function (k) {
				if (v[0] === 'P' && k.ways > k.rows) return 'more ways than BHR entries';
				const n = (1 << selBits(v, k)) * (1 << k.k);
				if (n > MAX_PHT) return 'PHT would need ' + n.toLocaleString() + ' counters (limit ' + MAX_PHT.toLocaleString() + ')';
				return null;
			},
			create: function (k, opts) { return new TwoLevel(v, k, opts); },
			about: aboutText(v)
		};
	}

	function aboutText(v) {
		const H = { G: 'one global branch history register (the last k outcomes of any branch)',
			P: 'a table of per-address history registers, indexed by the low bits of the branch address',
			S: 'a table of per-set history registers; a set is the aligned code block the branch lives in, SetH(B)' }[v[0]];
		const L = { g: 'a single global PHT', p: 'one PHT per branch address, picked by Addr(B)', s: 'one PHT per set, picked by SetP(B), the low address bits' }[v[2]];
		return v + ' keeps ' + H + ', and uses those k bits to index ' + L + '.';
	}

	const TWO_LEVEL = ['GAg', 'GAs', 'GAp', 'PAg', 'PAs', 'PAp', 'SAg', 'SAs', 'SAp'].map(makeDef);

	BP.twolevel = { TWO_LEVEL };

})(window.BP = window.BP || {});
