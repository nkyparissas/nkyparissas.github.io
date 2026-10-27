/* ==========================================================================
   /bp: Sprangle et al.'s agree predictor (survey Section III-D, Fig. 8).

   Each branch gets a biasing bit, set to its direction the first time it
   executes and kept with its BTB entry. The PHT (indexed by history XOR
   address, gshare style) no longer predicts a direction: its counters
   predict whether the branch will agree with its biasing bit. Two biased
   branches that share a counter now usually push it the same way (both
   "agree"), turning destructive aliasing into harmless aliasing.

   The biasing bit table is modelled as its own tagged, set-associative
   table with LRU, organised like a BTB. A branch that misses in it has no
   BTB entry and so no target: fetch falls through, i.e. predicts not taken,
   and the bit is allocated when the branch resolves.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, TableStats, CounterTable, GlobalHistory, log2, hex, binShort, brName, interferenceText } = BP.base;
	const { gshareIndex } = BP.mcfarling;
	const { callouts } = BP.figure;
	const S = BP.svg;

	// Tagged biasing bit table: one bit per branch, set by its first outcome.
	class BiasTable extends TableStats {
		constructor(entries, ways) {
			super('Biasing bit table', entries, 'evict');
			this.ways = ways;
			this.sets = entries / ways;
			this.sb = log2(this.sets);
			this.tag = new Int32Array(entries).fill(-1);
			this.bit = new Uint8Array(entries);
			this.owner = new Int32Array(entries).fill(-1);
			this.lru = new Float64Array(entries);
			this.tick = 0;
		}

		where(pc) {
			const w = pc >>> 2;
			return { set: w & (this.sets - 1), tag: w >>> this.sb };
		}

		find(set, tag) {
			const b = set * this.ways;
			for (let i = 0; i < this.ways; i++) if (this.tag[b + i] === tag) return b + i;
			return -1;
		}

		victim(set) {
			const b = set * this.ways;
			let v = b;
			for (let i = 0; i < this.ways; i++) {
				if (this.tag[b + i] < 0) return b + i;
				if (this.lru[b + i] < this.lru[v]) v = b + i;
			}
			return v;
		}

		// Prediction-time lookup. A miss in a full set means another branch will lose its bit
		// when this one is inserted; the eviction itself is counted then, once.
		lookup(pc) {
			const a = this.where(pc);
			const s = this.find(a.set, a.tag);
			if (s >= 0) {
				this.lru[s] = ++this.tick;
				this.noteLookup(false);
				return { hit: true, slot: s, set: a.set, tag: a.tag, bit: this.bit[s] };
			}
			const v = this.victim(a.set);
			return { hit: false, slot: v, set: a.set, tag: a.tag, bit: 0, evict: this.tag[v] >= 0, prev: this.owner[v] };
		}

		// First resolution of a branch (or first since it was evicted): record its direction.
		insert(pc, bit, br) {
			const a = this.where(pc);
			let s = this.find(a.set, a.tag);
			const fresh = s < 0;
			if (fresh) s = this.victim(a.set);
			const prev = fresh && this.tag[s] >= 0 ? this.owner[s] : -1;
			if (fresh) {
				this.noteLookup(prev >= 0);
				this.tag[s] = a.tag;
				this.bit[s] = bit;
				this.owner[s] = br;
				this.touch(s);
			}
			this.lru[s] = ++this.tick;
			return { slot: s, fresh: fresh, prev: prev, bit: this.bit[s] };
		}
	}

	class Agree extends Predictor {
		constructor(knobs, opts) {
			super(knobs, opts);
			this.ib = knobs.i;
			this.h = knobs.h;
			this.ghr = new GlobalHistory(Math.max(1, knobs.h), 'BHR');
			this.pht = new CounterTable(1 << knobs.i, knobs.n, 'PHT (agree counters)');   // start weakly "agree"
			this.bias = new BiasTable(knobs.brows, Math.min(knobs.bways, knobs.brows));
			this.latency = 1;
		}

		tables() { return [this.pht, this.bias]; }
		storageBits() { return this.pht.size * this.k.n + this.bias.size + this.h; }   // the bit only: tags belong to the BTB

		lookup(pc, br) {
			const word = pc >>> 2;
			const hist = this.h ? this.ghr.v & ((1 << this.h) - 1) : 0;
			const idx = gshareIndex(word, hist, this.ib, this.h);
			const b = this.bias.lookup(pc);
			const p = { hist: hist, idx: idx, biasHit: b.hit, bias: b.bit, bset: b.set, btag: b.tag, bevict: !!b.evict, bprev: b.prev };
			if (!b.hit) {
				p.taken = false;
				return p;
			}
			const rd = this.pht.read(idx, br);
			p.ctr = rd.v;
			p.agree = rd.taken;
			p.priv = rd.privTaken;
			p.alias = rd.alias;
			p.prev = rd.prev;
			p.taken = p.agree ? b.bit === 1 : b.bit === 0;
			return p;
		}

		shiftHistory(p, bit, undo) {
			p.newHist = this.ghr.shift(bit, undo, p.seq) & ((1 << this.h) - 1);
		}

		train(p, taken, mis) {
			const u = { histWritten: !this.spec || mis, newHist: p.newHist };
			if (p.biasHit) {
				const agreed = taken === (p.bias === 1);
				u.agreed = agreed;
				u.before = this.pht.ctr[p.idx];
				u.after = this.pht.train(p.idx, agreed, p.br);
				u.inter = this.pht.noteOutcome(p.agree, p.priv, agreed);
			}
			u.ins = this.bias.insert(p.pc, taken ? 1 : 0, p.br);
			return u;
		}

		describePredict(p) {
			let s = 'bias table set ' + hex(p.bset, this.bias.sb) + ', tag ' + hex(p.btag, 8) + ': ';
			if (!p.biasHit) {
				s += 'miss' + (p.bevict ? ' (set full: ' + brName(p.bprev) + '\'s bit will be evicted)' : '') +
					', so no BTB entry and no biasing bit → fetch falls through, predict NT';
				return { text: s, warn: p.bevict };
			}
			s += 'hit, biasing bit ' + (p.bias ? 'T' : 'NT') + ' · PC ⊕ BHR ' + (this.h ? binShort(p.hist, this.h, 16) : '—') +
				' = ' + hex(p.idx, this.ib) + ' → PHT[' + hex(p.idx, this.ib) + '] = ' + this.pht.fmt(p.ctr) + ' (' + (p.agree ? 'agree' : 'disagree') + ')';
			if (p.alias) s += ' (last trained by ' + brName(p.prev) + ')';
			return { text: s + ' → predict ' + (p.taken ? 'T' : 'NT'), warn: false };
		}

		describeUpdate(u) {
			const p = u.p;
			let s;
			if (p.biasHit) {
				s = 'outcome ' + (u.taken ? 'T' : 'NT') + (u.agreed ? ' agrees' : ' disagrees') + ' with the biasing bit → PHT[' + hex(p.idx, this.ib) + '] ' +
					this.pht.fmt(u.before) + '→' + this.pht.fmt(u.after);
			} else {
				s = 'first execution since allocation: biasing bit ← ' + (u.taken ? 'T' : 'NT') + ' (PHT not trained)';
				if (u.ins.prev >= 0) s += ', evicting ' + brName(u.ins.prev) + '\'s bit';
			}
			if (u.histWritten && this.h) s += ' · BHR ← ' + (u.taken ? 1 : 0) + (u.repaired ? ' (repaired)' : '');
			if (p.biasHit) s += interferenceText(u.inter, p.br, p.prev, u.agreed);
			return { text: s, warn: u.inter === 'destructive' };
		}

		warnings(p) {
			if (!p.biasHit && p.bevict) return ['bias table set ' + hex(p.bset, this.bias.sb) + ' full: ' + brName(p.bprev) + '\'s biasing bit will be evicted'];
			if (p.alias) return ['PHT[' + hex(p.idx, this.ib) + '] last trained by ' + brName(p.prev) + ' (agree/disagree, so often harmless)'];
			return [];
		}

		figure(view) {
			const p = view.read, u = view.upd;
			const rOn = !!(p && view.readNow), uOn = !!(u && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const fl = function (seq) { return p ? { on: rOn, dim: !rOn, seq: seq } : { dim: true }; };
			const n = this.k.n;
			let s = S.figLabel(10, 8, 'agree');

			// BHR and branch address into the indexing function.
			s += S.t(40, 112, 'BHR', 'tx');
			s += S.reg({ x: 40, y: 118, w: 120, h: 24, txt: this.h ? binShort(p ? p.hist : this.ghr.v & ((1 << this.h) - 1), this.h, 12) : '—', on: rOn, seq: 0,
				write: u && u.histWritten, seqWrite: 4, readDim: !rOn, writeDim: !uOn });
			s += S.wire([[160, 130], [190, 130], [190, 162], [218, 162]], 'rd', fl(0));
			s += S.t(20, 252, 'Branch', 'tx');
			s += S.t(20, 268, 'address', 'tx');
			if (p) s += S.val(20, 286, hex(p.pc, 16), rk);
			s += S.wire([[96, 260], [200, 260]], 'rd', Object.assign(fl(0), { arrow: false }));
			s += S.dot(200, 260, rOn ? 'rd' : 'ink');
			s += S.wire([[200, 260], [200, 182], [218, 182]], 'rd', fl(0));
			s += S.fnBox(220, 150, 100, 44, ['Indexing', 'function'], p && rOn && p.biasHit ? 'op-on' : '');

			// PHT of agree counters.
			const TOP = 104, RH = 26, GAP = 30, RY = TOP + RH + RH / 2;
			const sameIdx = p && u && u.p.idx === p.idx && u.p.biasHit;
			const pht = S.column({
				x: 400, y: TOP, w: 80, rh: RH, gap: GAP, sub: n, level: this.pht.level,
				read: p && p.biasHit ? 1 : -1, seqRead: 2,
				write: u && u.p.biasHit ? (sameIdx ? 1 : 2) : -1, writeTxt: u && u.p.biasHit ? '→' + this.pht.fmt(u.after) : null,
				seqWrite: 4, readDim: !rOn, writeDim: !uOn
			});
			s += S.tMid(440, TOP - 10, 'PHT (' + n + '-bit counter)', 'tx');
			s += pht.svg;
			s += S.wire([[322, 172], [360, 172], [360, RY], [398, RY]], 'rd', p && p.biasHit ? fl(1) : { dim: true });
			if (p && p.biasHit) s += S.val(326, 166, hex(p.idx, this.ib), rk);
			if (p && p.alias) s += S.t(380, RY - 10, '⚠', 'warn-glyph');
			// The selected counter, pulled out as in Fig. 8; its top bit says agree or disagree.
			const BX = 500, CW = Math.min(26, 56 / n);
			s += '<path d="M480,' + (RY - RH / 2) + ' L' + BX + ',' + (RY - RH / 2) + ' M480,' + (RY + RH / 2) + ' L' + BX + ',' + (RY + RH / 2) + '" class="gapline"/>';
			for (let b = 0; b < n; b++) {
				s += S.rect(BX + b * CW, RY - RH / 2, CW, RH, 'idxcell');
				if (p && p.biasHit) s += S.tMid(BX + b * CW + CW / 2, RY + 4, this.pht.fmt(p.ctr)[b], 'mono');
			}
			const ax = BX + CW / 2, CMP = 570, CY = 210;
			s += S.wire([[ax, RY + RH / 2], [ax, CY], [CMP - 2, CY]], 'rd', p && p.biasHit ? fl(3) : { dim: true });
			if (p && p.biasHit) s += S.val(ax + 4, CY - 6, p.agree ? 'agree' : 'disagree', rk);
			s += S.cmpBox(CMP, CY - 15, 30, p && rOn && p.biasHit ? 'op-on' : '');

			// Biasing bit table (in the BTB): Tag | Bit.
			const BT = 292, BRH = 22, BGAP = 22, BRY = BT + BRH + BRH / 2;
			const wRow = u && u.ins.fresh ? 2 : -1;
			const tagCol = S.column({
				x: 400, y: BT, w: 76, rh: BRH, gap: BGAP, level: this.bias.level,
				read: p ? 1 : -1, readCls: p && !p.biasHit ? 'q' : undefined, readTxt: p ? hex(p.btag, 8) : null, seqRead: 1,
				write: wRow, writeTxt: wRow > 0 ? 'new' : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
			});
			const bitCol = S.column({
				x: 476, y: BT, w: 34, rh: BRH, gap: BGAP, level: this.bias.level,
				read: p ? 1 : -1, readCls: p && !p.biasHit ? 'q' : undefined, readTxt: p && p.biasHit ? String(p.bias) : null, seqRead: 1,
				write: wRow, writeTxt: wRow > 0 ? String(u.ins.bit) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
			});
			s += S.tMid(438, BT - 8, 'Tag', 'tx sm') + S.tMid(493, BT - 8, 'Bit', 'tx sm');
			s += tagCol.svg + bitCol.svg;
			s += S.t(530, BT + 70, 'Biasing bit table', 'tx');
			s += S.t(530, BT + 86, '(in BTB)', 'tx');
			s += S.wire([[200, 260], [290, 260], [290, BRY], [398, BRY]], 'rd', fl(0));
			if (p && !p.biasHit) s += S.val(300, BRY - 8, 'miss', 'warn');
			s += S.wire([[510, BRY], [CMP + 15, BRY], [CMP + 15, CY + 17]], 'rd', p && p.biasHit ? fl(2) : { dim: true });
			if (p && p.biasHit) s += S.val(CMP + 20, BRY - 8, 'bias ' + (p.bias ? 'T' : 'NT'), rk);

			// Prediction.
			s += S.wire([[CMP + 30, CY], [664, CY]], 'rd', fl(4));
			if (p) {
				s += S.val(604, CY + 22, '→ ' + (p.taken ? 'T' : 'NT'), rk);
				if (!p.biasHit) s += S.val(560, CY + 38, 'no bias: fall through', 'warn');
			}

			// Updates.
			if (u) {
				const up = { on: uOn, dim: !uOn, seq: 4 };
				if (u.p.biasHit) {
					s += S.wire([[440, 272], [440, pht.bottom + 2]], 'up', up);
					s += S.val(446, 268, 'train ' + this.pht.fmt(u.before) + '→' + this.pht.fmt(u.after) + (u.agreed ? ' (agreed)' : ' (disagreed)'), uk);
				}
				if (u.ins.fresh) {
					s += S.wire([[438, 428], [438, tagCol.bottom + 2]], 'up', up);
					s += S.val(446, 424, 'allocate, bit ← ' + (u.taken ? 'T' : 'NT'), uk);
				}
			}
			s += S.t(16, 448, 'PHT ' + this.pht.describe() + '   ·   bias table ' + this.bias.describe(), 'dim');
			s += callouts(view, this);
			return S.svg(680, 456, s, 'Agree predictor');
		}
	}

	const AGREE = {
		id: 'agree',
		name: 'agree',
		title: 'Counters predict agreement with a per-branch biasing bit',
		group: 'III-D · Biased branches: bi-mode (Fig. 7), agree (Fig. 8)',
		figure: 'Fig. 8',
		knobs: [
			{ id: 'i', label: 'i · PHT index bits', type: 'int', min: 2, max: 18, def: 10, help: 'The PHT has 2^i agree counters, indexed by address XOR history.' },
			{ id: 'h', label: 'h · history bits', type: 'int', min: 0, max: 18, def: 10, help: 'Global history length (at most i).' },
			{ id: 'n', label: 'N · counter bits', type: 'int', min: 1, max: 4, def: 2, help: 'Width of each agree counter.' },
			{ id: 'brows', label: 'bias table entries', type: 'pow2', min: 16, max: 4096, def: 256, help: 'Biasing bits kept (one per BTB entry).' },
			{ id: 'bways', label: 'bias table ways', type: 'choice', options: [1, 2, 4, 8], def: 4, help: 'Associativity of the BTB that holds the bits (LRU).' }
		],
		validate: function (k) { return k.h > k.i ? 'the history cannot be longer than the index (h ≤ i)' : null; },
		create: function (k, opts) { return new Agree(k, opts); },
		about: 'Sprangle et al. keep a biasing bit per branch (its first outcome, stored with its BTB entry) and make the PHT predict whether the ' +
			'branch will agree with that bit. Most branches mostly agree with their own bias, so two branches sharing a counter now push it the ' +
			'same way: with biases of 85% and 15%, harmful interference drops from 74% to 25%. A new branch also finds counters already warmed up to "agree".'
	};

	BP.agree = { AGREE };

})(window.BP = window.BP || {});
