/* ==========================================================================
   /bp: McFarling's gselect and gshare (survey Section III-B, Table III).

   Both index one PHT with global history and branch address bits. gselect
   concatenates a address bits with h history bits; gshare XORs them over
   i bits, so the same storage can use more of both. A history shorter than
   the index is XORed into the high-order end, as McFarling does.

   The survey has no figure for these, so the panel uses the notation of
   Fig. 4 and Fig. 7: a grey history register, an XOR gate, a PHT column.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, CounterTable, GlobalHistory, hex, bin, binShort, pcField, brName, interferenceText } = BP.base;
	const { callouts } = BP.figure;
	const S = BP.svg;

	// gshare index: i address bits XOR h history bits aligned to the top of the index.
	function gshareIndex(word, hist, i, h) {
		return (word ^ (hist << (i - h))) & ((1 << i) - 1);
	}

	class McFarling extends Predictor {
		constructor(kind, knobs, opts) {
			super(knobs, opts);
			this.kind = kind;
			this.sh = kind === 'gshare';
			this.h = knobs.h;
			this.ab = this.sh ? knobs.i : knobs.a;   // address bits in the index
			this.ib = this.sh ? knobs.i : knobs.a + knobs.h;
			this.ghr = new GlobalHistory(Math.max(1, knobs.h), 'GHR');
			this.pht = new CounterTable(1 << this.ib, knobs.n, 'PHT');
			this.latency = 1;
		}

		tables() { return [this.pht]; }
		storageBits() { return this.pht.size * this.k.n + this.h; }

		lookup(pc, br) {
			const word = pc >>> 2;
			const hist = this.h ? this.ghr.v & ((1 << this.h) - 1) : 0;
			const addr = word & ((1 << this.ab) - 1);
			const idx = this.sh ? gshareIndex(word, hist, this.ib, this.h) : (addr << this.h) | hist;
			const rd = this.pht.read(idx, br);
			return { taken: rd.taken, hist: hist, addr: addr, idx: idx, ctr: rd.v, alias: rd.alias, prev: rd.prev, priv: rd.privTaken };
		}

		shiftHistory(p, bit, undo) {
			p.newHist = this.ghr.shift(bit, undo, p.seq) & ((1 << this.h) - 1);
		}

		train(p, taken, mis) {
			const before = this.pht.ctr[p.idx];
			const after = this.pht.train(p.idx, taken, p.br);
			const inter = this.pht.noteOutcome(p.taken, p.priv, taken);
			return { idx: p.idx, before: before, after: after, histWritten: !this.spec || mis, newHist: p.newHist, inter: inter };
		}

		histText(v) { return this.h ? binShort(v, this.h, 18) : '—'; }

		describePredict(p) {
			let s = pcField(2, this.ab) + ' = ' + hex(p.addr, this.ab) + (this.sh ? ' ⊕ ' : ' | ') + 'GHR ' + this.histText(p.hist) +
				' → index ' + hex(p.idx, this.ib) + ' → PHT[' + hex(p.idx, this.ib) + '] = ' + this.pht.fmt(p.ctr);
			if (p.alias) s += ' (last trained by ' + brName(p.prev) + ')';
			return { text: s + ' → predict ' + (p.taken ? 'T' : 'NT'), warn: false };
		}

		describeUpdate(u) {
			let s = 'PHT[' + hex(u.idx, this.ib) + '] ' + this.pht.fmt(u.before) + '→' + this.pht.fmt(u.after);
			if (u.histWritten && this.h) s += ' · GHR ← ' + (u.taken ? 1 : 0) + ' = ' + this.histText(u.newHist) + (u.repaired ? ' (speculative history repaired)' : '');
			s += interferenceText(u.inter, u.p.br, u.p.prev, u.taken);
			return { text: s, warn: u.inter === 'destructive' };
		}

		warnings(p) {
			return p.alias ? ['PHT[' + hex(p.idx, this.ib) + '] last trained by ' + brName(p.prev) + ': shared entry'] : [];
		}

		figure(view) {
			const p = view.read, u = view.upd;
			const rOn = !!(p && view.readNow), uOn = !!(u && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const fl = function (seq) { return p ? { on: rOn, dim: !rOn, seq: seq } : { dim: true }; };
			const RY = 165;   // the row everything converges on
			let s = S.figLabel(10, 8, this.kind);

			// Global history register.
			s += S.tMid(125, 92, 'Global history', 'tx');
			s += S.reg({ x: 60, y: 96, w: 130, h: 28, txt: this.histText(p ? p.hist : this.ghr.v & ((1 << this.h) - 1)).slice(-14), on: rOn, seq: 0,
				write: u && u.histWritten, seqWrite: 4, readDim: !rOn, writeDim: !uOn });
			if (u && u.histWritten) {
				s += S.wire([[125, 330], [125, 126]], 'up', { on: uOn, dim: !uOn, seq: 4 });
				s += S.val(131, 322, 'shift in ' + (u.taken ? 1 : 0), uk);
			}

			// Branch address.
			s += S.t(16, 222, 'Branch address', 'tx');
			if (p) s += S.val(16, 250, pcField(2, this.ab) + ' = ' + hex(p.addr, this.ab), rk);

			if (this.sh) {
				s += S.wire([[190, 110], [300, 110], [300, RY - 14]], 'rd', fl(0));
				s += S.tick(250, 110, 'h', 'h = ' + this.h);
				s += S.wire([[16, 230], [300, 230], [300, RY + 14]], 'rd', fl(0));
				s += S.tick(250, 230, 'h', 'i = ' + this.ib);
				s += S.xor(300, RY, 12);
				s += S.wire([[312, RY], [398, RY]], 'rd', fl(1));
				s += S.tick(356, RY, 'h', 'i');
				if (p) s += S.val(320, RY - 8, hex(p.idx, this.ib), rk);
			} else {
				const cx = 236, cw = 54;
				s += S.rect(cx, RY - 11, cw, 22, 'idxcell');
				s += S.rect(cx + cw, RY - 11, cw, 22, 'idxcell');
				if (p) {
					s += S.tMid(cx + cw / 2, RY + 4, hex(p.addr, this.ab), 'mono');
					s += S.tMid(cx + cw * 1.5, RY + 4, binShort(p.hist, this.h, 6), 'mono');
				}
				s += S.t(cx + 2, RY + 30, 'a = ' + this.ab, 'dim');
				s += S.t(cx + cw + 2, RY + 30, 'h = ' + this.h, 'dim');
				s += S.t(cx, RY - 20, 'index', 'tx sm');
				s += S.wire([[190, 110], [cx + cw * 1.5, 110], [cx + cw * 1.5, RY - 13]], 'rd', fl(0));
				s += S.wire([[16, 230], [200, 230], [200, RY], [cx - 2, RY]], 'rd', fl(0));
				s += S.wire([[cx + 2 * cw, RY], [398, RY]], 'rd', fl(1));
				s += S.tick(370, RY, 'h', 'a+h');
			}

			// PHT.
			const sameIdx = p && u && u.idx === p.idx;
			const col = S.column({
				x: 400, y: RY - 45, w: 70, rh: 30, gap: 40, level: this.pht.level, title: ['PHT'],
				read: p ? 1 : -1, readTxt: p ? this.pht.fmt(p.ctr) : null, seqRead: 2,
				write: u ? (sameIdx ? 1 : 2) : -1, writeTxt: u ? '→' + this.pht.fmt(u.after) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
			});
			s += col.svg;
			if (p && p.alias) s += S.t(380, RY - 8, '⚠', 'warn-glyph');
			s += S.wire([[col.right, RY], [col.right + 44, RY]], 'rd', fl(3));
			if (p) {
				s += S.val(col.right + 50, RY - 4, 'ctr ' + this.pht.fmt(p.ctr), rk);
				s += S.val(col.right + 50, RY + 13, '→ ' + (p.taken ? 'taken' : 'not taken'), rk);
			}
			if (u) {
				s += S.wire([[435, 330], [435, col.bottom + 2]], 'up', { on: uOn, dim: !uOn, seq: 4 });
				s += S.val(441, 322, 'train ' + this.pht.fmt(u.before) + '→' + this.pht.fmt(u.after), uk);
			}
			s += S.t(400, 352, this.pht.describe(), 'dim');
			s += callouts(view, this);
			return S.svg(680, 362, s, this.kind + ' predictor');
		}
	}

	const COMMON_ABOUT = ' Global history alone separates branches poorly in small tables, and address bits alone learn no patterns; ' +
		'combining them is McFarling\'s answer (Table III shows two branch/history pairs that only gshare tells apart).';

	const GSELECT = {
		id: 'gselect',
		name: 'gselect',
		title: 'Address bits concatenated with global history',
		group: 'III-B · Global history and address (McFarling), Table III',
		figure: 'Table III',
		knobs: [
			{ id: 'a', label: 'a · address bits', type: 'int', min: 1, max: 12, def: 5, help: 'Low branch address bits in the index.' },
			{ id: 'h', label: 'h · history bits', type: 'int', min: 1, max: 14, def: 5, help: 'Global history bits in the index.' },
			{ id: 'n', label: 'N · counter bits', type: 'int', min: 1, max: 4, def: 2, help: 'Width of each PHT counter.' }
		],
		validate: function (k) { return k.a + k.h > 22 ? 'a + h must be at most 22' : null; },
		create: function (k, opts) { return new McFarling('gselect', k, opts); },
		about: 'gselect concatenates a low address bits with h global history bits into a single PHT index of a + h bits.' + COMMON_ABOUT
	};

	const GSHARE = {
		id: 'gshare',
		name: 'gshare',
		title: 'Address bits XORed with global history',
		group: 'III-B · Global history and address (McFarling), Table III',
		figure: 'Table III',
		knobs: [
			{ id: 'i', label: 'i · index bits', type: 'int', min: 2, max: 18, def: 10, help: 'The PHT has 2^i counters; i address bits are XORed with the history.' },
			{ id: 'h', label: 'h · history bits', type: 'int', min: 0, max: 18, def: 10, help: 'Global history length (at most i); a shorter history is XORed into the top of the index.' },
			{ id: 'n', label: 'N · counter bits', type: 'int', min: 1, max: 4, def: 2, help: 'Width of each PHT counter.' }
		],
		validate: function (k) { return k.h > k.i ? 'the history cannot be longer than the index (h ≤ i)' : null; },
		create: function (k, opts) { return new McFarling('gshare', k, opts); },
		about: 'gshare XORs i low address bits with the h most recent global outcomes, so every index bit carries both kinds of information.' + COMMON_ABOUT
	};

	BP.mcfarling = { gshareIndex, GSELECT, GSHARE };

})(window.BP = window.BP || {});
