/* ==========================================================================
   /bp: Skadron et al.'s alloyed-index predictor (MAs), survey Fig. 5.

   A per-address BHT supplies p local history bits and a GHR supplies g global
   bits; both are "alloyed" with a address bits into one PHT index, so a branch
   gets local and global context without a meta-predictor.

   Fig. 5(a) reads the BHT and then the PHT (two serial accesses, two cycles).
   Fig. 5(b) splits the PHT into 2^p tables read in parallel with the BHT, and
   the p local bits drive a mux instead; one cycle, but only practical for
   small p (the paper says p <= 4).

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, CounterTable, HistoryTable, GlobalHistory, log2, hex, bin, binShort, pcField, brName, interferenceText } = BP.base;
	const { callouts } = BP.figure;
	const S = BP.svg;

	class Alloyed extends Predictor {
		constructor(knobs, opts) {
			super(knobs, opts);
			this.rows = knobs.rows;
			this.ib = log2(knobs.rows);
			this.a = knobs.a;
			this.g = knobs.g;
			this.p = knobs.p;
			this.par = knobs.layout === 'b';
			this.bht = new HistoryTable(knobs.rows, 1, Math.max(1, knobs.p), 'BHT');
			this.ghr = new GlobalHistory(Math.max(1, knobs.g), 'GHR');
			this.pht = new CounterTable(1 << (knobs.a + knobs.g + knobs.p), knobs.n, this.par ? 'PHTs' : 'PHT');
			this.latency = this.par ? 1 : 2;
		}

		tables() { return [this.bht, this.pht]; }
		storageBits() { return this.pht.size * this.k.n + this.rows * this.p + this.g; }

		lookup(pc, br) {
			const word = pc >>> 2;
			const l1 = this.bht.lookup(word & (this.rows - 1), 0, br);
			const local = this.p ? l1.hist & ((1 << this.p) - 1) : 0;
			const glob = this.g ? this.ghr.v & ((1 << this.g) - 1) : 0;
			const addr = this.a ? word & ((1 << this.a) - 1) : 0;
			const idx = (((addr << this.g) | glob) << this.p) | local;
			const rd = this.pht.read(idx, br);
			return { taken: rd.taken, l1: l1, local: local, glob: glob, addr: addr, idx: idx, ctr: rd.v, phtAlias: rd.alias, phtPrev: rd.prev, phtPriv: rd.privTaken };
		}

		shiftHistory(p, bit, undo) {
			p.newGlob = this.ghr.shift(bit, undo, p.seq) & ((1 << this.g) - 1);
			p.newLocal = this.bht.shiftIn(p.l1.set, 0, bit, p.br, undo, p.seq).hist & ((1 << this.p) - 1);
		}

		train(p, taken, mis) {
			const before = this.pht.ctr[p.idx];
			const after = this.pht.train(p.idx, taken, p.br);
			const inter = this.pht.noteOutcome(p.taken, p.phtPriv, taken);
			this.bht.noteResolve(p.l1.alias, mis);
			return { idx: p.idx, local: p.local, before: before, after: after, histWritten: !this.spec || mis, newGlob: p.newGlob, newLocal: p.newLocal, inter: inter };
		}

		indexText(p) {
			return (this.a ? hex(p.addr, this.a) : '') + (this.a ? '|' : '') + bin(p.glob, this.g) + (this.g ? '|' : '') + bin(p.local, this.p);
		}

		describePredict(p) {
			let s = pcField(2, this.ib) + ' = ' + hex(p.l1.set, this.ib) + ' → BHT ' + hex(p.l1.set, this.ib) + ' local = ' + (this.p ? bin(p.local, this.p) : '—');
			if (p.l1.alias) s += ' (last written by ' + brName(p.l1.prev) + ': aliasing)';
			s += ' · GHR = ' + (this.g ? bin(p.glob, this.g) : '—') +
				' → alloyed index ' + pcField(2, this.a) + '|global|local = ' + this.indexText(p) +
				' → PHT = ' + this.pht.fmt(p.ctr);
			if (p.phtAlias) s += ' (last trained by ' + brName(p.phtPrev) + ')';
			return { text: s + ' → predict ' + (p.taken ? 'T' : 'NT'), warn: p.l1.alias };
		}

		describeUpdate(u) {
			let s = 'PHT[' + this.indexText(u.p) + '] ' + this.pht.fmt(u.before) + '→' + this.pht.fmt(u.after);
			if (u.histWritten) {
				s += ' · GHR ← ' + (u.taken ? 1 : 0) + ', BHT ' + hex(u.p.l1.set, this.ib) + ' ← ' + (u.taken ? 1 : 0) + (u.repaired ? ' (repaired)' : '');
			}
			s += interferenceText(u.inter, u.p.br, u.p.phtPrev, u.taken);
			if (u.mis && u.p.l1.alias) s += ' · local history polluted by ' + brName(u.p.l1.prev);
			return { text: s, warn: u.inter === 'destructive' || (u.mis && u.p.l1.alias) };
		}

		warnings(p) {
			if (p.l1.alias) return ['BHT ' + hex(p.l1.set, this.ib) + ' last written by ' + brName(p.l1.prev) + ': aliasing'];
			if (p.phtAlias) return ['PHT entry last trained by ' + brName(p.phtPrev) + ': shared entry'];
			return [];
		}

		figure(view) {
			const p = view.read, u = view.upd;
			const rOn = !!(p && view.readNow), uOn = !!(u && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const fl = function (on, seq) { return p ? { on: on, dim: !on, seq: seq } : { dim: true }; };
			let s = S.figLabel(10, 8, 'MAs ' + (this.par ? '5(b)' : '5(a)'));

			// BHT, fed by the branch address.
			const bht = S.column({
				x: 100, y: 150, w: 80, rh: 30, gap: 40, level: this.bht.level, title: ['BHT'],
				read: p ? 1 : -1, readTxt: p && this.p ? bin(p.local, this.p) : null, seqRead: 1,
				write: u && u.histWritten ? (p && p.l1.set === u.p.l1.set ? 1 : 2) : -1,
				writeTxt: u && u.histWritten && this.p ? bin(u.newLocal, this.p) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
			});
			const by = bht.rowY(1);
			s += S.t(16, 92, 'Branch address', 'tx');
			s += S.wire([[40, 100], [40, by], [98, by]], 'rd', fl(rOn, 0));
			s += S.dot(40, 116, p && rOn ? 'rd' : 'ink');
			s += S.wire([[40, 116], [262, 116], [262, 136]], 'rd', fl(rOn, 0));
			if (p) s += S.val(48, 110, pcField(2, this.ib) + ' = ' + hex(p.l1.set, this.ib), rk);
			s += bht.svg;
			if (p && p.l1.alias) s += S.t(78, by - 8, '⚠', 'warn-glyph');
			if (u && u.histWritten) {
				s += S.wire([[115, 344], [115, bht.bottom + 2]], 'up', { on: uOn, dim: !uOn, seq: 4 });
				s += S.val(121, 344, 'shift in ' + (u.taken ? 1 : 0), uk);
			}

			// GHR above the alloyed index.
			s += S.t(250, 77, 'GHR', 'tx');
			s += S.reg({ x: 286, y: 60, w: 58, h: 24, txt: this.g ? binShort(p ? p.glob : this.ghr.v, this.g, 7) : '—', on: rOn, seq: 0,
				write: u && u.histWritten, seqWrite: 4, readDim: !rOn, writeDim: !uOn });
			s += S.wire([[315, 84], [315, 136]], 'rd', fl(rOn, 1));

			// Alloyed index cells: address | global | local (Fig. 5 order).
			const iy = 138;
			s += S.rect(240, iy, 46, 20, 'idxcell');
			s += S.rect(286, iy, 58, 20, 'idxcell');
			if (p) {
				s += S.tMid(263, iy + 14, this.a ? hex(p.addr, this.a) : '—', 'mono');
				s += S.tMid(315, iy + 14, this.g ? binShort(p.glob, this.g, 7) : '—', 'mono');
			}
			let outX = 344;
			if (!this.par) {
				s += S.rect(344, iy, 50, 20, 'idxcell');
				if (p) s += S.tMid(369, iy + 14, this.p ? binShort(p.local, this.p, 6) : '—', 'mono');
				s += S.wire([[bht.right, by], [369, by], [369, iy + 22]], 'rd', fl(rOn, 1));
				outX = 394;
				s += S.t(348, iy + 32, 'p=' + this.p, 'dim');
			}
			s += S.t(244, iy + 32, 'a=' + this.a, 'dim');
			s += S.t(290, iy + 32, 'g=' + this.g, 'dim');
			s += S.t(240, iy + 50, 'Alloyed index', 'tx');

			const pr = 195;
			const ctrTxt = p ? this.pht.fmt(p.ctr) : null;
			const sameIdx = p && u && u.idx === p.idx;
			if (!this.par) {
				const pht = S.column({
					x: 470, y: 120, w: 70, rh: 30, gap: 40, level: this.pht.level, title: ['PHT'],
					read: p ? 2 : -1, readTxt: ctrTxt, seqRead: 2,
					write: u ? (sameIdx ? 2 : 1) : -1, writeTxt: u ? '→' + this.pht.fmt(u.after) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
				});
				s += pht.svg;
				s += S.wire([[outX, iy + 10], [430, iy + 10], [430, pr], [468, pr]], 'rd', fl(rOn, 2));
				s += S.tick(430, 172, 'v', null);
				s += S.t(384, 177, (this.a + this.g + this.p) + ' bits', 'tx sm');
				s += S.wire([[pht.right, pr], [pht.right + 40, pr]], 'rd', fl(rOn, 3));
				if (p) {
					s += S.val(pht.right + 46, pr - 4, 'ctr ' + ctrTxt, rk);
					s += S.val(pht.right + 46, pr + 13, '→ ' + (p.taken ? 'taken' : 'not taken'), rk);
				}
				if (u) {
					s += S.wire([[pht.cx, 344], [pht.cx, pht.bottom + 2]], 'up', { on: uOn, dim: !uOn, seq: 4 });
					s += S.val(pht.cx + 6, 344, 'train ' + this.pht.fmt(u.before) + '→' + this.pht.fmt(u.after), uk);
				}
			} else {
				// 2^p PHTs read in parallel; the p local bits select one through the mux.
				const front = S.column({
					x: 470, y: 120, w: 50, rh: 30, gap: 40, level: this.pht.level,
					read: p ? 2 : -1, readTxt: ctrTxt, seqRead: 2,
					write: u && (!p || u.local === p.local) ? (sameIdx ? 2 : 1) : -1, writeTxt: u ? '→' + this.pht.fmt(u.after) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
				});
				const back = S.column({
					x: 560, y: 120, w: 50, rh: 30, gap: 40, level: this.pht.level,
					read: p ? 2 : -1, readCls: 'q', seqRead: 2,
					write: u && p && u.local !== p.local ? 1 : -1, writeTxt: u ? '→' + this.pht.fmt(u.after) : null, seqWrite: 4, readDim: !rOn, writeDim: !uOn
				});
				s += back.svg + front.svg;
				s += S.t(398, 128, 'PHT[' + (p && this.p ? bin(p.local, this.p) : 'local') + ']', 'tx sm');
				s += S.t(back.right + 6, 140, 'others', 'tx sm');
				s += '<path d="M520,120 L560,120 M520,' + front.bottom + ' L560,' + back.bottom + '" class="gapline"/>';
				s += S.t(470, 86, (1 << this.p) + ' PHTs read in parallel', 'dim');
				s += S.wire([[outX, iy + 10], [440, iy + 10], [440, pr], [468, pr]], 'rd', fl(rOn, 1));
				s += S.tick(440, 172, 'v', null);
				s += S.t(394, 177, (this.a + this.g) + ' bits', 'tx sm');
				const my = 316, mh = 22;
				s += S.wire([[front.cx, front.bottom], [front.cx, my]], 'rd', Object.assign(fl(rOn, 2), { arrow: false }));
				s += S.wire([[back.cx, back.bottom], [back.cx, my]], 'rd', { dim: true, arrow: false });
				s += S.mux(470, 620, my, mh, 14);
				s += S.wire([[bht.cx, bht.bottom], [bht.cx, my + mh / 2], [475, my + mh / 2]], 'rd', fl(rOn, 2));
				s += S.tick(300, my + mh / 2, 'h', 'p = ' + this.p);
				if (p) s += S.val(312, my + mh / 2 - 6, bin(p.local, this.p), rk);
				s += S.wire([[545, my + mh], [545, 356]], 'rd', fl(rOn, 3));
				if (p) s += S.val(552, 352, 'ctr ' + ctrTxt + ' → ' + (p.taken ? 'T' : 'NT'), rk);
				if (u) {
					const ux = (!p || u.local === p.local) ? front.cx : back.cx;
					s += S.wire([[ux, 94], [ux, 118]], 'up', { on: uOn, dim: !uOn, seq: 4 });
				}
			}
			s += S.t(16, 366, 'BHT ' + this.bht.describe() + '   ·   PHT ' + this.pht.describe(), 'dim');
			s += callouts(view, this);
			return S.svg(680, 374, s, 'Alloyed-index predictor');
		}
	}

	const ALLOYED = {
		id: 'MAs',
		name: 'MAs (alloyed)',
		title: 'Skadron et al.: local and global history alloyed into one PHT index',
		group: 'III-A · Alloyed index (Skadron et al.), Fig. 5',
		figure: 'Fig. 5',
		knobs: [
			{ id: 'layout', label: 'layout', type: 'choice', options: [{ v: 'a', label: 'Fig. 5(a) serial' }, { v: 'b', label: 'Fig. 5(b) parallel' }], def: 'a',
				help: '5(a) reads BHT then PHT (2 cycles). 5(b) reads 2^p PHTs alongside the BHT and muxes (1 cycle, p <= 4).' },
			{ id: 'rows', label: 'BHT entries', type: 'pow2', min: 16, max: 4096, def: 256,
				help: 'Per-address local history registers (direct-mapped, tag-less).' },
			{ id: 'a', label: 'a · address bits', type: 'int', min: 0, max: 12, def: 4, help: 'Branch address bits in the index.' },
			{ id: 'g', label: 'g · global bits', type: 'int', min: 0, max: 14, def: 4, help: 'Global history bits in the index.' },
			{ id: 'p', label: 'p · local bits', type: 'int', min: 0, max: 10, def: 4, help: 'Local (per-address) history bits in the index.' },
			{ id: 'n', label: 'N · counter bits', type: 'int', min: 1, max: 4, def: 2, help: 'Width of each PHT counter.' }
		],
		validate: function (k) {
			if (k.layout === 'b' && k.p > 4) return 'Fig. 5(b) needs p ≤ 4 (one PHT per local pattern)';
			if (k.a + k.g + k.p < 1) return 'the index needs at least one bit';
			if (k.a + k.g + k.p > 22) return 'a + g + p must be at most 22';
			return null;
		},
		create: function (k, opts) { return new Alloyed(k, opts); },
		about: 'Skadron et al. note that many mispredictions come from tracking the wrong kind of history. MAs alloys local (BHT) and ' +
			'global (GHR) history bits with address bits into a single PHT index. With a = 0, g = 0 and p = 1 it degenerates towards bimodal.'
	};

	BP.alloyed = { ALLOYED };

})(window.BP = window.BP || {});
