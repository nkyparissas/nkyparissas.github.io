/* ==========================================================================
   /bp: Lee et al.'s bi-mode predictor (survey Section III-D, Fig. 7).

   The level-2 counters are split into a "taken" and a "not-taken" direction
   PHT, both indexed by global history XOR branch address. A choice
   predictor (counters indexed by address only) learns each branch's bias
   and picks which direction PHT supplies the prediction, so branches of
   opposite bias stop sharing counters even when their indices collide.

   Update (partial): only the selected direction counter is trained. The
   choice counter is trained too, except when it pointed the wrong way but
   the selected direction counter was right anyway.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, CounterTable, GlobalHistory, hex, binShort, pcField, brName, interferenceText } = BP.base;
	const { gshareIndex } = BP.mcfarling;
	const { callouts } = BP.figure;
	const S = BP.svg;

	const SIDE = ['NT', 'T'];

	class BiMode extends Predictor {
		constructor(knobs, opts) {
			super(knobs, opts);
			this.cb = knobs.ci;
			this.db = knobs.di;
			this.h = knobs.h;
			this.ghr = new GlobalHistory(Math.max(1, knobs.h), 'GHR');
			this.choice = new CounterTable(1 << knobs.ci, knobs.n, 'Choice predictor');
			const half = 1 << (knobs.n - 1);
			// Each direction PHT starts weakly biased its own way.
			this.dir = [new CounterTable(1 << knobs.di, knobs.n, 'Not-taken PHT', undefined, half - 1),
				new CounterTable(1 << knobs.di, knobs.n, 'Taken PHT', undefined, half)];
			this.latency = 1;
		}

		tables() { return [this.choice, this.dir[0], this.dir[1]]; }
		storageBits() { return (this.choice.size + 2 * this.dir[0].size) * this.k.n + this.h; }

		lookup(pc, br) {
			const word = pc >>> 2;
			const hist = this.h ? this.ghr.v & ((1 << this.h) - 1) : 0;
			const ci = word & (this.choice.size - 1);
			const di = gshareIndex(word, hist, this.db, this.h);
			const c = this.choice.read(ci, br);
			const side = c.taken ? 1 : 0;
			const d = this.dir[side].read(di, br);
			// The other direction PHT is read in parallel too (Fig. 7), only for the figure.
			const other = this.dir[1 - side].ctr[di];
			return {
				taken: d.taken, hist: hist, addr: word & (this.choice.size - 1), ci: ci, di: di, useT: c.taken,
				cctr: c.v, cPriv: c.privTaken, cAlias: c.alias, cPrev: c.prev,
				ctr: d.v, other: other, priv: d.privTaken, alias: d.alias, prev: d.prev
			};
		}

		shiftHistory(p, bit, undo) {
			p.newHist = this.ghr.shift(bit, undo, p.seq) & ((1 << this.h) - 1);
		}

		train(p, taken, mis) {
			const side = p.useT ? 1 : 0;
			const t = this.dir[side];
			const before = t.ctr[p.di];
			const after = t.train(p.di, taken, p.br);
			const inter = t.noteOutcome(p.taken, p.priv, taken);
			const cBefore = this.choice.ctr[p.ci];
			// Keep the choice when it was "wrong" but its pick still predicted correctly.
			const keep = p.useT !== taken && p.taken === taken;
			const cInter = this.choice.noteOutcome(p.useT, p.cPriv, taken);
			const cAfter = keep ? cBefore : this.choice.train(p.ci, taken, p.br);
			return { side: side, before: before, after: after, inter: inter, cBefore: cBefore, cAfter: cAfter, keep: keep, cInter: cInter,
				histWritten: !this.spec || mis, newHist: p.newHist };
		}

		describePredict(p) {
			let s = 'choice[' + pcField(2, this.cb) + ' = ' + hex(p.ci, this.cb) + '] = ' + this.choice.fmt(p.cctr) +
				' → ' + (p.useT ? 'taken' : 'not-taken') + '-biased: use the ' + SIDE[p.useT ? 1 : 0] + ' PHT';
			if (p.cAlias) s += ' (choice entry last trained by ' + brName(p.cPrev) + ')';
			s += ' · PC ⊕ GHR ' + (this.h ? binShort(p.hist, this.h, 16) : '—') + ' = ' + hex(p.di, this.db) +
				' → ' + SIDE[p.useT ? 1 : 0] + '-PHT[' + hex(p.di, this.db) + '] = ' + this.dir[0].fmt(p.ctr);
			if (p.alias) s += ' (last trained by ' + brName(p.prev) + ')';
			return { text: s + ' → predict ' + (p.taken ? 'T' : 'NT'), warn: false };
		}

		describeUpdate(u) {
			const p = u.p;
			let s = SIDE[u.side] + '-PHT[' + hex(p.di, this.db) + '] ' + this.dir[0].fmt(u.before) + '→' + this.dir[0].fmt(u.after) +
				' (the other PHT is not touched)';
			s += u.keep ? ' · choice kept at ' + this.choice.fmt(u.cBefore) + ': it pointed the wrong way but its PHT was right'
				: ' · choice ' + this.choice.fmt(u.cBefore) + '→' + this.choice.fmt(u.cAfter);
			if (u.histWritten && this.h) s += ' · GHR ← ' + (u.taken ? 1 : 0) + (u.repaired ? ' (repaired)' : '');
			s += interferenceText(u.inter, p.br, p.prev, u.taken);
			return { text: s, warn: u.inter === 'destructive' };
		}

		warnings(p) {
			if (p.alias) return [SIDE[p.useT ? 1 : 0] + '-PHT[' + hex(p.di, this.db) + '] last trained by ' + brName(p.prev) + ' (same bias, so usually harmless)'];
			if (p.cAlias) return ['choice entry last trained by ' + brName(p.cPrev) + ': aliasing'];
			return [];
		}

		figure(view) {
			const p = view.read, u = view.upd;
			const rOn = !!(p && view.readNow), uOn = !!(u && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const fl = function (seq) { return p ? { on: rOn, dim: !rOn, seq: seq } : { dim: true }; };
			const TOP = 170, RH = 28, GAP = 34, RY = TOP + RH + RH / 2;
			const XC = 90, XY = 130;   // the XOR gate
			let s = S.figLabel(10, 8, 'bi-mode');

			// Global history XOR branch PC.
			s += S.t(30, 64, 'Global history', 'tx');
			s += S.reg({ x: 30, y: 70, w: 120, h: 24, txt: this.h ? binShort(p ? p.hist : this.ghr.v & ((1 << this.h) - 1), this.h, 12) : '—', on: rOn, seq: 0,
				write: u && u.histWritten, seqWrite: 4, readDim: !rOn, writeDim: !uOn });
			s += S.wire([[XC, 94], [XC, XY - 14]], 'rd', fl(0));
			s += S.t(400, 98, 'Branch PC', 'tx');
			if (p) s += S.val(476, 98, hex(p.addr, this.cb), rk);
			s += S.wire([[440, 104], [440, XY]], 'rd', Object.assign(fl(0), { arrow: false }));
			s += S.dot(440, XY, rOn ? 'rd' : 'ink');
			s += S.wire([[440, XY], [XC + 14, XY]], 'rd', fl(0));
			s += S.wire([[440, XY], [620, XY], [620, RY], [562, RY]], 'rd', fl(1));
			s += S.xor(XC, XY, 12);
			s += S.wire([[XC, XY + 12], [XC, RY], [148, RY]], 'rd', fl(1));
			if (p) s += S.val(XC + 6, RY - 8, hex(p.di, this.db), rk);

			// Direction predictor: not-taken and taken PHTs, read in parallel.
			const sel = p ? (p.useT ? 1 : 0) : -1;
			const wSide = u ? u.side : -1;
			const sameDi = p && u && u.p.di === p.di;
			const cols = [150, 240].map(function (x, side) {
				return S.column({
					x: x, y: TOP, w: 60, rh: RH, gap: GAP, level: this.dir[side].level, title: [side ? 'taken' : 'not-taken'],
					read: p ? 1 : -1, readCls: side === sel ? undefined : 'q', readTxt: p ? this.dir[side].fmt(side === sel ? p.ctr : p.other) : null, seqRead: 2,
					write: wSide === side ? (sameDi ? 1 : 2) : -1, writeTxt: wSide === side ? '→' + this.dir[side].fmt(u.after) : null,
					seqWrite: 4, readDim: !rOn, writeDim: !uOn
				});
			}, this);
			s += cols[0].svg + cols[1].svg;
			s += S.wire([[210, RY], [238, RY]], 'rd', fl(1));
			s += S.t(20, 262, 'Direction', 'tx');
			s += S.t(20, 278, 'predictor', 'tx');
			if (p && p.alias) s += S.t(cols[sel].cx - 6, TOP - 26, '⚠', 'warn-glyph');

			// Choice predictor, indexed by the branch address only.
			const sameCi = p && u && u.p.ci === p.ci;
			const ch = S.column({
				x: 500, y: TOP, w: 60, rh: RH, gap: GAP, level: this.choice.level,
				read: p ? 1 : -1, readTxt: p ? this.choice.fmt(p.cctr) : null, seqRead: 2,
				write: u && !u.keep ? (sameCi ? 1 : 2) : -1, writeTxt: u && !u.keep ? '→' + this.choice.fmt(u.cAfter) : null,
				seqWrite: 4, readDim: !rOn, writeDim: !uOn
			});
			s += ch.svg;
			s += S.t(572, 262, 'Choice', 'tx');
			s += S.t(572, 278, 'predictor', 'tx');
			if (p && p.cAlias) s += S.t(480, RY + 5, '⚠', 'warn-glyph');

			// Mux: the choice picks a direction PHT.
			const MY = 346, MH = 22;
			const lit = function (side) { return p ? { on: rOn && side === sel, dim: !(rOn && side === sel), seq: 3 } : { dim: true }; };
			s += S.wire([[cols[0].cx, cols[0].bottom], [cols[0].cx, 332], [230, 332], [230, MY]], 'rd', lit(0));
			s += S.wire([[cols[1].cx, cols[1].bottom], [cols[1].cx, MY]], 'rd', lit(1));
			s += S.wire([[ch.cx, ch.bottom], [ch.cx, MY + MH / 2], [315, MY + MH / 2]], 'rd', fl(3));
			if (p) s += S.val(ch.cx + 6, MY + MH / 2 - 6, p.useT ? 'select T' : 'select NT', rk);
			s += S.mux(200, 320, MY, MH, 14);
			s += S.wire([[260, MY + MH], [260, 392]], 'rd', fl(4));
			s += S.t(150, 408, 'Final prediction', 'tx');
			if (p) s += S.val(268, 388, '→ ' + (p.taken ? 'taken' : 'not taken'), rk);

			// Updates: the selected direction counter, and the choice counter unless kept.
			if (u) {
				const up = { on: uOn, dim: !uOn, seq: 4 };
				if (u.side === 0) s += S.wire([[160, 340], [160, cols[0].bottom + 2]], 'up', up);
				else s += S.wire([[440, 340], [440, cols[1].rowY(sameDi ? 1 : 2)], [302, cols[1].rowY(sameDi ? 1 : 2)]], 'up', up);
				if (!u.keep) s += S.wire([[550, 340], [550, ch.bottom + 2]], 'up', up);
				s += S.val(340, 408, 'train ' + SIDE[u.side] + ' ' + this.dir[0].fmt(u.before) + '→' + this.dir[0].fmt(u.after) +
					' · choice ' + (u.keep ? 'kept' : this.choice.fmt(u.cBefore) + '→' + this.choice.fmt(u.cAfter)), uk);
			}
			s += S.t(16, 430, 'choice: ' + this.choice.describe(), 'dim');
			s += S.t(16, 446, 'not-taken PHT: ' + this.dir[0].describe() + '   ·   taken PHT: ' + this.dir[1].describe(), 'dim');
			s += callouts(view, this);
			return S.svg(680, 456, s, 'Bi-mode predictor');
		}
	}

	const BIMODE = {
		id: 'bimode',
		name: 'bi-mode',
		title: 'Choice predictor picks a taken or a not-taken PHT',
		group: 'III-D · Biased branches: bi-mode (Fig. 7), agree (Fig. 8)',
		figure: 'Fig. 7',
		knobs: [
			{ id: 'ci', label: 'choice index bits', type: 'int', min: 2, max: 16, def: 10, help: 'The choice predictor has 2^bits counters, indexed by the branch address.' },
			{ id: 'di', label: 'direction index bits', type: 'int', min: 2, max: 16, def: 10, help: 'Each direction PHT has 2^bits counters, indexed by address XOR history.' },
			{ id: 'h', label: 'h · history bits', type: 'int', min: 0, max: 16, def: 10, help: 'Global history length (at most the direction index bits).' },
			{ id: 'n', label: 'N · counter bits', type: 'int', min: 1, max: 4, def: 2, help: 'Width of every counter.' }
		],
		validate: function (k) { return k.h > k.di ? 'the history cannot be longer than the direction index' : null; },
		create: function (k, opts) { return new BiMode(k, opts); },
		about: 'Lee et al. split the PHT into a taken and a not-taken direction predictor and let a choice predictor, indexed by address, ' +
			'decide which one a branch uses. Branches of opposite bias then train different counters even when their indices collide, ' +
			'which removes most destructive aliasing while keeping the neutral and helpful kind.'
	};

	BP.bimode = { BIMODE };

})(window.BP = window.BP || {});
