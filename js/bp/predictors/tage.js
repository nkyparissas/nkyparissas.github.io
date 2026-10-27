/* ==========================================================================
   /bp: Seznec and Michaud's TAGE predictor (survey Section III-E, Fig. 9).

   T0 is a bimodal base predictor. T1..TM are partially tagged tables whose
   entries hold a 3-bit signed prediction counter, a tag and a 2-bit useful
   counter U. Ti is indexed and tagged by hashes of the PC and the newest
   L(i) global outcomes, L(i) = floor(alpha^(i-1) * L(1) + 0.5).

   Prediction: all tables are read in parallel. The hitting table with the
   longest history is the provider, the next one (or T0) the alternate. A
   provider entry that is newly allocated (weak counter, U = 0) is not
   trusted yet, so the alternate prediction is used instead.

   Update: the provider's counter is trained (and the alternate's too while
   the provider is new). U goes up or down when the provider and the
   alternate disagreed and the provider was right or wrong. On a
   misprediction, an entry with U = 0 is allocated in a longer-history table
   (shorter ones preferred two to one); if there is none, those entries' U
   decay instead. Every so often all U counters are aged, alternately
   clearing their high and their low bit, so no entry stays useful forever.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Predictor, TableStats, CounterTable, LongHistory, TH, ALPHA, WARM, levelOf, geometric, hex, bin, brName } = BP.base;
	const { callouts } = BP.figure;
	const S = BP.svg;

	const MAX_HIST = 2048;
	const CTR_MAX = 7, WEAK_T = 4, WEAK_NT = 3, U_MAX = 3;

	function lengths(k) { return [0].concat(geometric(k.M, k.L1, k.alpha)); }
	function sgn(ctr) { const c = ctr - WEAK_T; return (c >= 0 ? '+' : '−') + Math.abs(c); }
	function sat(v, taken) { return taken ? Math.min(CTR_MAX, v + 1) : Math.max(0, v - 1); }

	// One tagged component. Stress is the worse of two signals: tag aliasing that cost a
	// prediction (the provider entry was allocated by another branch and was wrong), and
	// allocation pressure (a misprediction wanted this table's entry but it was still useful).
	class TaggedTable extends TableStats {
		constructor(entries, tagBits, name) {
			super(name, entries, 'destructive');
			this.tb = tagBits;
			this.ctr = new Uint8Array(entries).fill(WEAK_T);
			this.tag = new Int32Array(entries).fill(-1);
			this.u = new Uint8Array(entries);
			this.owner = new Int32Array(entries).fill(-1);
			this.hits = 0;
			this.falseHits = 0;
			this.allocs = 0;
			this.blocked = 0;
			this.ewA = 0;
		}

		noteHit(falseHit) {
			this.hits++;
			if (falseHit) this.falseHits++;
		}

		noteAlloc(blocked) {
			this.allocs++;
			if (blocked) this.blocked++;
			const a = Math.max(1 / this.allocs, ALPHA);
			this.ewA += ((blocked ? 1 : 0) - this.ewA) * a;
		}

		get level() {
			const l = super.level;
			return this.allocs < WARM ? l : Math.max(l, levelOf(this.ewA, TH.alloc));
		}

		describe() {
			const pct = function (x) { return (Math.round(x * 1000) / 10) + '%'; };
			return pct(this.occupancy) + ' used · ' + pct(this.hits ? this.falseHits / this.hits : 0) + ' false tag hits · ' +
				pct(this.allocs ? this.blocked / this.allocs : 0) + ' allocations blocked';
		}
	}

	class TAGE extends Predictor {
		constructor(knobs, opts) {
			super(knobs, opts);
			const M = knobs.M;
			this.M = M;
			this.lt = knobs.lt;
			this.lb = knobs.lb;
			this.tb = knobs.tb;
			this.mask = (1 << knobs.lt) - 1;
			this.tmask = (1 << knobs.tb) - 1;
			this.L = lengths(knobs);
			this.hist = new LongHistory(this.L[M], 'GHR');
			this.fi = [null];
			this.ft1 = [null];
			this.ft2 = [null];
			for (let i = 1; i <= M; i++) {
				this.fi.push(this.hist.addFold(this.L[i], knobs.lt));
				this.ft1.push(this.hist.addFold(this.L[i], knobs.tb));
				this.ft2.push(this.hist.addFold(this.L[i], knobs.tb - 1));
			}
			this.base = new CounterTable(1 << knobs.lb, 2, 'T0 (base)');
			this.T = [this.base];
			for (let i = 1; i <= M; i++) this.T.push(new TaggedTable(1 << knobs.lt, knobs.tb, 'T' + i));
			this.period = knobs.ureset;
			this.updates = 0;
			this.resets = 0;
			this.seed = 0x2545F491;
			this.latency = 1;
		}

		tables() { return this.T; }
		storageBits() { return this.base.size * 2 + this.M * (1 << this.lt) * (3 + this.tb + 2) + this.L[this.M]; }

		// Deterministic tie-break for allocation, so runs are repeatable.
		rand() {
			let x = this.seed;
			x ^= x << 13; x ^= x >>> 17; x ^= x << 5;
			this.seed = x;
			return x >>> 0;
		}

		lookup(pc, br) {
			const word = pc >>> 2, M = this.M;
			const b = this.base.read(word & (this.base.size - 1), br);
			const p = {
				idx: [word & (this.base.size - 1)], tag: [0], hit: [true], ctr: [b.v], u: [0], stag: [0], own: [b.prev],
				basePred: b.taken, basePriv: b.privTaken, recent: this.hist.text(Math.min(24, this.L[M]))
			};
			for (let i = 1; i <= M; i++) {
				const t = this.T[i];
				const ix = (word ^ (word >>> (Math.abs(this.lt - i) + 1)) ^ this.fi[i].comp) & this.mask;
				const tg = (word ^ this.ft1[i].comp ^ (this.ft2[i].comp << 1)) & this.tmask;
				p.idx.push(ix);
				p.tag.push(tg);
				p.stag.push(t.tag[ix]);
				p.ctr.push(t.ctr[ix]);
				p.u.push(t.u[ix]);
				p.own.push(t.owner[ix]);
				p.hit.push(t.tag[ix] === tg);
			}
			let prov = 0, alt = 0;
			for (let i = M; i >= 1; i--) {
				if (!p.hit[i]) continue;
				if (!prov) prov = i;
				else { alt = i; break; }
			}
			p.provider = prov;
			p.alt = alt;
			p.provPred = p.ctr[prov] >= (prov ? WEAK_T : this.base.half);
			p.altPred = p.ctr[alt] >= (alt ? WEAK_T : this.base.half);
			p.weakNew = prov > 0 && p.u[prov] === 0 && (p.ctr[prov] === WEAK_T || p.ctr[prov] === WEAK_NT);
			p.falseHit = prov > 0 && p.own[prov] !== br;
			if (prov) this.T[prov].noteHit(p.falseHit);
			p.src = prov && p.weakNew ? alt : prov;   // the table whose counter is the final prediction
			p.taken = p.weakNew ? p.altPred : p.provPred;
			return p;
		}

		shiftHistory(p, bit, undo) { this.hist.shift(bit, undo, p.seq); }

		// Train a tagged entry only if it still belongs to this branch's tag (it may have been
		// reallocated by another branch between prediction and resolution).
		trainTagged(k, p, taken) {
			const t = this.T[k], i = p.idx[k];
			if (t.tag[i] !== p.tag[k]) return null;
			const before = t.ctr[i];
			t.ctr[i] = sat(before, taken);
			return { before: before, after: t.ctr[i] };
		}

		train(p, taken, mis) {
			const M = this.M, prov = p.provider;
			const r = { histWritten: !this.spec || mis, alloc: 0, blocked: false, victim: -1, aged: '' };

			// 1. Allocate on a misprediction, in a table with a longer history than the provider.
			if (p.taken !== taken && prov < M) {
				const cands = [];
				for (let k = prov + 1; k <= M; k++) {
					const free = this.T[k].u[p.idx[k]] === 0;
					this.T[k].noteAlloc(!free);
					if (free) cands.push(k);
				}
				if (cands.length) {
					const k = cands.length > 1 && this.rand() % 3 === 0 ? cands[1] : cands[0];
					const t = this.T[k], i = p.idx[k];
					r.victim = t.tag[i] >= 0 && t.owner[i] !== p.br ? t.owner[i] : -1;
					t.tag[i] = p.tag[k];
					t.ctr[i] = taken ? WEAK_T : WEAK_NT;
					t.u[i] = 0;
					t.owner[i] = p.br;
					t.touch(i);
					r.alloc = k;
				} else {
					r.blocked = true;
					r.decayed = [];
					for (let k = prov + 1; k <= M; k++) {
						const t = this.T[k], i = p.idx[k];
						if (t.u[i] > 0) { t.u[i]--; r.decayed.push(k); }
					}
				}
			}

			// 2. Train the provider (or T0), and the alternate while the provider is newly allocated.
			if (prov) {
				const t = this.T[prov], i = p.idx[prov];
				r.prov = this.trainTagged(prov, p, taken);
				if (r.prov) {
					if (p.provPred !== p.altPred) {
						r.uBefore = t.u[i];
						if (p.provPred === taken) { if (t.u[i] < U_MAX) t.u[i]++; } else if (t.u[i] > 0) t.u[i]--;
						r.uAfter = t.u[i];
					}
					t.noteResolve(p.falseHit, p.provPred !== taken);
				}
				if (p.weakNew) {
					if (p.alt) r.altT = this.trainTagged(p.alt, p, taken);
					else r.altT = { before: this.base.ctr[p.idx[0]], after: this.base.train(p.idx[0], taken, p.br) };
				}
			} else {
				r.prov = { before: this.base.ctr[p.idx[0]], after: this.base.train(p.idx[0], taken, p.br) };
				r.inter = this.base.noteOutcome(p.basePred, p.basePriv, taken);
			}

			// 3. Periodically age every useful counter.
			this.updates++;
			if (this.period && this.updates % this.period === 0) {
				this.resets++;
				const keep = this.resets & 1 ? 1 : 2;   // odd resets clear the high bit, even ones the low bit
				for (let k = 1; k <= M; k++) {
					const uu = this.T[k].u;
					for (let e = 0; e < uu.length; e++) uu[e] &= keep;
				}
				r.aged = keep === 1 ? 'high' : 'low';
			}
			return r;
		}

		describePredict(p) {
			const hits = [];
			for (let i = 1; i <= this.M; i++) if (p.hit[i]) hits.push('T' + i);
			let s = 'T0[' + hex(p.idx[0], this.lb) + '] = ' + bin(p.ctr[0], 2) + ' · tag hits: ' + (hits.length ? hits.join(', ') : 'none');
			if (p.provider) {
				const k = p.provider;
				s += ' → provider T' + k + ' (L=' + this.L[k] + ', ctr ' + sgn(p.ctr[k]) + ', U ' + p.u[k] + ')';
				if (p.falseHit) s += ' [tag alias: this entry was allocated by ' + brName(p.own[k]) + ']';
				s += ', alternate ' + (p.alt ? 'T' + p.alt : 'T0') + ' says ' + (p.altPred ? 'T' : 'NT');
				if (p.weakNew) s += ' · the provider entry is newly allocated, so the alternate is used';
			} else {
				s += ' → no tagged table hits: the base predictor provides';
			}
			return { text: s + ' → predict ' + (p.taken ? 'T' : 'NT'), warn: p.falseHit };
		}

		describeUpdate(r) {
			const p = r.p;
			let s;
			if (p.provider) {
				s = r.prov ? 'T' + p.provider + ' ctr ' + sgn(r.prov.before) + '→' + sgn(r.prov.after)
					: 'T' + p.provider + ' entry was reallocated before resolve: not trained';
				if (r.uBefore !== undefined) s += ' · U ' + r.uBefore + '→' + r.uAfter + (p.provPred === r.taken ? ' (provider right, alternate wrong)' : ' (provider wrong, alternate right)');
				if (r.altT) s += ' · alternate ' + (p.alt ? 'T' + p.alt + ' ' + sgn(r.altT.before) + '→' + sgn(r.altT.after) : 'T0 ' + bin(r.altT.before, 2) + '→' + bin(r.altT.after, 2)) + ' trained too';
			} else {
				s = 'T0 ' + bin(r.prov.before, 2) + '→' + bin(r.prov.after, 2);
			}
			if (r.alloc) {
				const k = r.alloc;
				s += ' · mispredicted: allocated T' + k + '[' + hex(p.idx[k], this.lt) + '] (L=' + this.L[k] + ') with tag ' + hex(p.tag[k], this.tb) +
					(r.victim >= 0 ? ', replacing an entry of ' + brName(r.victim) : '');
			}
			if (r.blocked) s += ' · mispredicted, but every longer-history entry is still useful: no allocation, their U decay' + (r.decayed.length ? ' (T' + r.decayed.join(', T') + ')' : '');
			if (r.aged) s += ' · periodic reset: the ' + r.aged + ' bit of every U cleared';
			if (r.histWritten) s += ' · GHR ← ' + (r.taken ? 1 : 0) + (r.repaired ? ' (repaired)' : '');
			if (r.inter === 'destructive') s += ' · destructive interference in T0 from ' + brName(p.own[0]);
			return { text: s, warn: r.blocked || (r.mis && p.falseHit) || r.inter === 'destructive' };
		}

		warnings(p) {
			if (p.falseHit) return ['T' + p.provider + ' tag hit on an entry allocated by ' + brName(p.own[p.provider]) + ': tag aliasing'];
			if (p.weakNew) return ['T' + p.provider + ' entry is newly allocated: using the alternate prediction'];
			return [];
		}

		figure(view) {
			const p = view.read, r = view.upd;
			const rOn = !!(p && view.readNow), uOn = !!(r && view.updNow);
			const rk = rOn ? 'rd' : 'dim', uk = uOn ? 'up' : 'dim';   // read annotations fade once they are from an earlier cycle
			const on = function (cond, seq) { return p && cond ? { on: rOn, dim: !rOn, seq: seq } : { dim: true }; };
			const M = this.M, slot = M <= 4 ? 140 : 120, bw = slot - 30;
			const W = Math.max(680, 130 + M * slot + 10);
			const HY = 76, PY = 96, HT = 112, HH = 18, BT = 156, BB = 250, RY = 196, WY = 224, BH = 22, DY = 282, DR = 15;
			const MY0 = 310, MSTEP = 30, MH = 16;
			const src = p ? p.src : -1;
			const up = { on: uOn, dim: !uOn, seq: 4 };
			let s = S.figLabel(10, 8, 'TAGE');

			// History register and the two buses (global history above, PC below, as in Fig. 9).
			s += S.reg({ x: 16, y: HY - 11, w: 88, h: 22, txt: (p ? p.recent : this.hist.text(Math.min(24, this.L[M]))).slice(-10), on: rOn, seq: 0,
				write: r && r.histWritten, seqWrite: 4, readDim: !rOn, writeDim: !uOn });
			s += S.t(16, HY - 16, 'GHR', 'tx sm');
			s += S.t(16, PY + 18, 'PC', 'tx');
			const x0s = [];
			for (let i = 1; i <= M; i++) x0s.push(130 + (i - 1) * slot);
			// History feeds the left input of each hash, the PC the right one; each bus ends at its last tap.
			const hEnd = x0s[M - 1] + bw + 4, pEnd = x0s[M - 1] + bw + 24;
			s += S.wire([[104, HY], [hEnd, HY]], 'rd', Object.assign(on(true, 0), { arrow: false }));
			s += S.wire([[40, PY], [pEnd, PY]], 'rd', Object.assign(on(true, 0), { arrow: false }));

			// T0: the base predictor.
			s += S.wire([[55, PY], [55, BT - 2]], 'rd', on(true, 1));
			s += S.dot(55, PY, rOn ? 'rd' : 'ink');
			const lv0 = this.base.level;
			s += S.rect(20, BT, 70, BB - BT, 'cell s' + lv0);
			s += S.tMid(55, BT + 16, 'Base', 'tx sm') + S.tMid(55, BT + 30, 'predictor', 'tx sm');
			s += S.t(20, BT - 6, 'T0', 'tx');
			if (p) {
				s += S.rect(20, RY, 70, BH, 'cell h' + lv0 + ' pop' + (rOn ? '' : ' stale'), { style: '--seq:2' });
				s += S.tMid(55, RY + 15, bin(p.ctr[0], 2), 'mono on-solid' + (rOn ? '' : ' stale'));
				if (src === 0) s += S.rect(18, RY - 2, 74, BH + 4, 'provider pop' + (rOn ? '' : ' stale'), { style: '--seq:2' });
			}
			if (r && !r.p.provider) {
				const same = p && p.idx[0] === r.p.idx[0];
				s += S.rect(22, (same ? RY : WY) + 2, 66, BH - 4, 'cell-w pop' + (uOn ? '' : ' stale'), { style: '--seq:4' });
				if (!same) s += S.tMid(55, WY + 15, bin(r.prov.after, 2), 'mono v-up');
				s += S.wire([[80, 266], [80, BB + 2]], 'up', up);
			}

			// Tagged tables T1..TM.
			for (let i = 1; i <= M; i++) {
				const x0 = x0s[i - 1], t = this.T[i], lv = t.level;
				const px = Math.round(x0 + 0.14 * bw), cx = Math.round(x0 + 0.5 * bw), tagX = x0 + bw + 14;
				const s1 = Math.round(x0 + 0.28 * bw), s2 = Math.round(x0 + 0.72 * bw);

				// Hashes of PC and H[0:L(i)]: one for the index, one for the tag.
				s += S.wire([[cx - 10, HY], [cx - 10, HT - 2]], 'rd', on(true, 1));
				s += S.wire([[cx + 10, PY], [cx + 10, HT - 2]], 'rd', on(true, 1));
				s += S.wire([[tagX - 10, HY], [tagX - 10, HT - 2]], 'rd', on(true, 1));
				s += S.wire([[tagX + 10, PY], [tagX + 10, HT - 2]], 'rd', on(true, 1));
				[cx - 10, tagX - 10].forEach(function (x) { if (x < hEnd) s += S.dot(x, HY, rOn ? 'rd' : 'ink'); });
				[cx + 10, tagX + 10].forEach(function (x) { if (x < pEnd) s += S.dot(x, PY, rOn ? 'rd' : 'ink'); });
				s += S.hashBox(cx - 22, HT, 44, HH, 'Hash');
				s += S.hashBox(tagX - 22, HT, 44, HH, 'Hash');
				s += S.wire([[cx, HT + HH], [cx, BT - 2]], 'rd', on(true, 1));

				// The table: Pred | Tag | U.
				s += S.rect(x0, BT, bw, BB - BT, 'cell s' + lv);
				s += '<path d="M' + s1 + ',' + BT + ' L' + s1 + ',' + BB + ' M' + s2 + ',' + BT + ' L' + s2 + ',' + BB + '" class="segline"/>';
				s += S.tMid((x0 + s1) / 2, BT + 18, 'Pred', 'tx sm') + S.tMid((s1 + s2) / 2, BT + 18, 'Tag', 'tx sm') + S.tMid((s2 + x0 + bw) / 2, BT + 18, 'U', 'tx sm');
				s += S.t(x0, BT - 6, 'T' + i, 'tx') + S.t(x0 + 22, BT - 6, 'L=' + this.L[i], 'dim');
				if (p) {
					const hit = p.hit[i], st = rOn ? '' : ' stale';
					s += S.rect(x0, RY, bw, BH, 'cell ' + (hit ? 'h' : 'q') + lv + ' pop' + st, { style: '--seq:2' });
					const tc = hit ? 'mono on-solid' + st : 'mono' + st;
					s += S.tMid((x0 + s1) / 2, RY + 15, p.stag[i] >= 0 ? sgn(p.ctr[i]) : '·', tc);
					s += S.tMid((s1 + s2) / 2, RY + 15, p.stag[i] >= 0 ? hex(p.stag[i], this.tb) : 'empty', tc);
					s += S.tMid((s2 + x0 + bw) / 2, RY + 15, p.stag[i] >= 0 ? String(p.u[i]) : '·', tc);
					if (src === i) s += S.rect(x0 - 2, RY - 2, bw + 4, BH + 4, 'provider pop' + st, { style: '--seq:2' });
					if (i === p.provider && p.falseHit) s += S.t(x0 + bw - 12, BT + 18, '⚠', 'warn-glyph');
				}
				// Written entry (trained provider/alternate, or a new allocation).
				if (r) {
					const rp = r.p;
					let what = null;
					if (r.alloc === i) what = 'alloc';
					else if (rp.provider === i && r.prov) what = 'train';
					else if (rp.weakNew && rp.alt === i && r.altT) what = 'train';
					else if (r.blocked && r.decayed.indexOf(i) >= 0) what = 'U−1';
					if (what) {
						const same = p && p.idx[i] === rp.idx[i];
						const y = same ? RY : WY;
						s += S.rect(x0 + 2, y + 2, bw - 4, BH - 4, 'cell-w pop' + (uOn ? '' : ' stale'), { style: '--seq:4' });
						if (!same) {
							const v = this.T[i];
							const e = rp.idx[i];
							s += S.tMid((x0 + s1) / 2, WY + 15, sgn(v.ctr[e]), 'mono v-up') + S.tMid((s1 + s2) / 2, WY + 15, hex(v.tag[e], this.tb), 'mono v-up') +
								S.tMid((s2 + x0 + bw) / 2, WY + 15, String(v.u[e]), 'mono v-up');
						}
						s += S.wire([[x0 + bw - 10, 266], [x0 + bw - 10, BB + 2]], 'up', up);
						s += S.val(x0 + bw - 6, 262, what, what === 'U−1' ? 'warn' : uk);
					}
				}

				// Tag comparison.
				s += S.wire([[cx, BB], [cx, DY - DR - 2]], 'rd', on(true, 2));
				s += S.wire([[tagX, HT + HH], [tagX, DY], [cx + DR + 2, DY]], 'rd', on(true, 1));
				s += S.diamond(cx, DY, DR, p ? (p.hit[i] ? 'cmp-hit' : 'cmp-miss') : '');

				// Mux i: previous result (left input) or Ti's counter (right input), selected by the hit.
				const my = MY0 + (i - 1) * MSTEP, mx1 = x0 - 34, mx2 = x0 + 40;
				const prevX = i === 1 ? 55 : x0s[i - 2] + 3, prevY = i === 1 ? BB : my - MSTEP + MH;
				s += S.wire([[prevX, prevY], [prevX, my - 7], [x0 - 18, my - 7], [x0 - 18, my - 2]], 'rd', on(src < i, 3));
				s += S.wire([[px, BB], [px, my - 2]], 'rd', on(src === i, 3));
				s += S.wire([[cx, DY + DR], [cx, my + MH / 2], [mx2 - 4, my + MH / 2]], 'rd', on(p && p.hit[i], 3));
				s += S.mux(mx1, mx2, my, MH, 12);
			}

			// Final prediction.
			const lastMy = MY0 + (M - 1) * MSTEP + MH, fx = x0s[M - 1] + 3;
			s += S.wire([[fx, lastMy], [fx, lastMy + 24]], 'rd', on(true, 4));
			s += S.tEnd(fx - 8, lastMy + 20, 'Prediction', 'tx');
			if (p) {
				let why = p.provider ? 'provider T' + p.provider : 'base T0';
				if (p.weakNew) why = 'T' + p.provider + ' is new: alternate ' + (p.alt ? 'T' + p.alt : 'T0');
				s += S.val(fx + 8, lastMy + 20, '→ ' + (p.taken ? 'taken' : 'not taken'), rk);
				s += S.val(fx + 8, lastMy + 34, why, rk);
			}
			if (r && r.blocked) s += S.val(16, lastMy + 20, 'allocation blocked', 'warn');
			else if (r && r.alloc) s += S.val(16, lastMy + 20, 'allocated in T' + r.alloc, uk);
			let worst = 1;
			for (let i = 2; i <= M; i++) if (this.T[i].level > this.T[worst].level) worst = i;
			s += S.t(16, lastMy + 56, 'T0: ' + this.base.describe(), 'dim');
			s += S.t(16, lastMy + 72, 'most stressed tagged table, T' + worst + ': ' + this.T[worst].describe(), 'dim');
			s += callouts(view, this);
			return S.svg(W, lastMy + 80, s, 'TAGE predictor');
		}
	}

	const ALPHAS = [1.5, 2, 2.5, 3];
	const URESET = [{ v: 0, label: 'never' }, { v: 2048, label: 'every 2K' }, { v: 8192, label: 'every 8K' }, { v: 32768, label: 'every 32K' }, { v: 131072, label: 'every 128K' }];

	const TAGE_DEF = {
		id: 'TAGE',
		name: 'TAGE',
		title: 'Tagged tables with geometric history lengths',
		group: 'III-E · Geometric history lengths: GEHL (Table IV), TAGE (Fig. 9)',
		figure: 'Fig. 9',
		knobs: [
			{ id: 'M', label: 'M · tagged tables', type: 'int', min: 1, max: 8, def: 4, help: 'Number of tagged components T1..TM (Fig. 9 shows 4).' },
			{ id: 'lt', label: 'tagged entries (log2)', type: 'int', min: 4, max: 12, def: 10, help: 'Each tagged table has 2^value entries.' },
			{ id: 'lb', label: 'base entries (log2)', type: 'int', min: 4, max: 14, def: 12, help: 'The bimodal base predictor T0 has 2^value 2-bit counters.' },
			{ id: 'tb', label: 'tag bits', type: 'int', min: 4, max: 14, def: 9, help: 'Width of each partial tag; narrower tags alias more.' },
			{ id: 'L1', label: 'L(1) · shortest history', type: 'int', min: 1, max: 12, def: 4, help: 'History length of T1.' },
			{ id: 'alpha', label: 'α · length ratio', type: 'choice', options: ALPHAS, def: 2, help: 'L(i) = floor(α^(i-1) · L(1) + 0.5).' },
			{ id: 'ureset', label: 'U reset', type: 'choice', options: URESET, def: 8192, help: 'How often (in resolved branches) every useful counter is aged.' }
		],
		validate: function (k) {
			const L = lengths(k);
			return L[k.M] > MAX_HIST ? 'the longest history would be ' + L[k.M].toLocaleString() + ' bits (limit ' + MAX_HIST + ')' : null;
		},
		create: function (k, opts) { return new TAGE(k, opts); },
		about: 'TAGE keeps a bimodal base predictor and M partially tagged tables indexed with geometrically longer global histories. ' +
			'The longest-history table whose tag matches provides the prediction, so each branch uses just as much history as it needs; ' +
			'useful counters protect entries that beat the alternate prediction, and mispredictions allocate entries in longer-history tables.'
	};

	BP.tage = { TAGE: TAGE_DEF, MAX_HIST };

})(window.BP = window.BP || {});
