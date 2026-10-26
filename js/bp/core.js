/* ==========================================================================
   /bp: cycle-level model of an in-order, single-fetch front-end.

   Stage 0 (Fetch) reads the I-cache, looks up the BTB and asks the direction
   predictor about conditional branches; the next-PC mux picks PC+4, the BTB
   target, a Decode redirect or an Execute redirect. Branches resolve in the
   last stage (Execute), where the predictor is trained and a misprediction
   squashes every younger instruction and redirects fetch.

   The correct path comes from the functional Machine, consumed in order while
   the front-end is on the right path. Once a branch is mispredicted, fetch
   carries on down the wrong path (those instructions are real, predicted and
   squashed later) until the branch reaches Execute.

   A predictor with a 2-cycle lookup delivers a taken prediction one cycle
   late, which costs one fetch bubble per predicted-taken branch.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { Machine } = BP.machine;
	const { TEXT_BASE } = BP.compiler;
	const { hex, brName, log2 } = BP.base;

	const MID_NAMES = ['Rename', 'Dispatch', 'Schedule', 'Reg read', 'Operand', 'Wakeup', 'Select', 'Stage'];

	function stageNames(D) {
		const n = ['Fetch', 'Fetch queue', 'Decode'];
		for (let i = 3; i < D - 2; i++) n.push(MID_NAMES[Math.min(i - 3, MID_NAMES.length - 1)] + (i - 3 >= MID_NAMES.length - 1 ? ' ' + (i + 1) : ''));
		n.push('Issue', 'Execute');
		return n;
	}

	class BTB {
		constructor(entries) {
			this.ideal = !entries;
			this.entries = entries;
			if (this.ideal) return;
			this.ways = Math.min(4, entries);
			this.sets = entries / this.ways;
			this.sb = log2(this.sets);
			this.tag = new Int32Array(entries).fill(-1);
			this.tgt = new Int32Array(entries);
			this.lru = new Float64Array(entries);
			this.tick = 0;
		}

		lookup(pc, ins) {
			if (this.ideal) return { hit: true, target: ins.target };
			const w = pc >>> 2, set = w & (this.sets - 1), tag = w >>> this.sb, b = set * this.ways;
			for (let i = 0; i < this.ways; i++) {
				if (this.tag[b + i] === tag) {
					this.lru[b + i] = ++this.tick;
					return { hit: true, target: this.tgt[b + i] };
				}
			}
			return { hit: false, target: 0 };
		}

		insert(pc, target) {
			if (this.ideal) return;
			const w = pc >>> 2, set = w & (this.sets - 1), tag = w >>> this.sb, b = set * this.ways;
			let v = b;
			for (let i = 0; i < this.ways; i++) {
				if (this.tag[b + i] === tag) { v = b + i; break; }
				if (this.tag[b + i] < 0) { v = b + i; break; }
				if (this.lru[b + i] < this.lru[v]) v = b + i;
			}
			this.tag[v] = tag;
			this.tgt[v] = target;
			this.lru[v] = ++this.tick;
		}
	}

	class Core {
		// fe: { depth, btb (0 = ideal), history: 'spec' | 'resolve', maxInstr }
		constructor(program, def, knobs, fe) {
			this.prog = program;
			this.m = new Machine(program);
			this.def = def;
			this.knobs = knobs;
			this.fe = fe;
			this.D = fe.depth;
			this.names = stageNames(this.D);
			this.decIdx = 2;
			this.bp = def.create(knobs, { specHistory: fe.history !== 'resolve' });
			this.btb = new BTB(fe.btb);
			this.st = new Array(this.D).fill(null);
			this.pc = TEXT_BASE;
			this.onPath = true;
			this.fetchStop = false;
			this.bubbles = 0;
			this.seq = 0;
			this.cycle = 0;
			this.done = false;
			this.error = null;
			this.maxInstr = fe.maxInstr || 5000000;
			this.logOn = true;
			this.log = [];
			this.ev = null;
			this.lastRead = null;
			this.lastUpd = null;
			this.stats = {
				cycles: 0, retired: 0, fetched: 0, branches: 0, mispred: 0, btbMiss: 0,
				decodeRedirects: 0, squashed: 0, latencyBubbles: 0,
				perBranch: program.branches.map(function () { return { n: 0, taken: 0, mis: 0 }; })
			};
		}

		say(cls, stage, text) {
			if (this.logOn) this.log.push({ c: this.cycle, cls: cls, stage: stage, text: text });
		}

		step() {
			if (this.done) return;
			const c = ++this.cycle;
			const st = this.st, D = this.D;
			const ev = { cycle: c, mux: 'seq', fetched: null, predicted: null, btb: null, resolved: null,
				redirect: null, decodeRedirect: null, squashed: [], stall: null, halted: false };
			this.ev = ev;
			for (let i = D - 1; i > 0; i--) st[i] = st[i - 1];
			st[0] = null;
			try {
				if (st[D - 1]) this.execute(st[D - 1], ev);
				const d = st[this.decIdx];
				if (!ev.redirect && d && d.needsDecRedirect) this.decodeRedirect(d, ev);
				if (!ev.redirect && !ev.decodeRedirect && !this.done) this.fetch(ev);
			} catch (e) {
				this.error = e;
				this.done = true;
				this.say('x', 'error', e.message + (e.line ? ' (line ' + e.line + ')' : ''));
			}
			this.stats.cycles = c;
		}

		squash(from, to, ev) {
			let n = 0;
			for (let i = from; i <= to; i++) {
				if (this.st[i]) {
					ev.squashed.push({ stage: i, u: this.st[i] });
					this.st[i] = null;
					n++;
				}
			}
			this.stats.squashed += n;
			return n;
		}

		execute(x, ev) {
			const s = this.stats, ins = x.ins;
			s.retired++;
			if (ins.kind === 'cond') {
				const u = this.bp.resolve(x.pred, x.actualTaken, x.dirMis);
				s.branches++;
				const pb = s.perBranch[ins.brId];
				pb.n++;
				if (x.actualTaken) pb.taken++;
				if (x.dirMis) { s.mispred++; pb.mis++; }
				this.lastUpd = { u: u, cycle: this.cycle };
				ev.resolved = { u: x, upd: u };
				if (this.logOn) {
					const d = this.bp.describeUpdate(u);
					this.say(x.dirMis ? 'x' : 'ok', 'EX', brName(ins.brId) + ' @' + hex(x.pc, 16) + ' resolved ' + (x.actualTaken ? 'T' : 'NT') +
						(x.dirMis ? ', predicted ' + (x.predTaken ? 'T' : 'NT') + ': MISPREDICTED' : ': correct'));
					this.say(d.warn ? 'w' : 'u', 'update', d.text);
				}
			}
			if ((ins.kind === 'cond' && x.actualTaken) || ins.kind === 'jump') this.btb.insert(x.pc, ins.target);
			if (x.mispredict) {
				const n = this.squash(0, this.D - 2, ev);
				this.bp.squashAfter(x.seq);
				this.pc = x.actualNext;
				this.onPath = true;
				this.fetchStop = false;
				this.bubbles = 0;
				ev.redirect = { u: x, target: x.actualNext };
				ev.mux = 'redirect';
				this.say('x', 'EX', 'flush ' + n + ' wrong-path instruction' + (n === 1 ? '' : 's') + ', redirect fetch to ' + hex(x.actualNext, 16) +
					' (' + (this.D - 1) + '-cycle penalty)');
			}
			if (ins.kind === 'halt') {
				this.done = true;
				ev.halted = true;
				this.say('h', 'EX', 'ecall reached Execute: program finished after ' + s.retired.toLocaleString() + ' instructions');
			} else if (s.retired >= this.maxInstr) {
				this.done = true;
				this.error = new Error('stopped at the ' + this.maxInstr.toLocaleString() + '-instruction limit');
				this.say('w', 'EX', this.error.message);
			}
		}

		decodeRedirect(d, ev) {
			d.needsDecRedirect = false;
			const target = d.ins.target;
			const n = this.squash(0, this.decIdx - 1, ev);
			this.bp.squashAfter(d.seq);
			this.pc = target;
			this.fetchStop = false;
			this.bubbles = 0;
			d.predNext = target;
			if (!d.wrong) {
				d.mispredict = d.actualNext !== target;
				this.onPath = !d.mispredict;
			}
			this.stats.decodeRedirects++;
			ev.decodeRedirect = { u: d, target: target };
			ev.mux = 'decode';
			this.say('d', 'DEC', (d.ins.kind === 'cond' ? brName(d.ins.brId) + ' (predicted T)' : d.ins.text) + ' @' + hex(d.pc, 16) +
				': BTB had no target, Decode redirects fetch to ' + hex(target, 16) + ', squashing ' + n);
		}

		fetch(ev) {
			const s = this.stats;
			if (this.fetchStop) { ev.stall = 'halt'; return; }
			if (this.bubbles > 0) {
				this.bubbles--;
				s.latencyBubbles++;
				ev.stall = 'latency';
				return;
			}
			const pc = this.pc;
			const ins = this.m.instrAt(pc);
			if (!ins) { ev.stall = 'nothing to fetch'; this.fetchStop = true; return; }
			const u = { seq: ++this.seq, pc: pc, ins: ins, wrong: !this.onPath, fetchCycle: this.cycle };
			s.fetched++;
			if (this.onPath) {
				const rec = this.m.step();
				u.actualNext = rec.next;
				u.actualTaken = rec.taken;
			}
			let next = pc + 4;
			if (ins.kind === 'cond') {
				const p = this.bp.predict(pc, ins.brId, u.seq);
				u.pred = p;
				u.predTaken = p.taken;
				this.lastRead = { p: p, cycle: this.cycle, wrong: u.wrong };
				ev.predicted = u;
				const bt = this.btb.lookup(pc, ins);
				ev.btb = bt;
				u.btbHit = bt.hit;
				if (p.taken) {
					if (bt.hit) {
						next = bt.target;
						ev.mux = 'btb';
						this.bubbles = this.bp.latency - 1;
					} else {
						u.needsDecRedirect = true;
						if (!u.wrong) s.btbMiss++;
					}
				}
				if (this.logOn) {
					const d = this.bp.describePredict(p);
					this.say(d.warn ? 'w' : (u.wrong ? 'wp' : 'f'), 'F1', (u.wrong ? '[wrong path] ' : '') + brName(ins.brId) + ' @' + hex(pc, 16) + ': ' + d.text);
					if (p.taken && !bt.hit) this.say('d', 'F1', 'BTB miss for ' + brName(ins.brId) + ': no target yet, fetch falls through until Decode');
					if (p.taken && bt.hit && this.bp.latency > 1) {
						this.say('h', 'F1', this.bp.latency + '-cycle lookup (two serial tables): ' + (this.bp.latency - 1) + ' fetch bubble before ' + hex(next, 16));
					}
				}
			} else if (ins.kind === 'jump') {
				const bt = this.btb.lookup(pc, ins);
				ev.btb = bt;
				u.btbHit = bt.hit;
				if (bt.hit) { next = bt.target; ev.mux = 'btb'; }
				else { u.needsDecRedirect = true; if (!u.wrong) s.btbMiss++; }
			} else if (ins.kind === 'halt') {
				this.fetchStop = true;
			}
			u.predNext = next;
			if (!u.wrong) {
				u.mispredict = u.actualNext !== next;
				if (ins.kind === 'cond') u.dirMis = u.predTaken !== u.actualTaken;
				if (u.mispredict) this.onPath = false;
			}
			this.pc = next;
			this.st[0] = u;
			ev.fetched = u;
		}

		run(n) {
			let i = 0;
			while (i < n && !this.done) { this.step(); i++; }
			return i;
		}

		predView() {
			const r = this.lastRead, u = this.lastUpd;
			return {
				read: r ? r.p : null, readNow: !!(r && r.cycle === this.cycle), readCycle: r ? r.cycle : 0, readWrongPath: !!(r && r.wrong),
				upd: u ? u.u : null, updNow: !!(u && u.cycle === this.cycle), updCycle: u ? u.cycle : 0
			};
		}

		summary() {
			const s = this.stats;
			return {
				cycles: s.cycles,
				retired: s.retired,
				ipc: s.cycles ? s.retired / s.cycles : 0,
				branches: s.branches,
				mispred: s.mispred,
				accuracy: s.branches ? 1 - s.mispred / s.branches : 0,
				mpki: s.retired ? (1000 * s.mispred) / s.retired : 0,
				btbMiss: s.btbMiss,
				decodeRedirects: s.decodeRedirects,
				squashed: s.squashed,
				latencyBubbles: s.latencyBubbles,
				lost: Math.max(0, s.cycles - s.retired - (this.D - 1))
			};
		}
	}

	BP.core = { stageNames, Core };

})(window.BP = window.BP || {});
