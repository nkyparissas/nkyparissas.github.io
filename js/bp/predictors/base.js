/* ==========================================================================
   /bp: building blocks shared by every predictor.

   Hardware tables here are tag-less unless stated, exactly as the paper's
   figures draw them. To report aliasing anyway, every table keeps a shadow
   "owner" per entry (the static branch that last wrote it). The hardware
   would not have this; it exists only so the tool can say who collided.

   Stress: each table turns a conflict rate into one of five levels, using
   thresholds chosen per table type (and overridable per predictor), because
   a shared PHT entry in GAg is normal while a shared BHR row in PAg is not.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const STRESS_NAMES = ['relaxed', 'healthy', 'busy', 'stressed', 'thrashing'];

	// Metric thresholds for levels 1..4 (below the first is level 0).
	const TH = {
		// Fraction of BHR lookups that land on a row last written by another branch.
		alias: [0.004, 0.015, 0.05, 0.15],
		// Fraction of lookups in a tagged table that had to evict another branch's entry.
		evict: [0.004, 0.015, 0.05, 0.15],
		// Fraction of resolved branches that aliasing turned from right to wrong (see CounterTable).
		destructive: [0.002, 0.006, 0.015, 0.04]
	};

	const ALPHA = 1 / 256;   // EWMA weight: roughly the last few hundred events
	const WARM = 24;         // events before a table may leave "relaxed"

	function levelOf(v, th) {
		let l = 0;
		while (l < th.length && v >= th[l]) l++;
		return l;
	}

	function log2(n) { return Math.round(Math.log2(n)); }

	function hex(v, bits) {
		const d = Math.max(1, Math.ceil(bits / 4));
		let s = (v >>> 0).toString(16).toUpperCase();
		while (s.length < d) s = '0' + s;
		return '0x' + s;
	}

	function bin(v, bits) {
		if (bits <= 0) return '';
		let s = (v >>> 0).toString(2);
		while (s.length < bits) s = '0' + s;
		return s.slice(-bits);
	}

	function binShort(v, bits, max) {
		const s = bin(v, bits);
		const m = max || 12;
		return s.length > m ? '…' + s.slice(-(m - 1)) : s;
	}

	// Name of an n-bit field of the PC starting at bit lo, e.g. PC[9:2].
	function pcField(lo, n) {
		if (n <= 0) return '—';
		return n === 1 ? 'PC[' + lo + ']' : 'PC[' + (lo + n - 1) + ':' + lo + ']';
	}

	function fmtBytes(bits) {
		const b = bits / 8;
		if (b < 1024) return (Math.round(b * 10) / 10) + ' B';
		if (b < 1024 * 1024) return (Math.round(b / 102.4) / 10) + ' KiB';
		return (Math.round(b / 104857.6) / 10) + ' MiB';
	}

	function brName(br) { return 'B' + br; }

	// Log text for an interference verdict from CounterTable.noteOutcome.
	function interferenceText(kind, br, prev, taken) {
		if (kind === 'destructive') {
			return ' · destructive interference: ' + brName(prev) + ' had trained this entry; ' + brName(br) +
				'\'s own counter would have said ' + (taken ? 'T' : 'NT');
		}
		if (kind === 'constructive') return ' · constructive interference: sharing with ' + brName(prev) + ' happened to help';
		return '';
	}

	/* ------------------------------------------------------------ undo log */

	// Speculative history updates, newest last, so a mispredict can roll them back.
	class UndoLog {
		constructor() { this.q = []; }
		push(seq, obj, slot, old) { this.q.push({ seq: seq, obj: obj, slot: slot, old: old }); }
		// Undo every update made by branch instances with sequence number >= seq.
		rollback(seq) {
			const q = this.q;
			while (q.length && q[q.length - 1].seq >= seq) {
				const e = q.pop();
				e.obj.restore(e.slot, e.old);
			}
		}
		// Forget updates of instances with sequence number <= seq (they are now architectural).
		commit(seq) {
			const q = this.q;
			let n = 0;
			while (n < q.length && q[n].seq <= seq) n++;
			if (n) q.splice(0, n);
		}
	}

	/* --------------------------------------------------------------- stats */

	class TableStats {
		constructor(name, size, metric, th) {
			this.name = name;
			this.size = size;
			this.metric = metric;
			this.th = th || TH[metric];
			this.lookups = 0;
			this.conflicts = 0;
			this.resolves = 0;
			this.destructive = 0;
			this.constructive = 0;
			this.ew = 0;
			this.touched = 0;
			this.seen = new Uint8Array(size);
		}

		touch(i) {
			if (!this.seen[i]) { this.seen[i] = 1; this.touched++; }
		}

		noteLookup(conflict) {
			this.lookups++;
			if (conflict) this.conflicts++;
			if (this.metric !== 'destructive') {
				const a = Math.max(1 / this.lookups, ALPHA);
				this.ew += ((conflict ? 1 : 0) - this.ew) * a;
			}
		}

		noteResolve(conflict, mis) {
			this.resolves++;
			const d = conflict && mis;
			if (d) this.destructive++;
			if (this.metric === 'destructive') {
				const a = Math.max(1 / this.resolves, ALPHA);
				this.ew += ((d ? 1 : 0) - this.ew) * a;
			}
		}

		get level() {
			const n = this.metric === 'destructive' ? this.resolves : this.lookups;
			if (n < WARM) return 0;
			return levelOf(this.ew, this.th);
		}

		get occupancy() { return this.size ? this.touched / this.size : 0; }

		// Short human summary of the stress metric.
		describe() {
			const pct = function (x) { return (Math.round(x * 1000) / 10) + '%'; };
			const used = pct(this.occupancy) + ' used';
			if (this.metric === 'destructive') {
				const r = this.resolves || 1;
				return used + ' · ' + pct(this.destructive / r) + ' destructive · ' + pct(this.constructive / r) + ' constructive';
			}
			if (this.metric === 'evict') return used + ' · ' + pct(this.lookups ? this.conflicts / this.lookups : 0) + ' evictions';
			return used + ' · ' + pct(this.lookups ? this.conflicts / this.lookups : 0) + ' aliased';
		}
	}

	/* --------------------------------------------------- saturating counters */

	// Interference is classified against an interference-free twin: every branch also
	// trains a private copy of each counter it uses (a shadow, not hardware). Aliasing was
	// destructive when the shared counter was wrong but the private one would have been
	// right, and constructive in the opposite case (survey, Section II-A).
	class CounterTable extends TableStats {
		constructor(entries, bits, name, th) {
			super(name, entries, 'destructive', th);
			this.bits = bits;
			this.max = (1 << bits) - 1;
			this.half = 1 << (bits - 1);
			this.ctr = new Uint8Array(entries).fill(this.half);   // weakly taken
			this.owner = new Int32Array(entries).fill(-1);
			this.priv = new Map();
		}

		read(i, br) {
			const o = this.owner[i];
			const alias = o >= 0 && o !== br;
			this.noteLookup(alias);
			const v = this.ctr[i];
			const pk = br * this.size + i;
			const pv = this.priv.has(pk) ? this.priv.get(pk) : this.half;
			return { v: v, taken: v >= this.half, alias: alias, prev: o, privTaken: pv >= this.half };
		}

		train(i, taken, br) {
			let v = this.ctr[i];
			if (taken) { if (v < this.max) v++; } else if (v > 0) v--;
			this.ctr[i] = v;
			this.owner[i] = br;
			this.touch(i);
			const pk = br * this.size + i;
			let pv = this.priv.has(pk) ? this.priv.get(pk) : this.half;
			if (taken) { if (pv < this.max) pv++; } else if (pv > 0) pv--;
			this.priv.set(pk, pv);
			return v;
		}

		// Classify one resolved prediction; returns 'destructive', 'constructive' or ''.
		noteOutcome(predTaken, privTaken, taken) {
			this.resolves++;
			const d = predTaken !== taken && privTaken === taken;
			const c = predTaken === taken && privTaken !== taken;
			if (d) this.destructive++;
			if (c) this.constructive++;
			const a = Math.max(1 / this.resolves, ALPHA);
			this.ew += ((d ? 1 : 0) - this.ew) * a;
			return d ? 'destructive' : c ? 'constructive' : '';
		}

		fmt(v) { return bin(v, this.bits); }
	}

	/* ------------------------------------------------- branch history tables */

	// sets x ways history registers. One way = tag-less and direct-mapped, so two
	// branches that share a row share (and pollute) one history. More ways = tagged
	// and LRU-replaced, so sharing becomes eviction instead.
	class HistoryTable extends TableStats {
		constructor(sets, ways, bits, name, th) {
			super(name, sets * ways, ways > 1 ? 'evict' : 'alias', th);
			this.sets = sets;
			this.ways = ways;
			this.bits = bits;
			this.mask = bits >= 31 ? 0x7FFFFFFF : (1 << bits) - 1;
			this.tagged = ways > 1;
			this.hist = new Uint32Array(sets * ways);
			this.tag = new Int32Array(sets * ways).fill(-1);
			this.owner = new Int32Array(sets * ways).fill(-1);
			this.lru = new Float64Array(sets * ways);
			this.tick = 0;
		}

		find(set, tagv) {
			if (!this.tagged) return set;
			const b = set * this.ways;
			for (let w = 0; w < this.ways; w++) if (this.tag[b + w] === tagv) return b + w;
			return -1;
		}

		victim(set) {
			const b = set * this.ways;
			let v = b;
			for (let w = 0; w < this.ways; w++) {
				if (this.tag[b + w] < 0) return b + w;
				if (this.lru[b + w] < this.lru[v]) v = b + w;
			}
			return v;
		}

		// Read-only lookup at prediction time. `key` identifies the legitimate owner of a row
		// (the branch for per-address tables, the code block for per-set ones); defaults to br.
		lookup(set, tagv, br, key) {
			if (key === undefined) key = br;
			if (!this.tagged) {
				const o = this.owner[set];
				const alias = o >= 0 && o !== key;
				this.noteLookup(alias);
				return { slot: set, set: set, hit: true, hist: this.hist[set], alias: alias, prev: o, evict: false };
			}
			const s = this.find(set, tagv);
			if (s >= 0) {
				this.noteLookup(false);
				this.lru[s] = ++this.tick;
				return { slot: s, set: set, hit: true, hist: this.hist[s], alias: false, prev: this.owner[s], evict: false };
			}
			const v = this.victim(set);
			const vo = this.owner[v];
			const evict = this.tag[v] >= 0 && vo !== key;
			this.noteLookup(evict);
			return { slot: v, set: set, hit: false, hist: 0, alias: evict, prev: vo, evict: evict };
		}

		// Shift an outcome into the branch's row, allocating it if a tagged table missed.
		shiftIn(set, tagv, bit, br, undo, seq, key) {
			if (key === undefined) key = br;
			let s = this.find(set, tagv), h;
			if (s < 0) { s = this.victim(set); h = 0; } else { h = this.hist[s]; }
			if (undo) undo.push(seq, this, s, { h: this.hist[s], t: this.tag[s], o: this.owner[s] });
			this.tag[s] = this.tagged ? tagv : -1;
			this.hist[s] = ((h << 1) | bit) & this.mask;
			this.owner[s] = key;
			this.lru[s] = ++this.tick;
			this.touch(s);
			return { slot: s, hist: this.hist[s] };
		}

		restore(slot, old) {
			this.hist[slot] = old.h;
			this.tag[slot] = old.t;
			this.owner[slot] = old.o;
		}
	}

	class GlobalHistory {
		constructor(bits, name) {
			this.bits = bits;
			this.name = name || 'GHR';
			this.mask = bits >= 31 ? 0x7FFFFFFF : (1 << bits) - 1;
			this.v = 0;
		}
		shift(bit, undo, seq) {
			if (undo) undo.push(seq, this, 0, this.v);
			this.v = ((this.v << 1) | bit) & this.mask;
			return this.v;
		}
		restore(_slot, old) { this.v = old; }
	}

	/* -------------------------------------------------------------- predictor */

	// Contract for concrete predictors:
	//   lookup(pc, br)            -> prediction record { taken, ... } (no history side effects)
	//   shiftHistory(p, bit, undo) shift `bit` into the histories p used (undo may be null)
	//   train(p, taken)           -> update record for the figure and the log
	//   tables()                  -> TableStats-like objects, for colours and stats
	//   storageBits(), latency    -> budget and lookup latency in cycles
	//   describePredict(p), describeUpdate(u) -> log text
	//   figure(view)              -> SVG markup in the paper's notation
	class Predictor {
		constructor(knobs, opts) {
			this.k = knobs;
			this.spec = !opts || opts.specHistory !== false;
			this.undo = new UndoLog();
			this.latency = 1;
		}

		predict(pc, br, seq) {
			const p = this.lookup(pc, br);
			p.pc = pc;
			p.br = br;
			p.seq = seq;
			if (this.spec) this.shiftHistory(p, p.taken ? 1 : 0, this.undo);
			return p;
		}

		resolve(p, taken, mis) {
			let repaired = false;
			if (this.spec) {
				if (mis) {
					this.undo.rollback(p.seq);
					this.shiftHistory(p, taken ? 1 : 0, null);
					repaired = true;
				} else {
					this.undo.commit(p.seq);
				}
			} else {
				this.shiftHistory(p, taken ? 1 : 0, null);
			}
			const u = this.train(p, taken, mis);
			u.p = p;
			u.taken = taken;
			u.mis = mis;
			u.repaired = repaired;
			return u;
		}

		// Discard speculative history written by instances younger than seq.
		squashAfter(seq) {
			if (this.spec) this.undo.rollback(seq + 1);
		}

		maxLevel() {
			let l = 0;
			this.tables().forEach(function (t) { if (t.level > l) l = t.level; });
			return l;
		}
	}

	BP.base = { STRESS_NAMES, TH, levelOf, log2, hex, bin, binShort, pcField, fmtBytes, brName, interferenceText, UndoLog, TableStats, CounterTable, HistoryTable, GlobalHistory, Predictor };

})(window.BP = window.BP || {});
