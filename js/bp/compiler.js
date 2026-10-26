/* ==========================================================================
   /bp: compiler for a small C subset, targeting a RISC-V-flavoured ISA.

   Language: int scalars, static int arrays, if/else, for, while, do-while,
   break, continue, return, ?:, && and || (short-circuit, so each one is a real
   conditional branch), the usual arithmetic, bitwise and comparison operators,
   and rand(lo, hi), which compiles to an inline xorshift on gp. An optional
   `int main() { ... }` wrapper is accepted. Function calls are not: calls and
   returns are a target-prediction problem, outside the paper's scope.

   Loops are rotated (test at the bottom), as gcc -O1 lays them out, so a loop
   branch shows the (1110)^n pattern the survey describes in Section II-A.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const TEXT_BASE = 0x1000;
	const DATA_BASE = 0x10000;
	const MAX_INSTRS = 4096;
	const MAX_DATA_WORDS = 1 << 16;
	const RAND_SEED = 0x2545F491;

	class CompileError extends Error {
		constructor(message, line, col) {
			super(message);
			this.line = line || 0;
			this.col = col || 0;
		}
	}

	const REG_NAMES = [
		'zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1',
		'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
		's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11',
		't3', 't4', 't5', 't6'
	];
	const R = {};
	REG_NAMES.forEach(function (n, i) { R[n] = i; });

	function regName(r) { return REG_NAMES[r]; }

	const VAR_REGS = ['s0', 's1', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11',
		'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7'].map(function (n) { return R[n]; });
	const TMP_REGS = ['t0', 't1', 't2', 't3', 't4', 't5', 't6'].map(function (n) { return R[n]; });
	const RNG = R.gp;

	/* ------------------------------------------------------------------ lexer */

	const KEYWORDS = new Set(['int', 'if', 'else', 'for', 'while', 'do', 'break', 'continue', 'return', 'void']);
	const PUNCT = [
		'<<=', '>>=',
		'&&', '||', '==', '!=', '<=', '>=', '<<', '>>', '++', '--',
		'+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=',
		'(', ')', '{', '}', '[', ']', ';', ',', '=', '+', '-', '*', '/', '%',
		'&', '|', '^', '~', '!', '<', '>', '?', ':'
	];

	function lex(src) {
		const toks = [];
		let i = 0, line = 1, col = 1;
		function adv(n) {
			for (let j = 0; j < n; j++) {
				if (src[i] === '\n') { line++; col = 1; } else { col++; }
				i++;
			}
		}
		while (i < src.length) {
			const c = src[i];
			if (c === ' ' || c === '\t' || c === '\r' || c === '\n') { adv(1); continue; }
			if (c === '/' && src[i + 1] === '/') {
				while (i < src.length && src[i] !== '\n') adv(1);
				continue;
			}
			if (c === '/' && src[i + 1] === '*') {
				const l0 = line, c0 = col;
				adv(2);
				while (i < src.length && !(src[i] === '*' && src[i + 1] === '/')) adv(1);
				if (i >= src.length) throw new CompileError('unterminated comment', l0, c0);
				adv(2);
				continue;
			}
			if (c >= '0' && c <= '9') {
				const m = /^(0[xX][0-9a-fA-F]+|[0-9]+)/.exec(src.slice(i));
				const v = Number(m[0]);
				if (v > 0xFFFFFFFF) throw new CompileError('number too large: ' + m[0], line, col);
				toks.push({ t: 'num', v: v | 0, line: line, col: col });
				adv(m[0].length);
				if (/[A-Za-z_]/.test(src[i] || '')) throw new CompileError('malformed number', line, col);
				continue;
			}
			if (/[A-Za-z_]/.test(c)) {
				const m = /^[A-Za-z_][A-Za-z0-9_]*/.exec(src.slice(i));
				toks.push({ t: KEYWORDS.has(m[0]) ? 'kw' : 'id', v: m[0], line: line, col: col });
				adv(m[0].length);
				continue;
			}
			let p = null;
			for (let k = 0; k < PUNCT.length; k++) {
				if (src.startsWith(PUNCT[k], i)) { p = PUNCT[k]; break; }
			}
			if (!p) throw new CompileError('unexpected character \'' + c + '\'', line, col);
			toks.push({ t: 'p', v: p, line: line, col: col });
			adv(p.length);
		}
		toks.push({ t: 'eof', v: '', line: line, col: col });
		return toks;
	}

	/* ----------------------------------------------------------------- parser */

	const ASSIGN_OPS = new Set(['=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>=']);
	const LEVELS = [['||'], ['&&'], ['|'], ['^'], ['&'], ['==', '!='], ['<', '<=', '>', '>='], ['<<', '>>'], ['+', '-'], ['*', '/', '%']];

	function foldBinary(op, a, b) {
		switch (op) {
			case '+': return (a + b) | 0;
			case '-': return (a - b) | 0;
			case '*': return Math.imul(a, b);
			case '/': return b === 0 ? null : (a / b) | 0;
			case '%': return b === 0 ? null : (a % b) | 0;
			case '&': return a & b;
			case '|': return a | b;
			case '^': return a ^ b;
			case '<<': return a << (b & 31);
			case '>>': return a >> (b & 31);
			case '<': return a < b ? 1 : 0;
			case '<=': return a <= b ? 1 : 0;
			case '>': return a > b ? 1 : 0;
			case '>=': return a >= b ? 1 : 0;
			case '==': return a === b ? 1 : 0;
			case '!=': return a !== b ? 1 : 0;
		}
		return null;
	}

	class Parser {
		constructor(toks) { this.toks = toks; this.p = 0; }

		peek(o) { return this.toks[this.p + (o || 0)]; }
		next() { return this.toks[this.p++]; }
		is(v, o) { const t = this.peek(o); return (t.t === 'p' || t.t === 'kw') && t.v === v; }
		accept(v) { if (this.is(v)) { return this.next(); } return null; }
		expect(v) {
			if (this.is(v)) return this.next();
			const t = this.peek();
			throw new CompileError('expected \'' + v + '\' but found ' + describe(t), t.line, t.col);
		}

		program() {
			const body = [];
			while (this.peek().t !== 'eof') {
				if ((this.is('int') || this.is('void')) && this.peek(1).t === 'id' && this.is('(', 2)) {
					const name = this.peek(1);
					if (name.v !== 'main') {
						throw new CompileError('only main() may be defined: function calls are outside this ' +
							'tool\'s scope (they need target prediction)', name.line, name.col);
					}
					this.p += 3;
					this.accept('void');
					this.expect(')');
					const blk = this.block();
					blk.isMain = true;
					body.push(blk);
					continue;
				}
				body.push(this.statement());
			}
			return { k: 'block', body: body, line: 1 };
		}

		block() {
			const t = this.expect('{');
			const body = [];
			while (!this.is('}')) {
				if (this.peek().t === 'eof') throw new CompileError('missing \'}\'', t.line, t.col);
				body.push(this.statement());
			}
			this.next();
			return { k: 'block', body: body, line: t.line };
		}

		statement() {
			const t = this.peek();
			if (this.is('{')) return this.block();
			if (this.is('int')) { const d = this.decl(); this.expect(';'); return d; }
			if (this.accept('if')) {
				this.expect('(');
				const cond = this.expr();
				this.expect(')');
				const then = this.statement();
				const els = this.accept('else') ? this.statement() : null;
				return { k: 'if', cond: cond, then: then, els: els, line: t.line };
			}
			if (this.accept('while')) {
				this.expect('(');
				const cond = this.expr();
				this.expect(')');
				return { k: 'while', cond: cond, body: this.statement(), line: t.line };
			}
			if (this.accept('do')) {
				const body = this.statement();
				const w = this.expect('while');
				this.expect('(');
				const cond = this.expr();
				this.expect(')');
				this.expect(';');
				return { k: 'do', cond: cond, body: body, line: t.line, condLine: w.line };
			}
			if (this.accept('for')) {
				this.expect('(');
				let init = null, cond = null, step = null;
				if (!this.is(';')) init = this.is('int') ? this.decl() : { k: 'expr', e: this.expr(), line: t.line };
				this.expect(';');
				if (!this.is(';')) cond = this.expr();
				this.expect(';');
				if (!this.is(')')) step = this.expr();
				this.expect(')');
				return { k: 'for', init: init, cond: cond, step: step, body: this.statement(), line: t.line };
			}
			if (this.accept('break')) { this.expect(';'); return { k: 'break', line: t.line }; }
			if (this.accept('continue')) { this.expect(';'); return { k: 'continue', line: t.line }; }
			if (this.accept('return')) {
				let e = null;
				if (!this.is(';')) e = this.expr();
				this.expect(';');
				return { k: 'return', e: e, line: t.line };
			}
			if (this.accept(';')) return { k: 'empty', line: t.line };
			const e = this.expr();
			this.expect(';');
			return { k: 'expr', e: e, line: t.line };
		}

		decl() {
			const t = this.expect('int');
			const vars = [];
			do {
				const id = this.next();
				if (id.t !== 'id') throw new CompileError('expected a variable name', id.line, id.col);
				let size = null, init = null;
				if (this.accept('[')) {
					const n = this.expr();
					if (n.k !== 'num' || n.v <= 0) {
						throw new CompileError('array size must be a positive constant', id.line, id.col);
					}
					size = n.v;
					this.expect(']');
				}
				if (this.accept('=')) {
					if (size !== null && this.is('{')) {
						this.next();
						const vals = [];
						while (!this.is('}')) {
							const e = this.assign();
							if (e.k !== 'num') throw new CompileError('array initialisers must be constants', e.line, e.col);
							vals.push(e.v);
							if (!this.accept(',')) break;
						}
						this.expect('}');
						if (vals.length > size) throw new CompileError('too many initialisers for ' + id.v, id.line, id.col);
						init = { k: 'list', vals: vals };
					} else {
						init = this.assign();
						if (size !== null && !(init.k === 'call' && init.name === 'rand')) {
							throw new CompileError('an array takes { ... } or rand(lo, hi) as its initialiser', id.line, id.col);
						}
					}
				}
				vars.push({ name: id.v, size: size, init: init, line: id.line, col: id.col });
			} while (this.accept(','));
			return { k: 'decl', vars: vars, line: t.line };
		}

		expr() {
			let e = this.assign();
			while (this.is(',')) {
				const t = this.next();
				e = { k: 'comma', a: e, b: this.assign(), line: t.line, col: t.col };
			}
			return e;
		}

		assign() {
			const lhs = this.ternary();
			const t = this.peek();
			if (t.t === 'p' && ASSIGN_OPS.has(t.v)) {
				this.next();
				if (lhs.k !== 'var' && lhs.k !== 'index') throw new CompileError('cannot assign to this expression', t.line, t.col);
				return { k: 'assign', op: t.v, target: lhs, value: this.assign(), line: t.line, col: t.col };
			}
			return lhs;
		}

		ternary() {
			const c = this.binary(0);
			if (this.is('?')) {
				const t = this.next();
				const a = this.expr();
				this.expect(':');
				const b = this.ternary();
				if (c.k === 'num') return c.v ? a : b;
				return { k: 'cond', c: c, a: a, b: b, line: t.line, col: t.col };
			}
			return c;
		}

		binary(level) {
			if (level >= LEVELS.length) return this.unary();
			let a = this.binary(level + 1);
			for (;;) {
				const t = this.peek();
				if (t.t !== 'p' || LEVELS[level].indexOf(t.v) < 0) return a;
				this.next();
				const b = this.binary(level + 1);
				if (t.v === '&&' || t.v === '||') {
					a = { k: 'logic', op: t.v, a: a, b: b, line: t.line, col: t.col };
				} else if (a.k === 'num' && b.k === 'num' && foldBinary(t.v, a.v, b.v) !== null) {
					a = { k: 'num', v: foldBinary(t.v, a.v, b.v), line: a.line, col: a.col };
				} else {
					if ((t.v === '/' || t.v === '%') && b.k === 'num' && b.v === 0) {
						throw new CompileError('division by zero', t.line, t.col);
					}
					a = { k: 'bin', op: t.v, a: a, b: b, line: t.line, col: t.col };
				}
			}
		}

		unary() {
			const t = this.peek();
			if (t.t === 'p' && (t.v === '-' || t.v === '!' || t.v === '~' || t.v === '+')) {
				this.next();
				const a = this.unary();
				if (t.v === '+') return a;
				if (a.k === 'num') {
					const v = t.v === '-' ? (-a.v) | 0 : t.v === '!' ? (a.v ? 0 : 1) : ~a.v;
					return { k: 'num', v: v, line: t.line, col: t.col };
				}
				return { k: 'un', op: t.v, a: a, line: t.line, col: t.col };
			}
			if (t.t === 'p' && (t.v === '++' || t.v === '--')) {
				this.next();
				const a = this.unary();
				if (a.k !== 'var' && a.k !== 'index') throw new CompileError('cannot apply ' + t.v + ' here', t.line, t.col);
				return { k: 'incdec', op: t.v, prefix: true, target: a, line: t.line, col: t.col };
			}
			return this.postfix();
		}

		postfix() {
			let e = this.primary();
			for (;;) {
				const t = this.peek();
				if (this.is('[')) {
					this.next();
					if (e.k !== 'var') throw new CompileError('only named arrays can be indexed', t.line, t.col);
					const idx = this.expr();
					this.expect(']');
					e = { k: 'index', name: e.name, idx: idx, line: t.line, col: e.col };
				} else if (this.is('++') || this.is('--')) {
					this.next();
					if (e.k !== 'var' && e.k !== 'index') throw new CompileError('cannot apply ' + t.v + ' here', t.line, t.col);
					e = { k: 'incdec', op: t.v, prefix: false, target: e, line: t.line, col: t.col };
				} else {
					return e;
				}
			}
		}

		primary() {
			const t = this.next();
			if (t.t === 'num') return { k: 'num', v: t.v, line: t.line, col: t.col };
			if (t.t === 'id') {
				if (this.is('(')) {
					this.next();
					const args = [];
					while (!this.is(')')) {
						args.push(this.assign());
						if (!this.accept(',')) break;
					}
					this.expect(')');
					if (t.v !== 'rand') {
						throw new CompileError('function calls are not supported (only rand(lo, hi)); calls and ' +
							'returns need target prediction, which is outside the paper\'s scope', t.line, t.col);
					}
					if (args.length !== 2 || args[0].k !== 'num' || args[1].k !== 'num') {
						throw new CompileError('rand takes two constants: rand(lo, hi)', t.line, t.col);
					}
					if (args[1].v < args[0].v) throw new CompileError('rand(lo, hi) needs lo <= hi', t.line, t.col);
					return { k: 'call', name: 'rand', lo: args[0].v, hi: args[1].v, line: t.line, col: t.col };
				}
				return { k: 'var', name: t.v, line: t.line, col: t.col };
			}
			if (t.t === 'p' && t.v === '(') {
				const e = this.expr();
				this.expect(')');
				return e;
			}
			throw new CompileError('unexpected ' + describe(t), t.line, t.col);
		}
	}

	function describe(t) {
		if (t.t === 'eof') return 'end of program';
		if (t.t === 'num') return 'number ' + t.v;
		return '\'' + t.v + '\'';
	}

	/* ---------------------------------------------------------------- codegen */

	// Branch relations: canonical op and whether operands are swapped.
	const REL = {
		'==': { op: 'beq', swap: false, neg: '!=' },
		'!=': { op: 'bne', swap: false, neg: '==' },
		'<': { op: 'blt', swap: false, neg: '>=' },
		'>=': { op: 'bge', swap: false, neg: '<' },
		'>': { op: 'blt', swap: true, neg: '<=' },
		'<=': { op: 'bge', swap: true, neg: '>' }
	};
	const PSEUDO_BR = { '>': 'bgt', '<=': 'ble' };
	const ZERO_RS2 = { '==': 'beqz', '!=': 'bnez', '<': 'bltz', '>=': 'bgez', '>': 'bgtz', '<=': 'blez' };
	const ZERO_RS1 = { '==': 'beqz', '!=': 'bnez', '<': 'bgtz', '>=': 'blez', '>': 'bltz', '<=': 'bgez' };

	const R_OPS = { '+': 'add', '-': 'sub', '*': 'mul', '/': 'div', '%': 'rem', '&': 'and', '|': 'or', '^': 'xor', '<<': 'sll', '>>': 'sra' };
	const I_OPS = { '+': 'addi', '&': 'andi', '|': 'ori', '^': 'xori', '<<': 'slli', '>>': 'srai' };
	const COMMUTATIVE = new Set(['+', '*', '&', '|', '^']);

	function fitsImm(v) { return v >= -2048 && v <= 2047; }

	function xorshift(s) {
		s ^= s << 13;
		s ^= s >>> 17;
		s ^= s << 5;
		return s | 0;
	}

	class Gen {
		constructor() {
			this.code = [];
			this.nLabels = 0;
			this.scopes = [new Map()];
			this.freeVar = VAR_REGS.slice();
			this.freeTmp = TMP_REGS.slice();
			this.loops = [];
			this.data = [];
			this.arrays = [];
			this.scalars = [];
			this.line = 1;
			this.dataSeed = 0x1234567;
		}

		label() { return '.L' + (++this.nLabels); }
		place(l) { this.code.push({ label: l }); }
		emit(ins) {
			ins.line = this.line;
			this.code.push(ins);
			return ins;
		}

		tmp(node) {
			if (!this.freeTmp.length) {
				throw new CompileError('expression too complex: ran out of temporary registers', node.line, node.col);
			}
			return this.freeTmp.shift();
		}
		release(op) { if (op && op.tmp) this.freeTmp.unshift(op.reg); }
		isTmp(r) { return TMP_REGS.indexOf(r) >= 0; }

		lookup(name, node) {
			for (let i = this.scopes.length - 1; i >= 0; i--) {
				const s = this.scopes[i].get(name);
				if (s) return s;
			}
			throw new CompileError('\'' + name + '\' is not declared', node.line, node.col);
		}

		pushScope() { this.scopes.push(new Map()); }
		popScope() {
			const s = this.scopes.pop();
			s.forEach((sym) => { if (sym.kind === 'scalar') this.freeVar.unshift(sym.reg); });
		}

		/* -------- statements -------- */

		stmt(n) {
			this.line = n.line;
			switch (n.k) {
				case 'block':
					// main()'s body shares the program scope, so its variables count as top level.
					if (!n.isMain) this.pushScope();
					n.body.forEach((s) => this.stmt(s));
					if (!n.isMain) this.popScope();
					return;
				case 'decl': return this.decl(n);
				case 'expr': this.effect(n.e); return;
				case 'empty': return;
				case 'if': {
					const lElse = this.label();
					this.line = n.cond.line;
					this.branch(n.cond, lElse, false);
					this.stmt(n.then);
					if (n.els) {
						const lEnd = this.label();
						this.line = n.line;
						this.emit({ op: 'j', target: lEnd });
						this.place(lElse);
						this.stmt(n.els);
						this.place(lEnd);
					} else {
						this.place(lElse);
					}
					return;
				}
				case 'while':
					return this.loop(n, n.cond, null, n.body, true);
				case 'do':
					return this.loop(n, n.cond, null, n.body, false);
				case 'for':
					this.pushScope();
					if (n.init) this.stmt(n.init);
					this.loop(n, n.cond, n.step, n.body, true);
					this.popScope();
					return;
				case 'break':
				case 'continue': {
					if (!this.loops.length) throw new CompileError(n.k + ' outside a loop', n.line, 1);
					const l = this.loops[this.loops.length - 1];
					this.emit({ op: 'j', target: n.k === 'break' ? l.brk : l.cont });
					return;
				}
				case 'return':
					if (n.e) this.effect(n.e);
					this.line = n.line;
					this.emit({ op: 'halt' });
					return;
			}
			throw new CompileError('unsupported statement', n.line, 1);
		}

		// Rotated loop: jump to the test at the bottom, which branches back while true.
		loop(n, cond, step, body, testFirst) {
			const lBody = this.label(), lCont = this.label(), lBrk = this.label();
			const forever = !cond || (cond.k === 'num' && cond.v !== 0);
			const never = cond && cond.k === 'num' && cond.v === 0;
			const lTest = step ? this.label() : lCont;
			this.line = n.line;
			if (testFirst && !forever) this.emit({ op: 'j', target: lTest });
			this.place(lBody);
			this.loops.push({ brk: lBrk, cont: lCont });
			this.stmt(body);
			this.loops.pop();
			this.place(lCont);
			if (step) {
				this.line = n.line;
				this.effect(step);
				this.place(lTest);
			}
			this.line = cond ? cond.line : n.line;
			if (n.k === 'do' && n.condLine) this.line = n.condLine;
			if (forever) this.emit({ op: 'j', target: lBody });
			else if (!never) this.branch(cond, lBody, true);
			this.place(lBrk);
		}

		decl(n) {
			const scope = this.scopes[this.scopes.length - 1];
			n.vars.forEach((v) => {
				this.line = v.line;
				if (scope.has(v.name)) throw new CompileError('\'' + v.name + '\' is already declared here', v.line, v.col);
				if (v.size !== null) {
					if (this.data.length + v.size > MAX_DATA_WORDS) {
						throw new CompileError('arrays exceed the ' + MAX_DATA_WORDS + '-word data segment', v.line, v.col);
					}
					const sym = { kind: 'array', name: v.name, addr: DATA_BASE + 4 * this.data.length, size: v.size, line: v.line };
					for (let i = 0; i < v.size; i++) {
						let w = 0;
						if (v.init && v.init.k === 'list' && i < v.init.vals.length) w = v.init.vals[i];
						if (v.init && v.init.k === 'call') {
							this.dataSeed = xorshift(this.dataSeed);
							w = v.init.lo + ((this.dataSeed >>> 0) % (v.init.hi - v.init.lo + 1));
						}
						this.data.push(w | 0);
					}
					scope.set(v.name, sym);
					this.arrays.push(sym);
					return;
				}
				if (!this.freeVar.length) {
					throw new CompileError('too many live variables (at most ' + VAR_REGS.length + ' scalars fit in registers)', v.line, v.col);
				}
				const sym = { kind: 'scalar', name: v.name, reg: this.freeVar.shift(), line: v.line, top: this.scopes.length <= 2 };
				if (v.init) this.into(v.init, sym.reg);
				else this.emit({ op: 'li', rd: sym.reg, imm: 0 });
				scope.set(v.name, sym);
				this.scalars.push(sym);
			});
		}

		/* -------- conditions -------- */

		// Jump to `target` when `e` is true (jumpIfTrue) or false (!jumpIfTrue); else fall through.
		branch(e, target, jumpIfTrue) {
			if (e.k === 'num') {
				if ((e.v !== 0) === jumpIfTrue) this.emit({ op: 'j', target: target });
				return;
			}
			if (e.k === 'un' && e.op === '!') return this.branch(e.a, target, !jumpIfTrue);
			if (e.k === 'logic') {
				const isAnd = e.op === '&&';
				if (isAnd !== jumpIfTrue) {
					// &&, jump-if-false: either false jumps. ||, jump-if-true: either true jumps.
					this.branch(e.a, target, jumpIfTrue);
					this.branch(e.b, target, jumpIfTrue);
				} else {
					const skip = this.label();
					this.branch(e.a, skip, !jumpIfTrue);
					this.branch(e.b, target, jumpIfTrue);
					this.place(skip);
				}
				return;
			}
			if (e.k === 'bin' && REL[e.op]) {
				const rel = jumpIfTrue ? e.op : REL[e.op].neg;
				const a = this.value(e.a), b = this.value(e.b);
				this.emitBranch(rel, a.reg, b.reg, target, e);
				this.release(b);
				this.release(a);
				return;
			}
			const v = this.value(e);
			this.emitBranch(jumpIfTrue ? '!=' : '==', v.reg, 0, target, e);
			this.release(v);
		}

		emitBranch(rel, ra, rb, target, node) {
			const r = REL[rel];
			const rs1 = r.swap ? rb : ra, rs2 = r.swap ? ra : rb;
			let disp, ops;
			if (rb === 0) { disp = ZERO_RS2[rel]; ops = [ra]; }
			else if (ra === 0) { disp = ZERO_RS1[rel]; ops = [rb]; }
			else { disp = PSEUDO_BR[rel] || r.op; ops = [ra, rb]; }
			this.emit({ op: r.op, rs1: rs1, rs2: rs2, target: target, disp: disp, dops: ops, col: node.col });
		}

		/* -------- expressions -------- */

		// Evaluate for side effects only.
		effect(e) {
			if (e.k === 'assign') { const r = this.assign(e, false); this.release(r); return; }
			if (e.k === 'incdec') { this.incdec(e, null); return; }
			if (e.k === 'comma') { this.effect(e.a); this.effect(e.b); return; }
			if (e.k === 'cond') {
				const lElse = this.label(), lEnd = this.label();
				this.branch(e.c, lElse, false);
				this.effect(e.a);
				this.emit({ op: 'j', target: lEnd });
				this.place(lElse);
				this.effect(e.b);
				this.place(lEnd);
				return;
			}
			if (e.k === 'logic') {
				const lEnd = this.label();
				this.branch(e.a, lEnd, e.op === '||');
				this.effect(e.b);
				this.place(lEnd);
				return;
			}
			const v = this.value(e);
			this.release(v);
		}

		// Value in some register: { reg, tmp }.
		value(e) {
			if (e.k === 'reg') return { reg: e.reg, tmp: false };
			if (e.k === 'num' && e.v === 0) return { reg: 0, tmp: false };
			if (e.k === 'var') {
				const s = this.lookup(e.name, e);
				if (s.kind !== 'scalar') throw new CompileError('\'' + e.name + '\' is an array; index it', e.line, e.col);
				return { reg: s.reg, tmp: false };
			}
			if (e.k === 'assign') return this.assign(e, true);
			const t = this.tmp(e);
			this.into(e, t);
			return { reg: t, tmp: true };
		}

		// Evaluate e into register d.
		into(e, d) {
			switch (e.k) {
				case 'num':
					this.emit({ op: 'li', rd: d, imm: e.v });
					return;
				case 'var': {
					const v = this.value(e);
					if (v.reg !== d) this.emit({ op: 'addi', rd: d, rs1: v.reg, imm: 0, disp: 'mv' });
					return;
				}
				case 'index': {
					const a = this.addr(e);
					this.emit({ op: 'lw', rd: d, rs1: a.reg, imm: a.off, arr: a.sym });
					this.release(a);
					return;
				}
				case 'un': {
					const a = this.value(e.a);
					if (e.op === '-') this.emit({ op: 'sub', rd: d, rs1: 0, rs2: a.reg, disp: 'neg' });
					else if (e.op === '~') this.emit({ op: 'xori', rd: d, rs1: a.reg, imm: -1, disp: 'not' });
					else this.emit({ op: 'sltiu', rd: d, rs1: a.reg, imm: 1, disp: 'seqz' });
					this.release(a);
					return;
				}
				case 'bin': return this.binop(e, d);
				case 'call': return this.rand(e, d);
				case 'comma':
					this.effect(e.a);
					this.into(e.b, d);
					return;
				case 'assign':
				case 'incdec':
				case 'logic':
				case 'cond': {
					// These may read d's variable while writing, so go through a temporary when d is a variable.
					if (!this.isTmp(d)) {
						const t = this.tmp(e);
						this.into(e, t);
						this.emit({ op: 'addi', rd: d, rs1: t, imm: 0, disp: 'mv' });
						this.freeTmp.unshift(t);
						return;
					}
					if (e.k === 'assign') {
						const r = this.assign(e, true);
						if (r.reg !== d) this.emit({ op: 'addi', rd: d, rs1: r.reg, imm: 0, disp: 'mv' });
						this.release(r);
						return;
					}
					if (e.k === 'incdec') return this.incdec(e, d);
					if (e.k === 'logic') {
						const lEnd = this.label();
						this.emit({ op: 'li', rd: d, imm: 0 });
						this.branch(e, lEnd, false);
						this.emit({ op: 'li', rd: d, imm: 1 });
						this.place(lEnd);
						return;
					}
					const lElse = this.label(), lEnd = this.label();
					this.branch(e.c, lElse, false);
					this.into(e.a, d);
					this.emit({ op: 'j', target: lEnd });
					this.place(lElse);
					this.into(e.b, d);
					this.place(lEnd);
					return;
				}
			}
			throw new CompileError('unsupported expression', e.line, e.col);
		}

		binop(e, d) {
			const op = e.op;
			if (REL[op]) {
				const a = this.value(e.a), b = this.value(e.b);
				switch (op) {
					case '<': this.emit({ op: 'slt', rd: d, rs1: a.reg, rs2: b.reg }); break;
					case '>': this.emit({ op: 'slt', rd: d, rs1: b.reg, rs2: a.reg }); break;
					case '<=':
						this.emit({ op: 'slt', rd: d, rs1: b.reg, rs2: a.reg });
						this.emit({ op: 'xori', rd: d, rs1: d, imm: 1 });
						break;
					case '>=':
						this.emit({ op: 'slt', rd: d, rs1: a.reg, rs2: b.reg });
						this.emit({ op: 'xori', rd: d, rs1: d, imm: 1 });
						break;
					case '==':
						this.emit({ op: 'sub', rd: d, rs1: a.reg, rs2: b.reg });
						this.emit({ op: 'sltiu', rd: d, rs1: d, imm: 1, disp: 'seqz' });
						break;
					case '!=':
						this.emit({ op: 'sub', rd: d, rs1: a.reg, rs2: b.reg });
						this.emit({ op: 'sltu', rd: d, rs1: 0, rs2: d, disp: 'snez' });
						break;
				}
				this.release(b);
				this.release(a);
				return;
			}
			let lhs = e.a, rhs = e.b;
			if (lhs.k === 'num' && rhs.k !== 'num' && COMMUTATIVE.has(op)) { lhs = e.b; rhs = e.a; }
			if (rhs.k === 'num') {
				let imm = rhs.v, iop = I_OPS[op];
				if (op === '-') { iop = 'addi'; imm = -imm; }
				if (op === '<<' || op === '>>') imm &= 31;
				if (iop && fitsImm(imm)) {
					const a = this.value(lhs);
					this.emit({ op: iop, rd: d, rs1: a.reg, imm: imm });
					this.release(a);
					return;
				}
			}
			const a = this.value(lhs), b = this.value(rhs);
			this.emit({ op: R_OPS[op], rd: d, rs1: a.reg, rs2: b.reg });
			this.release(b);
			this.release(a);
		}

		// rand(lo, hi): xorshift32 on gp, then lo + gp % span.
		rand(e, d) {
			this.usesRand = true;
			const t = this.tmp(e);
			this.emit({ op: 'slli', rd: t, rs1: RNG, imm: 13 });
			this.emit({ op: 'xor', rd: RNG, rs1: RNG, rs2: t });
			this.emit({ op: 'srli', rd: t, rs1: RNG, imm: 17 });
			this.emit({ op: 'xor', rd: RNG, rs1: RNG, rs2: t });
			this.emit({ op: 'slli', rd: t, rs1: RNG, imm: 5 });
			this.emit({ op: 'xor', rd: RNG, rs1: RNG, rs2: t });
			this.emit({ op: 'li', rd: t, imm: (e.hi - e.lo + 1) | 0 });
			this.emit({ op: 'remu', rd: d, rs1: RNG, rs2: t });
			if (e.lo !== 0) {
				if (fitsImm(e.lo)) this.emit({ op: 'addi', rd: d, rs1: d, imm: e.lo });
				else {
					this.emit({ op: 'li', rd: t, imm: e.lo });
					this.emit({ op: 'add', rd: d, rs1: d, rs2: t });
				}
			}
			this.freeTmp.unshift(t);
		}

		// Address of a[idx]: { sym, reg, off, tmp }.
		addr(e) {
			const sym = this.lookup(e.name, e);
			if (sym.kind !== 'array') throw new CompileError('\'' + e.name + '\' is not an array', e.line, e.col);
			if (e.idx.k === 'num') {
				if (e.idx.v < 0 || e.idx.v >= sym.size) {
					throw new CompileError('index ' + e.idx.v + ' is outside ' + e.name + '[' + sym.size + ']', e.line, e.col);
				}
				return { sym: sym, reg: 0, off: 4 * e.idx.v, tmp: false };
			}
			const i = this.value(e.idx);
			const t = i.tmp ? i.reg : this.tmp(e);
			this.emit({ op: 'slli', rd: t, rs1: i.reg, imm: 2 });
			return { sym: sym, reg: t, off: 0, tmp: true };
		}

		assign(e, wantValue) {
			const tgt = e.target;
			const bop = e.op === '=' ? null : e.op.slice(0, -1);
			if (tgt.k === 'var') {
				const s = this.lookup(tgt.name, tgt);
				if (s.kind !== 'scalar') throw new CompileError('cannot assign to array \'' + tgt.name + '\'', tgt.line, tgt.col);
				const rhs = bop ? { k: 'bin', op: bop, a: tgt, b: e.value, line: e.line, col: e.col } : e.value;
				if (bop && (bop === '/' || bop === '%') && e.value.k === 'num' && e.value.v === 0) {
					throw new CompileError('division by zero', e.line, e.col);
				}
				this.into(rhs, s.reg);
				return { reg: s.reg, tmp: false };
			}
			const a = this.addr(tgt);
			let v;
			if (bop) {
				const t = this.tmp(e);
				this.emit({ op: 'lw', rd: t, rs1: a.reg, imm: a.off, arr: a.sym });
				this.binop({ k: 'bin', op: bop, a: { k: 'reg', reg: t }, b: e.value, line: e.line, col: e.col }, t);
				v = { reg: t, tmp: true };
			} else {
				v = this.value(e.value);
			}
			this.emit({ op: 'sw', rs1: a.reg, rs2: v.reg, imm: a.off, arr: a.sym });
			this.release(a);
			if (!wantValue) { this.release(v); return { reg: 0, tmp: false }; }
			return v;
		}

		incdec(e, d) {
			const delta = e.op === '++' ? 1 : -1;
			const tgt = e.target;
			if (tgt.k === 'var') {
				const s = this.lookup(tgt.name, tgt);
				if (s.kind !== 'scalar') throw new CompileError('cannot modify array \'' + tgt.name + '\'', tgt.line, tgt.col);
				if (d !== null && !e.prefix) this.emit({ op: 'addi', rd: d, rs1: s.reg, imm: 0, disp: 'mv' });
				this.emit({ op: 'addi', rd: s.reg, rs1: s.reg, imm: delta });
				if (d !== null && e.prefix) this.emit({ op: 'addi', rd: d, rs1: s.reg, imm: 0, disp: 'mv' });
				return;
			}
			const a = this.addr(tgt);
			const t = this.tmp(e);
			this.emit({ op: 'lw', rd: t, rs1: a.reg, imm: a.off, arr: a.sym });
			if (d !== null && !e.prefix) this.emit({ op: 'addi', rd: d, rs1: t, imm: 0, disp: 'mv' });
			this.emit({ op: 'addi', rd: t, rs1: t, imm: delta });
			if (d !== null && e.prefix) this.emit({ op: 'addi', rd: d, rs1: t, imm: 0, disp: 'mv' });
			this.emit({ op: 'sw', rs1: a.reg, rs2: t, imm: a.off, arr: a.sym });
			this.freeTmp.unshift(t);
			this.release(a);
		}
	}

	/* ----------------------------------------------------------------- layout */

	const KIND = {
		beq: 'cond', bne: 'cond', blt: 'cond', bge: 'cond',
		j: 'jump', halt: 'halt', lw: 'mem', sw: 'mem'
	};

	function memOperand(ins) {
		const n = ins.arr.name + (ins.imm ? '+' + ins.imm : '');
		return n + '(' + regName(ins.rs1) + ')';
	}

	function format(ins) {
		const r = regName;
		const op = ins.disp || ins.op;
		switch (ins.op) {
			case 'li': return 'li ' + r(ins.rd) + ', ' + ins.imm;
			case 'lw': return 'lw ' + r(ins.rd) + ', ' + memOperand(ins);
			case 'sw': return 'sw ' + r(ins.rs2) + ', ' + memOperand(ins);
			case 'j': return 'j ' + ins.target;
			case 'halt': return 'ecall';
			case 'beq': case 'bne': case 'blt': case 'bge':
				return op + ' ' + ins.dops.map(r).join(', ') + ', ' + ins.target;
		}
		if (ins.disp === 'mv') return 'mv ' + r(ins.rd) + ', ' + r(ins.rs1);
		if (ins.disp === 'neg' || ins.disp === 'snez') return op + ' ' + r(ins.rd) + ', ' + r(ins.rs2);
		if (ins.disp === 'not' || ins.disp === 'seqz') return op + ' ' + r(ins.rd) + ', ' + r(ins.rs1);
		if (ins.rs2 !== undefined) return op + ' ' + r(ins.rd) + ', ' + r(ins.rs1) + ', ' + r(ins.rs2);
		return op + ' ' + r(ins.rd) + ', ' + r(ins.rs1) + ', ' + ins.imm;
	}

	function compile(source) {
		const toks = lex(source);
		const ast = new Parser(toks).program();
		const g = new Gen();
		// Seed gp only when rand() runs at run time (array initialisers are filled at load time).
		let uses = false;
		(function scan(n) {
			if (!n || typeof n !== 'object') return;
			if (Array.isArray(n)) { n.forEach(scan); return; }
			if (n.k === 'call') uses = true;
			Object.keys(n).forEach(function (key) {
				if (key === 'init' && n.size !== null && n.size !== undefined) return;
				scan(n[key]);
			});
		})(ast);
		if (uses) { g.line = 1; g.emit({ op: 'li', rd: RNG, imm: RAND_SEED, note: 'rand() state' }); }
		// The program body is one block; keep its variables visible at the end for the summary.
		g.pushScope();
		ast.body.forEach(function (s) { g.stmt(s); });
		g.line = (toks[toks.length - 1].line) || 1;
		g.emit({ op: 'halt', note: 'exit' });

		// Assign addresses and resolve labels.
		const instrs = [], listing = [], labels = {};
		let pc = TEXT_BASE;
		g.code.forEach(function (c) {
			if (c.label) labels[c.label] = pc;
			else pc += 4;
		});
		if ((pc - TEXT_BASE) / 4 > MAX_INSTRS) {
			throw new CompileError('program too large (' + (pc - TEXT_BASE) / 4 + ' instructions, limit ' + MAX_INSTRS + ')', 1, 1);
		}
		// Drop labels nobody jumps to, so the listing stays readable.
		const used = new Set();
		g.code.forEach(function (c) { if (c.target) used.add(c.target); });
		const rename = {}, named = {};
		let nl = 0;
		g.code.forEach(function (c) {
			if (c.label && used.has(c.label)) { rename[c.label] = '.L' + (++nl); named[rename[c.label]] = labels[c.label]; }
		});
		const branches = [];
		pc = TEXT_BASE;
		g.code.forEach(function (c) {
			if (c.label) {
				if (used.has(c.label)) listing.push({ kind: 'label', name: rename[c.label] });
				return;
			}
			const ins = {
				pc: pc,
				op: c.op,
				rd: c.rd === undefined ? 0 : c.rd,
				rs1: c.rs1 === undefined ? 0 : c.rs1,
				rs2: c.rs2 === undefined ? 0 : c.rs2,
				imm: c.imm === undefined ? 0 : c.imm,
				arr: c.arr ? { name: c.arr.name, addr: c.arr.addr, size: c.arr.size } : null,
				target: c.target ? labels[c.target] : 0,
				targetLabel: c.target ? rename[c.target] : null,
				line: c.line,
				kind: KIND[c.op] || 'alu',
				brId: -1,
				text: '',
				note: c.note || ''
			};
			ins.text = format(Object.assign({}, c, { target: c.target ? rename[c.target] : c.target }));
			if (ins.kind === 'cond') {
				ins.brId = branches.length;
				branches.push({ id: ins.brId, pc: pc, line: c.line, label: 'B' + ins.brId, text: ins.text });
			}
			listing.push({ kind: 'ins', i: instrs.length });
			instrs.push(ins);
			pc += 4;
		});

		return {
			instrs: instrs,
			listing: listing,
			labels: named,
			branches: branches,
			data: Int32Array.from(g.data),
			arrays: g.arrays.map(function (a) { return { name: a.name, addr: a.addr, size: a.size, line: a.line }; }),
			scalars: g.scalars.filter(function (s) { return s.top; }).map(function (s) { return { name: s.name, reg: s.reg, line: s.line }; }),
			usesRand: uses
		};
	}

	BP.compiler = { TEXT_BASE, DATA_BASE, MAX_INSTRS, MAX_DATA_WORDS, RAND_SEED, CompileError, regName, compile };

})(window.BP = window.BP || {});
