/* ==========================================================================
   /bp: functional model. Executes the compiled program in order and yields
   the correct-path trace that the cycle-level front-end (core.js) consumes.
   Wrong-path instructions are fetched by the front-end but never executed
   here, so architectural state is always exact.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { TEXT_BASE, DATA_BASE } = BP.compiler;

	class RuntimeError extends Error {
		constructor(message, line) {
			super(message);
			this.line = line || 0;
		}
	}

	class Machine {
		constructor(program) {
			this.prog = program;
			this.regs = new Int32Array(32);
			this.mem = Int32Array.from(program.data);
			this.pc = TEXT_BASE;
			this.halted = false;
			this.count = 0;
		}

		instrAt(pc) {
			if (pc < TEXT_BASE || (pc & 3)) return null;
			return this.prog.instrs[(pc - TEXT_BASE) >>> 2] || null;
		}

		word(ins) {
			const a = ins.arr;
			const addr = (this.regs[ins.rs1] + ins.imm) | 0;
			const off = addr;
			if (off < 0 || off >= a.size * 4) {
				throw new RuntimeError(a.name + '[' + (off >> 2) + '] is out of bounds (size ' + a.size + ')', ins.line);
			}
			return ((a.addr - DATA_BASE) >> 2) + (off >> 2);
		}

		// Execute one instruction; returns { ins, pc, next, taken }.
		step() {
			const ins = this.instrAt(this.pc);
			if (!ins) throw new RuntimeError('execution left the program at 0x' + this.pc.toString(16), 0);
			const r = this.regs;
			const a = r[ins.rs1], b = r[ins.rs2];
			let v = 0, write = true, taken = false;
			switch (ins.op) {
				case 'add': v = a + b; break;
				case 'sub': v = a - b; break;
				case 'mul': v = Math.imul(a, b); break;
				case 'div': v = b === 0 ? -1 : (a === -2147483648 && b === -1) ? a : (a / b) | 0; break;
				case 'rem': v = b === 0 ? a : (a === -2147483648 && b === -1) ? 0 : a % b; break;
				case 'remu': v = b === 0 ? a : ((a >>> 0) % (b >>> 0)); break;
				case 'and': v = a & b; break;
				case 'or': v = a | b; break;
				case 'xor': v = a ^ b; break;
				case 'sll': v = a << (b & 31); break;
				case 'srl': v = a >>> (b & 31); break;
				case 'sra': v = a >> (b & 31); break;
				case 'slt': v = a < b ? 1 : 0; break;
				case 'sltu': v = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
				case 'addi': v = a + ins.imm; break;
				case 'andi': v = a & ins.imm; break;
				case 'ori': v = a | ins.imm; break;
				case 'xori': v = a ^ ins.imm; break;
				case 'slli': v = a << (ins.imm & 31); break;
				case 'srli': v = a >>> (ins.imm & 31); break;
				case 'srai': v = a >> (ins.imm & 31); break;
				case 'slti': v = a < ins.imm ? 1 : 0; break;
				case 'sltiu': v = (a >>> 0) < (ins.imm >>> 0) ? 1 : 0; break;
				case 'li': v = ins.imm; break;
				case 'lw': v = this.mem[this.word(ins)]; break;
				case 'sw': this.mem[this.word(ins)] = b; write = false; break;
				case 'beq': taken = a === b; write = false; break;
				case 'bne': taken = a !== b; write = false; break;
				case 'blt': taken = a < b; write = false; break;
				case 'bge': taken = a >= b; write = false; break;
				case 'j': taken = true; write = false; break;
				case 'halt': this.halted = true; write = false; break;
				default: throw new RuntimeError('unknown instruction ' + ins.op, ins.line);
			}
			if (write && ins.rd !== 0) r[ins.rd] = v;
			const pc = this.pc;
			const next = this.halted ? pc : taken ? ins.target : pc + 4;
			this.pc = next;
			this.count++;
			return { ins: ins, pc: pc, next: next, taken: taken };
		}

		read(name) {
			const p = this.prog;
			for (let i = 0; i < p.scalars.length; i++) {
				if (p.scalars[i].name === name) return this.regs[p.scalars[i].reg];
			}
			return undefined;
		}
	}

	BP.machine = { RuntimeError, Machine };

})(window.BP = window.BP || {});
