/* ==========================================================================
   /bp: SVG primitives in the survey's figure notation (Fig. 4 to 6).

   Tables are columns of a few rows, a dashed gap and a last row; the entry a
   branch touches is filled. A slash across a bus carries its width. Wires are
   orthogonal: every polyline segment is horizontal or vertical.

   Colour: a table's fill shows its stress level (s0..s4), the entry read this
   cycle is the solid version (h0..h4), and an entry being written has a
   purple dashed outline.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	function esc(s) {
		return String(s).replace(/[&<>"]/g, function (c) {
			return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c];
		});
	}

	function attrs(o) {
		let s = '';
		if (!o) return s;
		Object.keys(o).forEach(function (k) {
			if (o[k] !== undefined && o[k] !== null && o[k] !== false) s += ' ' + k + '="' + esc(o[k]) + '"';
		});
		return s;
	}

	function svg(w, h, body, label) {
		return '<svg viewBox="0 0 ' + w + ' ' + h + '" class="fig-svg" role="img"' +
			(label ? ' aria-label="' + esc(label) + '"' : '') + '>' + body + '</svg>';
	}

	// Text. cls: tx (serif label), sm, mono, v-rd, v-up, v-rx, v-warn, dim.
	function t(x, y, s, cls, extra) {
		return '<text x="' + x + '" y="' + y + '"' + attrs(Object.assign({ class: cls || 'tx' }, extra || {})) + '>' + esc(s) + '</text>';
	}

	function tEnd(x, y, s, cls) { return t(x, y, s, cls, { 'text-anchor': 'end' }); }
	function tMid(x, y, s, cls) { return t(x, y, s, cls, { 'text-anchor': 'middle' }); }

	// Orthogonal wire through pts. kind: ink | rd (prediction) | up (update) | rx (redirect) | dr (decode redirect).
	// o.on: carries data this cycle; o.seq: animation order; o.arrow: arrowhead (default true); o.dim: stale.
	function wire(pts, kind, o) {
		o = o || {};
		for (let i = 1; i < pts.length; i++) {
			if (pts[i][0] !== pts[i - 1][0] && pts[i][1] !== pts[i - 1][1]) {
				throw new Error('diagonal wire segment ' + JSON.stringify(pts[i - 1]) + ' -> ' + JSON.stringify(pts[i]));
			}
		}
		const d = 'M' + pts.map(function (p) { return p[0] + ',' + p[1]; }).join(' L');
		let cls = 'w w-' + kind;
		if (o.on) cls += ' on';
		if (o.dim) cls += ' dim';
		// pathLength=1 lets the draw-in animation use unit dashes; dashed update wires fade in instead.
		return '<path d="' + d + '" class="' + cls + '"' + (kind === 'up' ? '' : ' pathLength="1"') +
			(o.arrow === false ? '' : ' marker-end="url(#bpm-' + kind + ')"') +
			(o.seq !== undefined ? ' style="--seq:' + o.seq + '"' : '') + '/>';
	}

	// Small filled dot marking a wire junction.
	function dot(x, y, kind) {
		return '<circle cx="' + x + '" cy="' + y + '" r="2.6" class="dot dot-' + (kind || 'ink') + '"/>';
	}

	// Bus-width slash on a horizontal ('h') or vertical ('v') wire, with its label.
	function tick(x, y, dir, label, labelCls) {
		let s;
		if (dir === 'h') {
			s = '<path d="M' + (x - 5) + ',' + (y + 7) + ' L' + (x + 5) + ',' + (y - 7) + '" class="tick"/>';
			if (label) s += t(x - 4, y + 21, label, labelCls || 'tx sm');
		} else {
			s = '<path d="M' + (x - 7) + ',' + (y + 5) + ' L' + (x + 7) + ',' + (y - 5) + '" class="tick"/>';
			if (label) s += t(x + 10, y + 5, label, labelCls || 'tx sm');
		}
		return s;
	}

	// The shadowed name tag in the corner of each Fig. 4 panel.
	function figLabel(x, y, s) {
		const w = Math.max(48, s.length * 9 + 18);
		return '<rect x="' + x + '" y="' + y + '" width="' + w + '" height="28" class="figlabel"/>' +
			t(x + 9, y + 20, s, 'tx figlabel-t');
	}

	function rect(x, y, w, h, cls, extra) {
		return '<rect' + attrs(Object.assign({ x: x, y: y, width: w, height: h, class: cls }, extra || {})) + '/>';
	}

	// Read entry: solid in the stress colour. Write entry: purple dashed outline on top.
	// readDim / writeDim: the access happened in an earlier cycle, so draw it faded.
	function cellRect(x, y, w, h, level, mode, seq, readCls, readDim, writeDim) {
		let s = '';
		const isRead = mode === 'r' || mode === 'rw';
		const isWrite = mode === 'w' || mode === 'rw';
		s += rect(x, y, w, h, isRead ? 'cell ' + (readCls || 'h') + level + ' pop' + (readDim ? ' stale' : '') : 'cell s' + level,
			isRead && seq !== undefined ? { style: '--seq:' + seq } : null);
		if (isWrite) s += rect(x + 2, y + 2, w - 4, h - 4, 'cell-w pop' + (writeDim ? ' stale' : ''), seq !== undefined ? { style: '--seq:' + seq } : null);
		return s;
	}

	// Paper-style table column: rows 0..2, a dashed gap, then row 3 (the last entry).
	// o: { x, y, w, rh, gap, level, read, write, readTxt, writeTxt, sub, seqRead, seqWrite, title: [lines],
	//      readCls: 'q' draws the read entry half-solid (read in parallel but not selected) }
	// Returns { svg, rowY(r), x, y, w, right, bottom, cx }.
	function column(o) {
		const rh = o.rh || 30, gap = o.gap || 40;
		const ys = [o.y, o.y + rh, o.y + 2 * rh, o.y + 3 * rh + gap];
		let s = '';
		if (o.title) {
			o.title.forEach(function (line, i) {
				s += tMid(o.x + o.w / 2, o.y - 10 - (o.title.length - 1 - i) * 16, line, 'tx');
			});
		}
		for (let r = 0; r < 4; r++) {
			let mode = '';
			if (r === o.read && r === o.write) mode = 'rw';
			else if (r === o.read) mode = 'r';
			else if (r === o.write) mode = 'w';
			s += cellRect(o.x, ys[r], o.w, rh, o.level, mode, mode === 'w' ? o.seqWrite : o.seqRead, o.readCls, o.readDim, o.writeDim);
			if (o.sub > 1) {
				for (let k = 1; k < o.sub; k++) {
					const xx = o.x + (o.w * k) / o.sub;
					s += '<path d="M' + xx + ',' + ys[r] + ' L' + xx + ',' + (ys[r] + rh) + '" class="subdiv"/>';
				}
			}
		}
		s += '<path d="M' + (o.x + o.w / 2) + ',' + (o.y + 3 * rh) + ' L' + (o.x + o.w / 2) + ',' + (o.y + 3 * rh + gap) + '" class="gapline"/>';
		if (o.readTxt && o.read !== undefined && o.read >= 0) {
			s += tMid(o.x + o.w / 2, ys[o.read] + rh / 2 + 4, o.readTxt, 'mono on-solid pop' + (o.readDim ? ' stale' : ''), o.seqRead !== undefined ? { style: '--seq:' + o.seqRead } : null);
		}
		if (o.writeTxt && o.write !== undefined && o.write >= 0 && o.write !== o.read) {
			s += tMid(o.x + o.w / 2, ys[o.write] + rh / 2 + 4, o.writeTxt, 'mono v-up pop' + (o.writeDim ? ' stale' : ''), o.seqWrite !== undefined ? { style: '--seq:' + o.seqWrite } : null);
		}
		return {
			svg: s,
			x: o.x, y: o.y, w: o.w, rh: rh,
			right: o.x + o.w,
			bottom: ys[3] + rh,
			cx: o.x + o.w / 2,
			rowY: function (r) { return ys[r] + rh / 2; }
		};
	}

	// Box of PHTs (Fig. 4, per-set / per-address): columns 0, 1, an ellipsis, and the last.
	// o: { x, y, colW, colGap, rh, gap, level, readCol, readRow, writeCol, writeRow, readTxt, writeTxt, sub, title }
	function bank(o) {
		const pad = 10;
		const cols = [0, 1, 2].map(function (i) { return o.x + pad + i * (o.colW + o.colGap) + (i === 2 ? o.colGap : 0); });
		let s = '';
		const geo = [];
		cols.forEach(function (cx, i) {
			const c = column({
				x: cx, y: o.y + pad, w: o.colW, rh: o.rh, gap: o.gap, level: o.level, sub: o.sub,
				read: i === o.readCol ? o.readRow : -1,
				write: i === o.writeCol ? o.writeRow : -1,
				readTxt: i === o.readCol ? o.readTxt : null,
				writeTxt: i === o.writeCol ? o.writeTxt : null,
				seqRead: o.seqRead, seqWrite: o.seqWrite, readDim: o.readDim, writeDim: o.writeDim
			});
			s += c.svg;
			geo.push(c);
		});
		const right = cols[2] + o.colW + pad;
		const bottom = geo[0].bottom + pad;
		// Ellipsis between the second and the last PHT, at the row being read (as in Fig. 4).
		const ey = geo[1].rowY(o.readRow >= 0 ? o.readRow : 2);
		s += '<path d="M' + (cols[1] + o.colW) + ',' + ey + ' L' + cols[2] + ',' + ey + '" class="gapline"/>';
		s = rect(o.x, o.y, right - o.x, bottom - o.y, 'bankbox') + s;
		if (o.title) s += t(o.titleX !== undefined ? o.titleX : o.x + 60, o.y - 6, o.title, 'tx');
		return {
			svg: s, x: o.x, y: o.y, right: right, bottom: bottom, cols: geo,
			colCx: function (i) { return geo[i].cx; }
		};
	}

	// Grey history register (Global BHR, GHR, K-bit shift register).
	function reg(o) {
		let s = rect(o.x, o.y, o.w, o.h, 'regbox' + (o.on ? ' pop' : ''), o.seq !== undefined ? { style: '--seq:' + o.seq } : null);
		if (o.txt) s += tMid(o.x + o.w / 2, o.y + o.h / 2 + 4, o.txt, 'mono on-reg');
		if (o.write) s += rect(o.x + 2, o.y + 2, o.w - 4, o.h - 4, 'cell-w pop' + (o.writeDim ? ' stale' : ''), o.seqWrite !== undefined ? { style: '--seq:' + o.seqWrite } : null);
		return s;
	}

	// Horizontal mux: wide top edge (inputs), narrow bottom (output).
	function mux(x1, x2, y, h, inset) {
		const i = inset === undefined ? 14 : inset;
		return '<path d="M' + x1 + ',' + y + ' L' + x2 + ',' + y + ' L' + (x2 - i) + ',' + (y + h) + ' L' + (x1 + i) + ',' + (y + h) + ' Z" class="muxbox"/>';
	}

	// Short annotation in a wire colour. kind: rd | up | rx | warn | dim.
	function val(x, y, s, kind, anchor) {
		return t(x, y, s, 'mono v-' + (kind || 'rd'), anchor ? { 'text-anchor': anchor } : null);
	}

	function legendNote(x, y, s) { return t(x, y, s, 'dim'); }

	BP.svg = { esc, svg, t, tEnd, tMid, wire, dot, tick, figLabel, rect, column, bank, reg, mux, val, legendNote };

})(window.BP = window.BP || {});
