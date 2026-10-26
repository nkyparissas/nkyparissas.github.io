/* ==========================================================================
   /bp: pieces shared by every predictor figure.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { hex, brName } = BP.base;
	const S = BP.svg;

	// Header lines shared by every predictor figure: what is being read and written now.
	function callouts(view, pred, x0) {
		const p = view.read, u = view.upd;
		const x = x0 || 110;
		let s = '';
		if (p) {
			s += S.val(x, 18, 'read  ' + brName(p.br) + ' @ ' + hex(p.pc, 16) + ' · cycle ' + view.readCycle +
				' · predict ' + (p.taken ? 'T' : 'NT') + (view.readWrongPath ? ' · wrong path' : ''), view.readNow ? 'rd' : 'dim');
		}
		if (u) {
			s += S.val(x, 36, 'write ' + brName(u.p.br) + ' @ ' + hex(u.p.pc, 16) + ' · cycle ' + view.updCycle +
				' · actual ' + (u.taken ? 'T' : 'NT') + (u.mis ? ' · mispredicted' : ' · correct'), view.updNow ? (u.mis ? 'rx' : 'up') : 'dim');
		}
		const warns = [];
		if (p && view.readNow && pred.warnings) pred.warnings(p).forEach(function (w) { warns.push(w); });
		if (warns.length) s += S.val(x, 54, '⚠ ' + warns[0], 'warn');
		return s;
	}

	BP.figure = { callouts };

})(window.BP = window.BP || {});
