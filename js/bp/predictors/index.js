/* ==========================================================================
   /bp: predictor registry. Each entry is a definition object:
     { id, name, title, group, figure, knobs, validate(k), create(k, opts), about }
   Adding a predictor from a later section of the survey means writing one
   script that publishes such a definition on BP, loading it from bp.html
   before this file, and listing it here; the UI builds the dropdown, the
   knobs and the figure panel from it.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const { BIMODAL } = BP.bimodal;
	const { TWO_LEVEL } = BP.twolevel;
	const { ALLOYED } = BP.alloyed;
	const { CORRELATION } = BP.correlation;
	const { GSELECT, GSHARE } = BP.mcfarling;
	const { GSKEW } = BP.skewed;
	const { BIMODE } = BP.bimode;
	const { AGREE } = BP.agree;
	const { GEHL } = BP.gehl;
	const { TAGE } = BP.tage;

	// In survey order: Section III baseline, III-A, III-B, III-C, III-D, III-E.
	const PREDICTORS = [BIMODAL].concat(TWO_LEVEL, [ALLOYED, CORRELATION, GSELECT, GSHARE, GSKEW, BIMODE, AGREE, GEHL, TAGE]);

	function findPredictor(id) {
		for (let i = 0; i < PREDICTORS.length; i++) if (PREDICTORS[i].id === id) return PREDICTORS[i];
		return null;
	}

	function defaultKnobs(def) {
		const k = {};
		def.knobs.forEach(function (kn) { k[kn.id] = kn.def; });
		return k;
	}

	// Compact "k=8 rows=256" summary for the run history.
	function knobSummary(def, k) {
		return def.knobs.map(function (kn) {
			let v = k[kn.id];
			if (kn.type === 'choice' && kn.options && typeof kn.options[0] === 'object') {
				const o = kn.options.filter(function (x) { return x.v === v; })[0];
				v = o ? o.v : v;
			}
			return kn.id + '=' + v;
		}).join(' ');
	}

	BP.registry = { PREDICTORS, findPredictor, defaultKnobs, knobSummary };

})(window.BP = window.BP || {});
