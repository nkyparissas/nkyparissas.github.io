/* =============================================================================
 * PetriPlan — Petri-net task scheduler
 *
 * Copyright (c) 2026 Nick Kyparissas — https://github.com/nkyparissas
 * Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
 * Free to use, change and share, provided you credit the author.
 *
 * Zero dependencies. Nothing here is loaded from a CDN, bundled, or transpiled.
 * The whole tool is DOM + SVG + Pointer Events + Blob/FileReader, all of which
 * have been stable in browsers for the better part of a decade.
 *
 * Model
 * -----
 * A bipartite directed graph. Tasks are the work; barriers are synchronisation
 * points. Every task runs barrier -> task -> barrier, so a task may only begin
 * once EVERY task feeding its incoming barrier is complete (an AND-join).
 * Two fixed barriers always exist: ROOT ("Project start") and END
 * ("Project complete").
 *
 * Edges marked `auto` are placeholder wiring to ROOT/END that keeps a freshly
 * created node valid; they are dissolved as soon as a real edge takes over, and
 * restored if a node is ever left dangling.
 * ========================================================================== */

(function () {
	'use strict';

	var SVGNS = 'http://www.w3.org/2000/svg';
	var STORAGE_KEY = 'petriplan:autosave';
	var THEME_KEY = 'petriplan:theme';   // also read by the inline script in <head>
	var FILE_FORMAT = 'petriplan';
	var FILE_VERSION = 1;

	var ROOT_ID = 'root';
	var END_ID = 'end';

	/* -------------------------------------------------------------- constants */

	/* Status palette. Green and red are ~indistinguishable under deuteranopia
	   (validated: CVD dE 4.1), so state is carried redundantly by a glyph, a
	   text label, and a border dash pattern. Colour is never the only channel. */
	/* Steps are chosen so WHITE text clears 4.5:1 on every pill, which is why
	   they sit darker than a plain status palette would. "Under review" is the
	   exception and keeps black ink: white on amber measures 1.83:1, which is
	   unreadable, while black on it measures 10.73:1. */
	var STATES = [
		{ key: 'not-started', label: 'Not started',  glyph: '○', color: '#73716c', ink: '#ffffff', dash: '2 3' },
		{ key: 'in-progress', label: 'In progress',  glyph: '▶', color: '#2771cb', ink: '#ffffff', dash: '' },
		{ key: 'blocked',     label: 'Blocked',      glyph: '✕', color: '#d03939', ink: '#ffffff', dash: '7 4' },
		{ key: 'review',      label: 'Under review', glyph: '◆', color: '#fab219', ink: '#0b0b0b', dash: '10 3 2 3' },
		{ key: 'completed',   label: 'Completed',    glyph: '✓', color: '#0a830a', ink: '#ffffff', dash: '' }
	];
	var STATE_BY_KEY = {};
	STATES.forEach(function (s) { STATE_BY_KEY[s.key] = s; });

	/* States that assert work has begun — these are the ones the dependency
	   rule gates. "Not started" and "Blocked" are always selectable. */
	var GATED_STATES = { 'in-progress': 1, 'review': 1, 'completed': 1 };

	/* Gating is also applied retroactively: if the graph changes so that a task
	   is no longer ready, a claim that work is underway has become false and is
	   demoted to Blocked. "Completed" is deliberately absent — finished work
	   stays finished, and is surfaced as a warning instead. */
	var DEMOTE_WHEN_UNREADY = { 'in-progress': 1, 'review': 1 };

	/* Categorical slots, in the validated order. These are a free-choice
	   grouping colour for the user; the encoding that carries meaning is state. */
	var SWATCHES = ['#2a78d6', '#eb6834', '#1baf7a', '#eda100', '#e87ba4', '#008300', '#4a3aa7', '#e34948'];

	var HEX_COLOR = /^#[0-9a-fA-F]{3}(?:[0-9a-fA-F]{3})?$/;

	/* Node and edge ids from a file become object keys. Assigning to "__proto__"
	   sets an object's prototype instead of adding a property, which silently
	   corrupts every id-keyed map (the topological sort, the readiness cache).
	   Such ids are never produced by uid(), so refusing them costs nothing. */
	function isUnsafeKey(id) {
		return String(id) === '__proto__';
	}

	var TASK_W = 200, TASK_H = 58;
	var BAR_W = 18, BAR_H = 58;
	/* Labels sit above their node, so a tight ROW_GAP lets an edge running
	   between columns pass straight through the row below's label — hence the
	   generous vertical gap. COL_GAP stays moderate on purpose: widening columns
	   makes the graph wider, which only makes fit-to-view zoom further out. */
	var COL_GAP = 112, ROW_GAP = 82;

	var MIN_K = 0.2, MAX_K = 2.6;
	var MAX_FIT = 1;                   /* ceiling for fit-to-view only */

	/* PNG export. The target is an area, not a width, so the aspect ratio of
	   whatever you drew is preserved. MAX_SIDE stays well inside the canvas
	   limits browsers enforce (Safari caps a side at 16384). */
	var EXPORT_PIXELS = 12e6;
	var EXPORT_MAX_SIDE = 10000;

	/* ------------------------------------------------------------------ state */

	var model = emptyModel();
	var view = { x: 0, y: 0, k: 1 };

	/* { kind: 'node'|'edge', ids: [...] }. An edge selection always holds exactly
	   one id; node selections may hold many. */
	var selection = null;
	var connectMode = false;
	var connectFrom = null;            // node id
	var analysis = null;               // recomputed on every render

	var undoStack = [];
	var redoStack = [];
	var UNDO_LIMIT = 60;

	var nodeEls = {};                  // id -> <g>
	var edgeEls = {};                  // id -> { path, hit }
	var seq = 0;

	/* ------------------------------------------------------------------- dom */

	var $ = function (id) { return document.getElementById(id); };

	var svg, viewportG, edgeLayer, ghostLayer, nodeLayer;
	var inspector, inspectorInner, statusMsg, problemsBtn, canvasHint, zoomControls;

	/* ----------------------------------------------------------------- utils */

	function uid(prefix) {
		seq += 1;
		return prefix + '-' + Date.now().toString(36) + '-' + seq.toString(36);
	}

	function el(name, attrs, parent) {
		var node = document.createElementNS(SVGNS, name);
		if (attrs) {
			Object.keys(attrs).forEach(function (k) {
				if (attrs[k] !== null && attrs[k] !== undefined) node.setAttribute(k, attrs[k]);
			});
		}
		if (parent) parent.appendChild(node);
		return node;
	}

	function html(name, attrs, parent) {
		var node = document.createElement(name);
		if (attrs) {
			Object.keys(attrs).forEach(function (k) {
				if (k === 'text') node.textContent = attrs[k];
				else if (k === 'html') node.innerHTML = attrs[k];
				else if (attrs[k] !== null && attrs[k] !== undefined) node.setAttribute(k, attrs[k]);
			});
		}
		if (parent) parent.appendChild(node);
		return node;
	}

	function clear(node) { while (node.firstChild) node.removeChild(node.firstChild); }

	function truncate(text, max) {
		text = String(text || '');
		return text.length > max ? text.slice(0, max - 1).trim() + '…' : text;
	}

	function nodeW(n) { return n.type === 'task' ? TASK_W : BAR_W; }
	function nodeH(n) { return n.type === 'task' ? TASK_H : BAR_H; }

	function outAnchor(n) { return { x: n.x + nodeW(n), y: n.y + nodeH(n) / 2 }; }
	function inAnchor(n) { return { x: n.x, y: n.y + nodeH(n) / 2 }; }

	/* ----------------------------------------------------------------- model */

	function emptyModel() {
		return {
			project: 'Untitled project',
			nodes: {
				root: { id: ROOT_ID, type: 'barrier', label: 'Project start', x: 0, y: 0, fixed: true },
				end:  { id: END_ID,  type: 'barrier', label: 'Project complete', x: 520, y: 0, fixed: true }
			},
			edges: {}
		};
	}

	function allNodes() { return Object.keys(model.nodes).map(function (id) { return model.nodes[id]; }); }
	function allEdges() { return Object.keys(model.edges).map(function (id) { return model.edges[id]; }); }

	function predsOf(id) {
		return allEdges().filter(function (e) { return e.to === id; }).map(function (e) { return e.from; });
	}
	function succsOf(id) {
		return allEdges().filter(function (e) { return e.from === id; }).map(function (e) { return e.to; });
	}
	function edgeBetween(from, to) {
		return allEdges().filter(function (e) { return e.from === from && e.to === to; })[0] || null;
	}

	function addEdge(from, to, auto) {
		if (from === to) return null;
		if (edgeBetween(from, to)) return null;
		var e = { id: uid('e'), from: from, to: to, auto: !!auto };
		model.edges[e.id] = e;
		return e;
	}

	function removeEdge(id) { delete model.edges[id]; }

	/* Would adding from -> to close a loop? Walk forward from `to`. */
	function wouldCycle(from, to) {
		if (from === to) return true;
		var seen = {}, stack = [to];
		while (stack.length) {
			var cur = stack.pop();
			if (cur === from) return true;
			if (seen[cur]) continue;
			seen[cur] = true;
			succsOf(cur).forEach(function (n) { stack.push(n); });
		}
		return false;
	}

	/* Placeholder wiring: every node must sit on a path from ROOT to END. */
	function dissolveAutoIn(id) {
		allEdges().forEach(function (e) {
			if (e.to === id && e.auto && e.from === ROOT_ID) removeEdge(e.id);
		});
	}
	function dissolveAutoOut(id) {
		allEdges().forEach(function (e) {
			if (e.from === id && e.auto && e.to === END_ID) removeEdge(e.id);
		});
	}

	function reattachDangling() {
		allNodes().forEach(function (n) {
			if (n.id === ROOT_ID || n.id === END_ID) return;
			if (predsOf(n.id).length === 0) addEdge(ROOT_ID, n.id, true);
			if (succsOf(n.id).length === 0) addEdge(n.id, END_ID, true);
		});

		/* With nothing in between, the two fixed barriers still have to form a
		   path or an empty project reports itself as broken. The placeholder is
		   withdrawn as soon as there is real content to route through. */
		var hasContent = allNodes().some(function (n) { return !n.fixed; });
		var direct = edgeBetween(ROOT_ID, END_ID);
		if (!hasContent && !direct) addEdge(ROOT_ID, END_ID, true);
		else if (hasContent && direct && direct.auto) removeEdge(direct.id);
	}

	function createTask(x, y) {
		var n = {
			id: uid('t'),
			type: 'task',
			label: 'New task',
			description: '',
			start: '',
			end: '',
			color: SWATCHES[0],
			state: 'not-started',
			x: x, y: y
		};
		model.nodes[n.id] = n;
		addEdge(ROOT_ID, n.id, true);
		addEdge(n.id, END_ID, true);
		reattachDangling();
		return n;
	}

	function createBarrier(x, y, label) {
		var n = { id: uid('b'), type: 'barrier', label: label || 'Barrier', x: x, y: y };
		model.nodes[n.id] = n;
		return n;
	}

	function deleteNode(id) {
		var n = model.nodes[id];
		if (!n || n.fixed) return false;
		allEdges().forEach(function (e) {
			if (e.from === id || e.to === id) removeEdge(e.id);
		});
		delete model.nodes[id];
		reattachDangling();
		return true;
	}

	/* Connect two nodes, inserting a barrier when both ends are tasks. */
	function connect(fromId, toId) {
		var a = model.nodes[fromId], b = model.nodes[toId];
		if (!a || !b) return { ok: false, msg: 'Node no longer exists.' };
		if (fromId === toId) return { ok: false, msg: 'A node cannot depend on itself.' };
		if (toId === ROOT_ID) return { ok: false, msg: 'Nothing can run before Project start.' };
		if (fromId === END_ID) return { ok: false, msg: 'Nothing can run after Project complete.' };
		if (edgeBetween(fromId, toId)) return { ok: false, msg: 'Those two are already connected.' };
		if (wouldCycle(fromId, toId)) {
			return { ok: false, msg: 'That would create a circular dependency.' };
		}

		if (a.type === 'task' && b.type === 'task') {
			/* Tasks always run barrier -> task -> barrier, so drop one in between. */
			var mid = createBarrier(
				Math.round((a.x + nodeW(a) + b.x) / 2 - BAR_W / 2),
				Math.round((a.y + b.y) / 2),
				'Sync'
			);
			dissolveAutoOut(fromId);
			dissolveAutoIn(toId);
			addEdge(fromId, mid.id, false);
			addEdge(mid.id, toId, false);
			reattachDangling();
			return { ok: true, msg: 'Connected via a new barrier.', inserted: mid.id };
		}

		dissolveAutoOut(fromId);
		dissolveAutoIn(toId);
		addEdge(fromId, toId, false);
		reattachDangling();
		return { ok: true, msg: 'Connected.' };
	}

	/* -------------------------------------------------------------- analysis */

	/* ------------------------------------------------------------- scheduling
	 *
	 * Critical Path Method over the same graph the dependency rule uses. Dates
	 * are handled as whole days in UTC: an <input type="date"> yields
	 * "YYYY-MM-DD", and parsing that as UTC avoids a local timezone shifting a
	 * date across midnight.
	 *
	 * Convention: a task occupies its start and end dates inclusively, so
	 * 1 Jul -> 3 Jul is three days, and a successor starts the day after its
	 * predecessor finishes. Barriers take no time and simply pass the date
	 * through.
	 */

	var DAY = 86400000;
	var MONTHS = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun',
	              'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'];

	function parseDay(s) {
		var m = /^(\d{4})-(\d{2})-(\d{2})$/.exec(String(s || ''));
		if (!m) return null;
		var t = Date.UTC(+m[1], +m[2] - 1, +m[3]);
		return isNaN(t) ? null : t;
	}

	function formatDay(ms) {
		if (ms === null || ms === undefined || isNaN(ms)) return '—';
		var d = new Date(ms);
		return d.getUTCDate() + ' ' + MONTHS[d.getUTCMonth()] + ' ' + d.getUTCFullYear();
	}

	function taskDuration(n) {
		var s = parseDay(n.start), e = parseDay(n.end);
		if (s === null || e === null || e < s) return null;
		return (e - s) / DAY + 1;                       // inclusive of both ends
	}

	/* Returns null when the graph has a cycle (dates are meaningless in a loop)
	   or when no task carries a date at all — in which case the whole schedule
	   overlay stays switched off rather than inventing numbers. */
	function computeSchedule(nodes, order, cyclic) {
		if (cyclic) return null;

		var ids = Object.keys(nodes);
		var dated = ids.filter(function (id) {
			return nodes[id].type === 'task' && parseDay(nodes[id].start) !== null;
		});
		if (!dated.length) return null;

		var projectStart = Math.min.apply(null, dated.map(function (id) {
			return parseDay(nodes[id].start);
		}));

		var dur = {}, undated = [];
		ids.forEach(function (id) {
			var n = nodes[id];
			if (n.type !== 'task') { dur[id] = 0; return; }
			var d = taskDuration(n);
			if (d === null) { dur[id] = 0; undated.push(id); }
			else dur[id] = d;
		});

		/* Forward pass: earliest start and finish. */
		var es = {}, ef = {};
		order.forEach(function (id) {
			var n = nodes[id];
			var preds = predsOf(id);

			if (id === ROOT_ID) {
				/* One day before, so the first real task begins on projectStart. */
				es[id] = ef[id] = projectStart - DAY;
				return;
			}
			var base = preds.length
				? Math.max.apply(null, preds.map(function (p) {
					return ef[p] === undefined ? projectStart - DAY : ef[p];
				}))
				: projectStart - DAY;

			if (n.type === 'task') {
				es[id] = base + DAY;
				ef[id] = es[id] + Math.max(0, dur[id] - 1) * DAY;
			} else {
				es[id] = ef[id] = base;                 // barriers take no time
			}
		});

		var projectFinish = ef[END_ID];
		ids.forEach(function (id) {
			if (ef[id] !== undefined && (projectFinish === undefined || ef[id] > projectFinish)) {
				projectFinish = ef[id];
			}
		});

		/* Backward pass: latest finish and start, mirroring the forward rules. */
		var lf = {}, ls = {};
		order.slice().reverse().forEach(function (id) {
			var n = nodes[id];
			var succs = succsOf(id);
			lf[id] = succs.length
				? Math.min.apply(null, succs.map(function (s) {
					if (ls[s] === undefined) return projectFinish;
					return nodes[s] && nodes[s].type === 'task' ? ls[s] - DAY : ls[s];
				}))
				: projectFinish;
			ls[id] = n.type === 'task' ? lf[id] - Math.max(0, dur[id] - 1) * DAY : lf[id];
		});

		var slack = {}, critical = {};
		ids.forEach(function (id) {
			if (es[id] === undefined || ls[id] === undefined) return;
			slack[id] = Math.round((ls[id] - es[id]) / DAY);
			critical[id] = slack[id] <= 0;
		});

		return {
			projectStart: projectStart,
			projectFinish: projectFinish,
			es: es, ef: ef, ls: ls, lf: lf,
			slack: slack, critical: critical,
			dur: dur, undated: undated
		};
	}

	function analyse() {
		var nodes = model.nodes;
		var ids = Object.keys(nodes);
		var sat = {};
		var resolving = {};

		function satisfied(id) {
			if (Object.prototype.hasOwnProperty.call(sat, id)) return sat[id];
			if (resolving[id]) return false;              // inside a cycle
			resolving[id] = true;

			var n = nodes[id];
			var result;
			if (n.type === 'task') {
				result = n.state === 'completed';
			} else {
				result = predsOf(id).every(function (p) { return satisfied(p); });
			}

			resolving[id] = false;
			sat[id] = result;
			return result;
		}

		var ready = {};
		ids.forEach(function (id) {
			ready[id] = predsOf(id).every(function (p) { return satisfied(p); });
		});
		ids.forEach(function (id) { satisfied(id); });

		/* Kahn's algorithm — anything left over is inside a cycle. */
		var indeg = {}, adj = {};
		ids.forEach(function (id) { indeg[id] = 0; adj[id] = []; });
		allEdges().forEach(function (e) {
			if (nodes[e.from] && nodes[e.to]) { adj[e.from].push(e.to); indeg[e.to] += 1; }
		});
		var queue = ids.filter(function (id) { return indeg[id] === 0; });
		var layer = {}, order = [];
		queue.forEach(function (id) { layer[id] = 0; });
		while (queue.length) {
			var cur = queue.shift();
			order.push(cur);
			adj[cur].forEach(function (t) {
				layer[t] = Math.max(layer[t] || 0, (layer[cur] || 0) + 1);
				indeg[t] -= 1;
				if (indeg[t] === 0) queue.push(t);
			});
		}
		var inCycle = {};
		var cyclic = order.length !== ids.length;
		if (cyclic) {
			var placed = {};
			order.forEach(function (id) { placed[id] = true; });
			ids.forEach(function (id) { if (!placed[id]) { inCycle[id] = true; layer[id] = layer[id] || 0; } });
		}

		var schedule = computeSchedule(nodes, order, cyclic);

		/* Reachability, so we can flag anything stranded off the main flow. */
		var fromRoot = reach(ROOT_ID, succsOf);
		var toEnd = reach(END_ID, predsOf);

		var problems = [];
		if (cyclic) {
			problems.push({
				severity: 'error',
				msg: 'Circular dependency: ' + Object.keys(inCycle).length + ' node(s) form a loop.',
				nodeId: Object.keys(inCycle)[0]
			});
		}

		ids.forEach(function (id) {
			var n = nodes[id];

			if (!fromRoot[id] && id !== ROOT_ID) {
				problems.push({ severity: 'error', msg: labelOf(n) + ' is not reachable from Project start.', nodeId: id });
			}
			if (!toEnd[id] && id !== END_ID) {
				problems.push({ severity: 'error', msg: labelOf(n) + ' never leads to Project complete.', nodeId: id });
			}
			if (n.type !== 'task') return;

			/* Only "Completed" can still be seen here: the started states are
			   demoted to Blocked as soon as they stop being ready. Finished work
			   is kept, so this is reported as a warning rather than an error. */
			if (GATED_STATES[n.state] && !ready[id]) {
				problems.push({
					severity: n.state === 'completed' ? 'warn' : 'error',
					msg: labelOf(n) + ' is "' + STATE_BY_KEY[n.state].label +
					     '" but work it depends on is not complete.',
					nodeId: id
				});
			}
			predsOf(id).forEach(function (p) {
				if (nodes[p] && nodes[p].type === 'task') {
					problems.push({ severity: 'error', msg: labelOf(n) + ' is fed directly by a task instead of a barrier.', nodeId: id });
				}
			});
			if (n.start && n.end && n.start > n.end) {
				problems.push({ severity: 'warn', msg: labelOf(n) + ' ends before it starts.', nodeId: id });
			}

			/* The plan contradicts the graph: this task is booked to begin before
			   the work it depends on can possibly be finished. */
			if (schedule) {
				var declared = parseDay(n.start);
				if (declared !== null && schedule.es[id] !== undefined && declared < schedule.es[id]) {
					problems.push({
						severity: 'error',
						msg: labelOf(n) + ' is set to start ' + formatDay(declared) +
						     ', but its dependencies cannot finish before ' +
						     formatDay(schedule.es[id] - DAY) + '.',
						nodeId: id
					});
				}
			}
		});

		return {
			satisfied: sat, ready: ready, layer: layer, inCycle: inCycle,
			cyclic: cyclic, problems: problems, fromRoot: fromRoot, toEnd: toEnd,
			schedule: schedule
		};
	}

	function reach(startId, step) {
		var seen = {}, stack = [startId];
		while (stack.length) {
			var cur = stack.pop();
			if (seen[cur]) continue;
			seen[cur] = true;
			step(cur).forEach(function (n) { stack.push(n); });
		}
		return seen;
	}

	function labelOf(n) { return '"' + (n.label || 'Untitled') + '"'; }

	/* Nearest upstream tasks that are holding this one back. */
	function blockers(id) {
		var out = [], seen = {}, stack = predsOf(id).slice();
		while (stack.length) {
			var cur = stack.pop();
			if (seen[cur]) continue;
			seen[cur] = true;
			var n = model.nodes[cur];
			if (!n) continue;
			if (n.type === 'task') {
				if (n.state !== 'completed') out.push(n);
				continue;                     // stop at the first incomplete layer
			}
			predsOf(cur).forEach(function (p) { stack.push(p); });
		}
		return out;
	}

	/* -------------------------------------------------------------- rendering */

	/* A task claiming to be underway when its dependencies are no longer complete
	   is stating something untrue, so the claim is withdrawn rather than merely
	   flagged. Demoting to Blocked cannot cascade: readiness depends only on
	   which tasks are Completed, and this never touches that, so one pass is
	   always enough. Nothing is auto-promoted the other way — the tool has no
	   basis for deciding that work has resumed. */
	function demoteUnreadyTasks() {
		var demoted = [];
		allNodes().forEach(function (n) {
			if (n.type !== 'task') return;
			if (!DEMOTE_WHEN_UNREADY[n.state]) return;
			if (analysis.ready[n.id]) return;
			n.state = 'blocked';
			demoted.push(n.label || 'Untitled');
		});
		return demoted;
	}

	function render() {
		analysis = analyse();

		var demoted = demoteUnreadyTasks();
		if (demoted.length) analysis = analyse();   // readiness text is now stale

		renderEdges();
		renderNodes();
		renderStatus();
		applyViewTransform();

		if (demoted.length) {
			/* A real model change, so make sure it reaches storage even on the
			   render paths that do not persist themselves (restore, select). */
			persistDebounced();
			/* After renderStatus(), which would otherwise overwrite the message,
			   and held so the caller's own confirmation cannot bury it. */
			flash((demoted.length === 1 ? '"' + demoted[0] + '" is' : demoted.length + ' tasks are') +
			      ' no longer unblocked, so moved to Blocked.', true);
		}
	}

	function renderEdges() {
		clear(edgeLayer);
		edgeEls = {};
		var ctx = routingContext();
		allEdges().forEach(function (e) {
			var a = model.nodes[e.from], b = model.nodes[e.to];
			if (!a || !b) return;

			var d = edgePathFor(e, a, b, ctx);
			var g = el('g', null, edgeLayer);

			var hit = el('path', { d: d, 'class': 'edge-hit' }, g);
			hit.dataset.edgeId = e.id;

			var cls = 'edge';
			if (e.auto) cls += ' is-auto';
			if (analysis.satisfied[e.from]) cls += ' is-satisfied';
			if (analysis.schedule &&
				analysis.schedule.critical[e.from] && analysis.schedule.critical[e.to]) {
				cls += ' is-critical';
			}
			if (isSelected('edge', e.id)) cls += ' is-selected';

			var path = el('path', { d: d, 'class': cls }, g);
			edgeEls[e.id] = { path: path, hit: hit };
		});
	}

	/* ------------------------------------------------------------ edge routing
	 *
	 * Edges are orthogonal polylines with rounded corners rather than free
	 * curves, because a curve cannot be steered around anything. Every route is
	 * built from axis-aligned segments, which makes the obstacle test a pair of
	 * interval overlaps instead of general segment/rectangle intersection.
	 *
	 * Several routes are proposed per edge, cheapest first, and the first one
	 * that touches no other node wins. This is not a general path-finder: it
	 * handles the cases a left-to-right dependency graph actually produces —
	 * a straight run, a step between rows, and a detour over or under whatever
	 * sits in the way.
	 */

	var EDGE_STUB = 18;      // straight run off a node before the first turn
	var EDGE_APPROACH = 34;  // longer run into a node on a detour, so the last
	                         // corner is a sweep rather than a cramped hook
	var EDGE_CLEAR = 12;     // keep this far away from other nodes
	var EDGE_LABEL_CLEAR = 5;
	var EDGE_RADIUS = 10;    // corner rounding

	function nodeRect(n, pad) {
		return {
			x0: n.x - pad, y0: n.y - pad,
			x1: n.x + nodeW(n) + pad, y1: n.y + nodeH(n) + pad
		};
	}

	/* The label sits above the node, centred, and is regularly wider than what it
	   labels — "Project complete" renders ~110px over an 18px barrier. Routing
	   around the box alone therefore still draws lines through the text. */
	function labelRect(n) {
		var chars = Math.min((n.label || '').length, n.type === 'task' ? 30 : 22);
		var half = Math.max(nodeW(n), chars * 6.6) / 2;
		var mid = n.x + nodeW(n) / 2;
		return {
			x0: mid - half - EDGE_LABEL_CLEAR,
			y0: n.y - 22 - EDGE_LABEL_CLEAR,
			x1: mid + half + EDGE_LABEL_CLEAR,
			y1: n.y - 2 + EDGE_LABEL_CLEAR
		};
	}

	/* Routes are axis-aligned by construction, so this only has to handle
	   horizontal and vertical segments. */
	function segHitsRect(p, q, r) {
		if (p.y === q.y) {
			if (p.y <= r.y0 || p.y >= r.y1) return false;
			return Math.max(p.x, q.x) > r.x0 && Math.min(p.x, q.x) < r.x1;
		}
		if (p.x === q.x) {
			if (p.x <= r.x0 || p.x >= r.x1) return false;
			return Math.max(p.y, q.y) > r.y0 && Math.min(p.y, q.y) < r.y1;
		}
		return false;
	}

	function routeBlocked(pts, rects) {
		for (var i = 0; i < pts.length - 1; i++) {
			for (var j = 0; j < rects.length; j++) {
				if (segHitsRect(pts[i], pts[i + 1], rects[j])) return true;
			}
		}
		return false;
	}

	function routeEdge(A, B, rects) {
		var bx = B.x - 2;                       // room for the arrowhead
		var start = { x: A.x, y: A.y }, end = { x: bx, y: B.y };
		var level = Math.abs(A.y - B.y) < 0.5;
		var cands = [];

		if (level) cands.push([start, end]);

		if (bx - A.x > EDGE_STUB * 2) {
			var mx = Math.round((A.x + bx) / 2);
			cands.push([start, { x: mx, y: A.y }, { x: mx, y: B.y }, end]);
		}

		/* Only nodes standing between the two ends can force a detour. */
		var lo = Math.min(A.x, bx), hi = Math.max(A.x, bx);
		var between = rects.filter(function (r) { return r.x1 > lo && r.x0 < hi; });

		if (between.length) {
			var top = Infinity, bottom = -Infinity;
			between.forEach(function (r) {
				top = Math.min(top, r.y0);
				bottom = Math.max(bottom, r.y1);
			});
			var ax2 = A.x + EDGE_STUB, bx2 = bx - EDGE_APPROACH;
			var lanes = [bottom + EDGE_CLEAR, top - EDGE_CLEAR];
			/* Try whichever side is the shorter deviation first. */
			if (Math.abs(lanes[1] - A.y) < Math.abs(lanes[0] - A.y)) lanes.reverse();
			lanes.forEach(function (ly) {
				cands.push([
					start, { x: ax2, y: A.y }, { x: ax2, y: ly },
					{ x: bx2, y: ly }, { x: bx2, y: B.y }, end
				]);
			});
		}

		/* Target sits left of the source (only reachable by dragging): leave and
		   enter forwards, looping around outside everything in between. */
		if (bx - A.x <= EDGE_STUB * 2) {
			var outY = (between.length
				? Math.max.apply(null, between.map(function (r) { return r.y1; })) + EDGE_CLEAR
				: Math.max(A.y, B.y) + 60);
			cands.push([
				start, { x: A.x + EDGE_STUB, y: A.y }, { x: A.x + EDGE_STUB, y: outY },
				{ x: bx - EDGE_APPROACH, y: outY }, { x: bx - EDGE_APPROACH, y: B.y }, end
			]);
		}

		for (var i = 0; i < cands.length; i++) {
			if (!routeBlocked(cands[i], rects)) return cands[i];
		}
		/* Nothing clear: fall back to the tidiest shape rather than nothing. */
		return cands[cands.length - 1] || [start, end];
	}

	function tidyPoints(pts) {
		var out = [];
		pts.forEach(function (p) {
			var last = out[out.length - 1];
			if (last && Math.abs(last.x - p.x) < 0.5 && Math.abs(last.y - p.y) < 0.5) return;
			out.push(p);
		});
		/* Drop a middle point that lies on a straight run. */
		for (var i = 1; i < out.length - 1; i++) {
			var p0 = out[i - 1], p1 = out[i], p2 = out[i + 1];
			if ((p0.x === p1.x && p1.x === p2.x) || (p0.y === p1.y && p1.y === p2.y)) {
				out.splice(i, 1);
				i--;
			}
		}
		return out;
	}

	function roundedPath(pts, radius) {
		pts = tidyPoints(pts);
		if (pts.length < 2) return '';
		if (pts.length === 2) {
			return 'M ' + pts[0].x + ' ' + pts[0].y + ' L ' + pts[1].x + ' ' + pts[1].y;
		}

		var d = 'M ' + pts[0].x + ' ' + pts[0].y;
		for (var i = 1; i < pts.length - 1; i++) {
			var p0 = pts[i - 1], p1 = pts[i], p2 = pts[i + 1];
			var d1 = Math.hypot(p1.x - p0.x, p1.y - p0.y);
			var d2 = Math.hypot(p2.x - p1.x, p2.y - p1.y);
			var r = Math.min(radius, d1 / 2, d2 / 2);
			if (r < 0.5) { d += ' L ' + p1.x + ' ' + p1.y; continue; }
			var t1 = { x: p1.x + (p0.x - p1.x) * (r / d1), y: p1.y + (p0.y - p1.y) * (r / d1) };
			var t2 = { x: p1.x + (p2.x - p1.x) * (r / d2), y: p1.y + (p2.y - p1.y) * (r / d2) };
			d += ' L ' + round1(t1.x) + ' ' + round1(t1.y) +
			     ' Q ' + p1.x + ' ' + p1.y + ' ' + round1(t2.x) + ' ' + round1(t2.y);
		}
		var last = pts[pts.length - 1];
		return d + ' L ' + last.x + ' ' + last.y;
	}

	function round1(v) { return Math.round(v * 10) / 10; }

	/* Everything a routing pass needs, built once instead of per edge: the
	   obstacles to avoid, and where each edge should attach. */
	function routingContext() {
		var rects = [];
		allNodes().forEach(function (n) {
			rects.push({ id: n.id, r: nodeRect(n, EDGE_CLEAR) });
			rects.push({ id: n.id, r: labelRect(n) });
		});
		return { rects: rects, anchors: buildAnchors() };
	}

	/* Several edges meeting one node used to land on the same point, so their
	   arrowheads stacked. Spread them along the node's edge instead, ordered by
	   where the other end sits so the lines do not cross each other on the way in. */
	function buildAnchors() {
		var out = {}, into = {};
		var centreY = function (id) {
			var n = model.nodes[id];
			return n ? n.y + nodeH(n) / 2 : 0;
		};

		allNodes().forEach(function (n) {
			var h = nodeH(n);
			var spread = function (edges, otherEnd, x, store) {
				edges.sort(function (p, q) { return centreY(otherEnd(p)) - centreY(otherEnd(q)); });
				var c = edges.length;
				var gap = c > 1 ? Math.min(16, (h * 0.62) / (c - 1)) : 0;
				edges.forEach(function (e, i) {
					store[e.id] = {
						x: x,
						y: Math.round(n.y + h / 2 + (i - (c - 1) / 2) * gap)
					};
				});
			};
			spread(allEdges().filter(function (e) { return e.from === n.id; }),
				function (e) { return e.to; }, n.x + nodeW(n), out);
			spread(allEdges().filter(function (e) { return e.to === n.id; }),
				function (e) { return e.from; }, n.x, into);
		});

		return { out: out, in: into };
	}

	function edgePathFor(e, a, b, ctx) {
		var rects = [];
		for (var i = 0; i < ctx.rects.length; i++) {
			if (ctx.rects[i].id !== a.id && ctx.rects[i].id !== b.id) rects.push(ctx.rects[i].r);
		}
		var A = ctx.anchors.out[e.id] || outAnchor(a);
		var B = ctx.anchors.in[e.id] || inAnchor(b);
		return roundedPath(routeEdge(A, B, rects), EDGE_RADIUS);
	}

	function renderNodes() {
		clear(nodeLayer);
		nodeEls = {};
		allNodes().forEach(function (n) {
			nodeEls[n.id] = n.type === 'task' ? renderTask(n) : renderBarrier(n);
		});
	}

	function nodeClasses(n) {
		var cls = 'node node-' + n.type;
		if (isSelected('node', n.id)) cls += ' is-selected';
		if (connectFrom === n.id) cls += ' is-connect-source';
		if (analysis.inCycle[n.id]) cls += ' is-cycle';
		if (n.type === 'task' && !analysis.ready[n.id] && n.state !== 'completed') cls += ' is-gated';
		if (analysis.schedule && analysis.schedule.critical[n.id]) cls += ' is-critical';
		return cls;
	}

	function renderTask(n) {
		var st = STATE_BY_KEY[n.state] || STATES[0];
		var g = el('g', { 'class': nodeClasses(n), transform: 'translate(' + n.x + ',' + n.y + ')' }, nodeLayer);
		g.dataset.nodeId = n.id;

		el('title', null, g).textContent = n.label + (n.description ? '\n\n' + n.description : '');

		/* Label sits above the node, as specified. */
		var lbl = el('text', {
			'class': 'node-label', x: TASK_W / 2, y: -9, 'text-anchor': 'middle'
		}, g);
		lbl.textContent = truncate(n.label, 30);

		el('rect', {
			'class': 'node-box', width: TASK_W, height: TASK_H, rx: 6,
			stroke: st.color, 'stroke-dasharray': st.dash || null
		}, g);

		/* Grouping colour: a tab down the leading edge. */
		el('rect', { 'class': 'node-stripe', x: 3, y: 3, width: 5, height: TASK_H - 6, rx: 2.5, fill: n.color }, g);

		/* State pill — glyph + word, so it survives colourblindness and greyscale. */
		var pillW = 26 + st.label.length * 6.4;
		var pillX = 16, pillY = (TASK_H - 22) / 2;
		el('rect', { x: pillX, y: pillY, width: pillW, height: 22, rx: 11, fill: st.color }, g);
		var pt = el('text', {
			'class': 'pill-text', x: pillX + pillW / 2, y: pillY + 15, 'text-anchor': 'middle', fill: st.ink
		}, g);
		pt.textContent = st.glyph + '  ' + st.label;

		/* Quiet markers for detail that only opens on click. */
		var marks = '';
		if (n.description) marks += '≡';
		if (n.start || n.end) marks += (marks ? ' ' : '') + '◷';
		if (marks) {
			var mk = el('text', {
				'class': 'node-sublabel', x: TASK_W - 12, y: TASK_H / 2 + 4, 'text-anchor': 'end'
			}, g);
			mk.textContent = marks;
		}

		/* Waiting on upstream work. Drawn as shapes rather than a pause glyph:
		   U+23F8 has no glyph in the site fonts and renders as a tofu box. */
		if (!analysis.ready[n.id] && n.state !== 'completed') {
			var wait = el('g', { transform: 'translate(' + (TASK_W - 21) + ',10)' }, g);
			el('rect', { width: 3.5, height: 11, rx: 1.2, fill: '#898781' }, wait);
			el('rect', { x: 5.5, width: 3.5, height: 11, rx: 1.2, fill: '#898781' }, wait);
			el('title', null, wait).textContent = 'Waiting on upstream tasks';
		}

		return g;
	}

	function renderBarrier(n) {
		var g = el('g', { 'class': nodeClasses(n), transform: 'translate(' + n.x + ',' + n.y + ')' }, nodeLayer);
		g.dataset.nodeId = n.id;

		el('title', null, g).textContent = n.label;

		var lbl = el('text', { 'class': 'node-label', x: BAR_W / 2, y: -9, 'text-anchor': 'middle' }, g);
		lbl.textContent = truncate(n.label, 22);

		var done = analysis.satisfied[n.id];
		el('rect', {
			'class': 'barrier-bar', width: BAR_W, height: BAR_H, rx: 4,
			fill: done ? '#0a830a' : (n.fixed ? '#52514e' : '#898781'),
			stroke: done ? '#0a830a' : '#52514e'
		}, g);

		return g;
	}

	/* Move node elements without rebuilding the DOM. */
	function moveNodeEls(ids) {
		ids.forEach(function (id) {
			var n = model.nodes[id], g = nodeEls[id];
			if (n && g) g.setAttribute('transform', 'translate(' + n.x + ',' + n.y + ')');
		});
		refreshEdgePaths();
	}

	function moveNodeEl(id) { moveNodeEls([id]); }

	/* Every edge is re-routed, not only those touching the moved node: moving a
	   node reorders the fanned anchors at its neighbours, which shifts edges that
	   do not touch it. Routing the whole graph costs a few milliseconds and this
	   only rewrites the `d` attribute, so there is no DOM churn. */
	function refreshEdgePaths() {
		var ctx = routingContext();
		allEdges().forEach(function (e) {
			var refs = edgeEls[e.id];
			var a = model.nodes[e.from], b = model.nodes[e.to];
			if (!refs || !a || !b) return;
			var d = edgePathFor(e, a, b, ctx);
			refs.path.setAttribute('d', d);
			refs.hit.setAttribute('d', d);
		});
	}

	function renderStatus() {
		var tasks = allNodes().filter(function (n) { return n.type === 'task'; });
		var done = tasks.filter(function (n) { return n.state === 'completed'; }).length;
		var readyNow = tasks.filter(function (n) {
			return analysis.ready[n.id] && n.state === 'not-started';
		}).length;

		var bits = [tasks.length + (tasks.length === 1 ? ' task' : ' tasks'), done + ' complete'];
		if (readyNow) bits.push(readyNow + ' ready to start');
		var sch = analysis.schedule;
		if (sch && sch.projectFinish !== undefined) {
			bits.push('finishes ' + formatDay(sch.projectFinish) +
			          (sch.undated.length ? ' at the earliest' : ''));
		}
		/* A held notice outranks the routine counts. Any later render would
		   otherwise wipe it, and this writes to the bar without going through
		   flash(), so the guard has to be here too. */
		if (Date.now() >= holdUntil) statusMsg.textContent = bits.join(' · ');

		var errs = analysis.problems.filter(function (p) { return p.severity === 'error'; });
		if (analysis.problems.length) {
			problemsBtn.hidden = false;
			problemsBtn.textContent = analysis.problems.length +
				(analysis.problems.length === 1 ? ' issue' : ' issues');
			problemsBtn.style.background = errs.length ? 'var(--st-blocked)' : 'var(--st-review)';
			problemsBtn.style.color = errs.length ? '#fff' : '#0b0b0b';
		} else {
			problemsBtn.hidden = true;
		}
	}

	function setHint(text) {
		if (!text) { canvasHint.hidden = true; canvasHint.textContent = ''; return; }
		canvasHint.hidden = false;
		canvasHint.textContent = text;
	}

	var flashTimer = null;
	var holdUntil = 0;

	/* `hold` marks a message the user must not miss — notably "your task was
	   moved to Blocked". render() emits those, and the routine confirmation the
	   caller flashes straight afterwards ("Connected.") would otherwise bury it. */
	function flash(text, hold) {
		if (!hold && Date.now() < holdUntil) return;
		statusMsg.textContent = text;
		if (hold) holdUntil = Date.now() + 4000;
		if (flashTimer) clearTimeout(flashTimer);
		flashTimer = setTimeout(function () {
			holdUntil = 0;
			if (analysis) renderStatus();
		}, hold ? 4000 : 3200);
	}

	/* ---------------------------------------------------------------- layout */

	function autoArrange() {
		pushUndo();
		layoutGraph();
		render();
		fitToView();
		persist();
		flash('Arranged by dependency depth.');
	}

	function layoutGraph() {
		var a = analyse();
		var ids = Object.keys(model.nodes);

		/* ROOT anchors the left edge; END always sits one column past everything
		   else, so it reads as the terminus even if some branch is stranded. */
		var maxLayer = 0;
		ids.forEach(function (id) {
			if (id === END_ID) return;
			maxLayer = Math.max(maxLayer, a.layer[id] || 0);
		});
		a.layer[ROOT_ID] = 0;
		a.layer[END_ID] = maxLayer + 1;

		var byLayer = {};
		ids.forEach(function (id) {
			var L = a.layer[id] || 0;
			(byLayer[L] = byLayer[L] || []).push(id);
		});

		var layerKeys = Object.keys(byLayer).map(Number).sort(function (p, q) { return p - q; });
		var cursorX = 0;

		layerKeys.forEach(function (L) {
			var group = byLayer[L];

			/* Preserve the user's vertical ordering so the layout stays familiar. */
			group.sort(function (p, q) { return model.nodes[p].y - model.nodes[q].y; });

			var widest = 0;
			group.forEach(function (id) { widest = Math.max(widest, nodeW(model.nodes[id])); });

			var totalH = group.length * BAR_H + (group.length - 1) * ROW_GAP;
			var startY = -totalH / 2;

			group.forEach(function (id, i) {
				var n = model.nodes[id];
				n.x = Math.round(cursorX + (widest - nodeW(n)) / 2);
				n.y = Math.round(startY + i * (BAR_H + ROW_GAP));
			});

			cursorX += widest + COL_GAP;
		});
	}

	/* ------------------------------------------------------------ view / zoom */

	function applyViewTransform() {
		viewportG.setAttribute('transform',
			'translate(' + view.x + ',' + view.y + ') scale(' + view.k + ')');
		var pct = Math.round(view.k * 100) + '%';
		var btn = $('btnZoomReset');
		if (btn) btn.textContent = pct;
	}

	function zoomAt(sx, sy, factor) {
		var k = Math.min(MAX_K, Math.max(MIN_K, view.k * factor));
		if (k === view.k) return;
		/* Keep the point under the cursor pinned while scaling. */
		view.x = sx - (sx - view.x) * (k / view.k);
		view.y = sy - (sy - view.y) * (k / view.k);
		view.k = k;
		applyViewTransform();
	}

	function layerBounds(layer) {
		if (!layer || !layer.firstChild) return null;
		var b;
		try { b = layer.getBBox(); } catch (err) { return null; }
		if (!b || (!b.width && !b.height)) return null;
		return { minX: b.x, minY: b.y, maxX: b.x + b.width, maxY: b.y + b.height };
	}

	/* Measure what is actually drawn, not just the node rectangles. A label is
	   centred on its node and is regularly far wider than it — a barrier is 18px
	   across while "Project complete" renders ~110px — and edge curves bulge past
	   their endpoints. Measuring boxes alone underestimates the graph, so fit
	   would zoom in until the overhang was clipped off-frame.
	   nodeLayer/edgeLayer carry no transform of their own, so getBBox() returns
	   world coordinates directly. */
	function contentBounds() {
		if (!allNodes().length) return null;

		var parts = [layerBounds(nodeLayer), layerBounds(edgeLayer)]
			.filter(function (p) { return !!p; });

		if (parts.length) {
			var b = { minX: Infinity, minY: Infinity, maxX: -Infinity, maxY: -Infinity };
			parts.forEach(function (p) {
				b.minX = Math.min(b.minX, p.minX);
				b.minY = Math.min(b.minY, p.minY);
				b.maxX = Math.max(b.maxX, p.maxX);
				b.maxY = Math.max(b.maxY, p.maxY);
			});
			return b;
		}

		/* Fallback when getBBox is unavailable: boxes plus room for the label. */
		var minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
		allNodes().forEach(function (n) {
			minX = Math.min(minX, n.x - 60);
			minY = Math.min(minY, n.y - 22);
			maxX = Math.max(maxX, n.x + nodeW(n) + 60);
			maxY = Math.max(maxY, n.y + nodeH(n));
		});
		return { minX: minX, minY: minY, maxX: maxX, maxY: maxY };
	}

	function fitToView() {
		var b = contentBounds();
		if (!b) return;
		var rect = svg.getBoundingClientRect();
		if (!rect.width || !rect.height) return;

		var pad = rect.width < 560 ? 22 : 64;
		var w = Math.max(1, b.maxX - b.minX), h = Math.max(1, b.maxY - b.minY);
		var k = Math.min((rect.width - pad * 2) / w, (rect.height - pad * 2) / h);
		k = Math.min(MAX_K, Math.max(MIN_K, k));

		/* Never magnify past 1:1. Text is sharpest at its design size, and a
		   three-node net blown up 2.6x just looks broken. Zooming in further is
		   the user's call, not something fit should do on their behalf. */
		k = Math.min(k, MAX_FIT);

		/* A long chain on a phone "fits" only at a zoom no one can read. Below
		   this floor, stay legible and start the user at Project start instead,
		   letting them pan along the flow. */
		var FIT_FLOOR = 0.55;
		var anchorLeft = k < FIT_FLOOR;
		if (anchorLeft) k = FIT_FLOOR;

		view.k = k;
		view.x = anchorLeft ? pad - b.minX * k : (rect.width - w * k) / 2 - b.minX * k;
		view.y = (rect.height - h * k) / 2 - b.minY * k;
		applyViewTransform();
	}

	function screenToWorld(sx, sy) {
		return { x: (sx - view.x) / view.k, y: (sy - view.y) / view.k };
	}

	function localPoint(evt) {
		var rect = svg.getBoundingClientRect();
		return { x: evt.clientX - rect.left, y: evt.clientY - rect.top };
	}

	/* Where a newly created node should land: middle of the viewport. */
	function viewportCentre() {
		var rect = svg.getBoundingClientRect();
		return screenToWorld(rect.width / 2, rect.height / 2);
	}

	/* ------------------------------------------------------------- inspector */

	function selectedIds() { return selection ? selection.ids : []; }

	function isSelected(kind, id) {
		return !!selection && selection.kind === kind && selection.ids.indexOf(id) >= 0;
	}

	function selectedNodes() {
		if (!selection || selection.kind !== 'node') return [];
		return selection.ids.map(function (id) { return model.nodes[id]; }).filter(Boolean);
	}

	/* `ids` may be a single id or an array; falsy clears the selection. */
	function select(kind, ids) {
		var list = ids == null ? [] : (Array.isArray(ids) ? ids.slice() : [ids]);
		selection = (kind && list.length) ? { kind: kind, ids: list } : null;
		render();
		renderInspector();
	}

	/* Shift-click behaviour: add a node, or remove it if already in the set. */
	function toggleInSelection(id) {
		if (!selection || selection.kind !== 'node') return select('node', id);
		var at = selection.ids.indexOf(id);
		var list = selection.ids.slice();
		if (at >= 0) list.splice(at, 1); else list.push(id);
		return select('node', list);
	}

	function isSheet() { return window.matchMedia('(max-width: 820px)').matches; }

	function renderInspector() {
		clear(inspectorInner);

		var open = !!selection;
		inspector.classList.toggle('is-open', open);
		zoomControls.classList.toggle('is-lifted', open && isSheet());

		if (!selection) {
			inspector.classList.add('is-empty');
			html('p', {
				'class': 'empty-note',
				html: 'Nothing selected.<br><br>Click a node to edit its details, or use <b>Task</b> ' +
				      'and <b>Barrier</b> to add to the net. Press <b>?</b> in the toolbar for the full guide.'
			}, inspectorInner);
			return;
		}
		inspector.classList.remove('is-empty');

		if (selection.kind === 'edge') return renderEdgeInspector();
		if (selection.ids.length > 1) return renderMultiInspector();

		var n = model.nodes[selection.ids[0]];
		if (!n) { selection = null; return renderInspector(); }
		return n.type === 'task' ? renderTaskInspector(n) : renderBarrierInspector(n);
	}

	/* Shown when more than one node is selected. Only fields that are meaningful
	   to set on many nodes at once appear: label, description and dates are
	   per-task by nature and are deliberately left out. */
	function renderMultiInspector() {
		var nodes = selectedNodes();
		var tasks = nodes.filter(function (n) { return n.type === 'task'; });
		var barriers = nodes.filter(function (n) { return n.type === 'barrier'; });
		var fixed = nodes.filter(function (n) { return n.fixed; });

		var parts = [];
		if (tasks.length) parts.push(tasks.length + (tasks.length === 1 ? ' task' : ' tasks'));
		if (barriers.length) parts.push(barriers.length + (barriers.length === 1 ? ' barrier' : ' barriers'));

		html('div', { 'class': 'node-kind', text: nodes.length + ' selected' }, inspectorInner);
		html('p', { 'class': 'multi-summary', text: parts.join(' · ') }, inspectorInner);

		if (!tasks.length) {
			html('p', {
				'class': 'empty-note',
				text: 'Barriers carry only a label, so there is nothing to set in bulk. Drag to move them together.'
			}, inspectorInner);
		}

		/* Current spread of states, so it is clear what is about to be overwritten. */
		if (tasks.length) {
			var counts = {};
			tasks.forEach(function (n) { counts[n.state] = (counts[n.state] || 0) + 1; });
			var chips = html('div', { 'class': 'state-tally' }, inspectorInner);
			STATES.forEach(function (st) {
				if (!counts[st.key]) return;
				var chip = html('span', { 'class': 'tally-chip' }, chips);
				chip.style.background = st.color;
				chip.style.color = st.ink;
				chip.textContent = st.glyph + ' ' + counts[st.key] + ' ' + st.label;
			});
		}

		/* Bulk colour */
		if (tasks.length) {
			var fc = html('div', { 'class': 'field' }, inspectorInner);
			html('span', { 'class': 'field-label', text: 'Set colour for all' }, fc);
			var sw = html('div', { 'class': 'swatches' }, fc);
			SWATCHES.forEach(function (hex) {
				var b = html('button', {
					type: 'button', 'class': 'swatch', title: hex, 'aria-label': 'Colour ' + hex
				}, sw);
				b.style.background = hex;
				b.addEventListener('click', function () {
					pushUndo();
					tasks.forEach(function (n) { n.color = hex; });
					render();
					renderInspector();
					persist();
					flash('Colour applied to ' + tasks.length + ' tasks.');
				});
			});

			/* Bulk state. A state is offered only if it is legal for EVERY selected
			   task, otherwise applying it would demote some of them straight back. */
			var allReady = tasks.every(function (n) { return analysis.ready[n.id]; });
			var notReady = tasks.filter(function (n) { return !analysis.ready[n.id]; });

			var fs = html('div', { 'class': 'field' }, inspectorInner);
			html('span', { 'class': 'field-label', text: 'Set state for all' }, fs);
			var states = html('div', { 'class': 'states' }, fs);

			STATES.forEach(function (st) {
				var locked = !allReady && !!GATED_STATES[st.key];
				var b = html('button', {
					type: 'button',
					'class': 'state-opt state-bulk' + (locked ? ' is-disabled' : '')
				}, states);
				if (locked) {
					b.disabled = true;
					b.title = notReady.length + ' of the selected tasks are not unblocked yet.';
				}
				var dot = html('span', { 'class': 'dot', text: st.glyph }, b);
				dot.style.background = st.color;
				dot.style.color = st.ink;
				html('span', { text: st.label }, b);

				b.addEventListener('click', function () {
					if (locked) return;
					pushUndo();
					tasks.forEach(function (n) { n.state = st.key; });
					render();
					renderInspector();
					persist();
					flash('Set ' + tasks.length + ' tasks to ' + st.label + '.');
				});
			});

			if (!allReady) {
				html('div', {
					'class': 'gate-note',
					html: '<b>' + notReady.length + '</b> of these are still waiting on upstream work, ' +
					      'so the started states cannot be applied to the whole set.'
				}, inspectorInner);
			}
		}

		var actions = html('div', { 'class': 'inspector-actions' }, inspectorInner);
		var removable = nodes.length - fixed.length;
		var del = html('button', {
			type: 'button', 'class': 'btn btn-danger',
			text: removable ? 'Delete ' + removable + ' node' + (removable === 1 ? '' : 's') : 'Nothing to delete'
		}, actions);
		if (!removable) del.disabled = true;
		else del.addEventListener('click', function () { doDelete(selectedIds()); });

		if (fixed.length) {
			html('p', {
				'class': 'empty-note',
				text: 'Project start and Project complete are part of the selection but cannot be deleted.'
			}, inspectorInner);
		}
	}

	function renderEdgeInspector() {
		var e = model.edges[selection.ids[0]];
		if (!e) { selection = null; return renderInspector(); }
		var a = model.nodes[e.from], b = model.nodes[e.to];

		html('div', { 'class': 'node-kind', text: 'Dependency' }, inspectorInner);
		var dl = html('dl', { 'class': 'relations' }, inspectorInner);
		html('dt', { text: 'From' }, dl);
		html('dd', { text: a ? a.label : '(missing)' }, dl);
		html('dt', { text: 'To' }, dl);
		html('dd', { text: b ? b.label : '(missing)' }, dl);
		if (e.auto) {
			html('div', {
				'class': 'gate-note',
				html: 'This is <b>placeholder wiring</b>. It keeps the node attached to the ' +
				      'project bounds and dissolves on its own once you connect something real.'
			}, inspectorInner);
		}

		var actions = html('div', { 'class': 'inspector-actions' }, inspectorInner);
		var del = html('button', { type: 'button', 'class': 'btn btn-danger', text: 'Delete link' }, actions);
		del.addEventListener('click', function () {
			pushUndo();
			removeEdge(e.id);
			reattachDangling();
			selection = null;
			render();
			renderInspector();
			persist();
			flash('Link deleted.');
		});
	}

	function renderBarrierInspector(n) {
		html('div', { 'class': 'node-kind', text: n.fixed ? 'Fixed barrier' : 'Barrier' }, inspectorInner);

		var f = html('div', { 'class': 'field' }, inspectorInner);
		html('label', { text: 'Label', 'for': 'f-label' }, f);
		var label = html('input', { type: 'text', id: 'f-label', value: n.label }, f);
		if (n.fixed) label.disabled = true;
		label.addEventListener('input', function () {
			n.label = label.value;
			render();
			persistDebounced();
		});

		html('div', {
			'class': 'gate-note' + (analysis.satisfied[n.id] ? ' is-ok' : ''),
			html: analysis.satisfied[n.id]
				? 'All incoming work is <b>complete</b>. Everything downstream may start.'
				: 'Waiting on incoming work. Tasks after this barrier cannot start yet.'
		}, inspectorInner);

		relationList(n);

		if (!n.fixed) {
			var actions = html('div', { 'class': 'inspector-actions' }, inspectorInner);
			var del = html('button', { type: 'button', 'class': 'btn btn-danger', text: 'Delete barrier' }, actions);
			del.addEventListener('click', function () { doDelete(n.id); });
		}
	}

	function renderTaskInspector(n) {
		html('div', { 'class': 'node-kind', text: 'Task' }, inspectorInner);

		/* label */
		var f1 = html('div', { 'class': 'field' }, inspectorInner);
		html('label', { text: 'Label', 'for': 'f-label' }, f1);
		var label = html('input', { type: 'text', id: 'f-label', value: n.label }, f1);
		label.addEventListener('input', function () { n.label = label.value; render(); persistDebounced(); });

		/* description */
		var f2 = html('div', { 'class': 'field' }, inspectorInner);
		html('label', { text: 'Description', 'for': 'f-desc' }, f2);
		var desc = html('textarea', { id: 'f-desc', rows: 4 }, f2);
		desc.value = n.description || '';
		desc.addEventListener('input', function () { n.description = desc.value; render(); persistDebounced(); });

		/* dates */
		var row = html('div', { 'class': 'field-row' }, inspectorInner);
		var f3 = html('div', { 'class': 'field' }, row);
		html('label', { text: 'Start', 'for': 'f-start' }, f3);
		var start = html('input', { type: 'date', id: 'f-start', value: n.start || '' }, f3);

		var f4 = html('div', { 'class': 'field' }, row);
		html('label', { text: 'End', 'for': 'f-end' }, f4);
		var end = html('input', { type: 'date', id: 'f-end', value: n.end || '' }, f4);

		/* A date change moves the whole schedule, so the panel is rebuilt too. */
		start.addEventListener('change', function () {
			n.start = start.value; render(); renderInspector(); persist();
		});
		end.addEventListener('change', function () {
			n.end = end.value; render(); renderInspector(); persist();
		});

		renderScheduleBlock(n);

		/* colour */
		var f5 = html('div', { 'class': 'field' }, inspectorInner);
		html('span', { 'class': 'field-label', text: 'Colour' }, f5);
		var sw = html('div', { 'class': 'swatches' }, f5);
		SWATCHES.forEach(function (hex) {
			var b = html('button', {
				type: 'button', 'class': 'swatch', title: hex,
				'aria-label': 'Colour ' + hex,
				'aria-pressed': n.color === hex ? 'true' : 'false'
			}, sw);
			b.style.background = hex;
			b.addEventListener('click', function () {
				pushUndo();
				n.color = hex;
				render();
				renderInspector();
				persist();
			});
		});

		/* state — gated by the dependency rule */
		var ready = analysis.ready[n.id];
		var waiting = ready ? [] : blockers(n.id);

		var f6 = html('div', { 'class': 'field' }, inspectorInner);
		html('span', { 'class': 'field-label', text: 'State' }, f6);
		var states = html('div', { 'class': 'states', role: 'radiogroup' }, f6);

		STATES.forEach(function (st) {
			var locked = !ready && !!GATED_STATES[st.key];
			var opt = html('label', { 'class': 'state-opt' + (locked ? ' is-disabled' : '') }, states);
			if (locked) opt.title = 'Blocked until every upstream task is complete.';

			var radio = html('input', { type: 'radio', name: 'state' }, opt);
			radio.checked = n.state === st.key;
			radio.disabled = locked;

			var dot = html('span', { 'class': 'dot', text: st.glyph }, opt);
			dot.style.background = st.color;
			dot.style.color = st.ink;

			html('span', { text: st.label }, opt);

			radio.addEventListener('change', function () {
				if (!radio.checked) return;
				pushUndo();
				n.state = st.key;
				render();
				renderInspector();
				persist();
			});
		});

		if (ready) {
			html('div', {
				'class': 'gate-note is-ok',
				html: 'All dependencies are complete — this task <b>can start</b>.'
			}, inspectorInner);
		} else {
			var names = waiting.map(function (b) { return b.label || 'Untitled'; });
			html('div', {
				'class': 'gate-note',
				html: 'Cannot start yet. Waiting on: <b>' +
				      (names.length ? names.map(escapeHtml).join('</b>, <b>') : 'upstream work') + '</b>.'
			}, inspectorInner);
		}

		relationList(n);

		var actions = html('div', { 'class': 'inspector-actions' }, inspectorInner);
		var del = html('button', { type: 'button', 'class': 'btn btn-danger', text: 'Delete task' }, actions);
		del.addEventListener('click', function () { doDelete(n.id); });
	}

	/* Everything the Critical Path pass worked out about one task. Only shown
	   once some task in the graph carries a date — with none, there is nothing
	   to compute and an empty panel would just be noise. */
	function renderScheduleBlock(n) {
		var s = analysis.schedule;
		if (!s) return;

		var box = html('div', { 'class': 'schedule' }, inspectorInner);
		html('span', { 'class': 'field-label', text: 'Schedule' }, box);

		var dl = html('dl', { 'class': 'schedule-rows' }, box);
		var row = function (label, value, cls) {
			html('dt', { text: label }, dl);
			html('dd', { text: value, 'class': cls || null }, dl);
		};

		var d = s.dur[n.id];
		row('Duration', d ? d + (d === 1 ? ' day' : ' days') : 'no dates set');
		row('Earliest start', formatDay(s.es[n.id]));
		row('Earliest finish', formatDay(s.ef[n.id]));

		var slack = s.slack[n.id];
		if (slack === undefined) {
			row('Slack', '—');
		} else if (slack <= 0) {
			row('Slack', 'none — on the critical path', 'is-critical-note');
		} else {
			row('Slack', slack + (slack === 1 ? ' day' : ' days'));
		}

		var declared = parseDay(n.start);
		if (declared !== null && s.es[n.id] !== undefined && declared < s.es[n.id]) {
			html('div', {
				'class': 'gate-note',
				html: 'The planned start of <b>' + escapeHtml(formatDay(declared)) +
				      '</b> is earlier than the dependencies allow. The earliest ' +
				      'possible start is <b>' + escapeHtml(formatDay(s.es[n.id])) + '</b>.'
			}, box);
		} else if (declared !== null && s.es[n.id] !== undefined && declared > s.es[n.id]) {
			var wait = Math.round((declared - s.es[n.id]) / DAY);
			html('p', {
				'class': 'schedule-note',
				text: 'Planned to start ' + wait + (wait === 1 ? ' day' : ' days') +
				      ' later than it could.'
			}, box);
		}
	}

	function relationList(n) {
		var dl = html('dl', { 'class': 'relations' }, inspectorInner);
		var ps = predsOf(n.id).map(function (id) { return model.nodes[id]; }).filter(Boolean);
		var ss = succsOf(n.id).map(function (id) { return model.nodes[id]; }).filter(Boolean);

		html('dt', { text: 'Comes after' }, dl);
		html('dd', { text: ps.length ? ps.map(function (p) { return p.label; }).join(', ') : '—' }, dl);
		html('dt', { text: 'Leads to' }, dl);
		html('dd', { text: ss.length ? ss.map(function (s) { return s.label; }).join(', ') : '—' }, dl);
	}

	function escapeHtml(s) {
		return String(s).replace(/[&<>"']/g, function (c) {
			return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
		});
	}

	function doDelete(ids) {
		var list = Array.isArray(ids) ? ids : [ids];
		var removable = list.filter(function (id) {
			var n = model.nodes[id];
			return n && !n.fixed;
		});
		var kept = list.length - removable.length;

		if (!removable.length) {
			flash('Project start and Project complete cannot be deleted.');
			return;
		}

		pushUndo();
		removable.forEach(deleteNode);
		selection = null;
		render();
		renderInspector();
		persist();
		flash(removable.length === 1
			? 'Deleted.'
			: 'Deleted ' + removable.length + ' nodes.' +
			  (kept ? ' Project start and Project complete were kept.' : ''));
	}

	/* ----------------------------------------------------------- persistence */

	function serialize() {
		return {
			format: FILE_FORMAT,
			version: FILE_VERSION,
			project: model.project,
			savedAt: new Date().toISOString(),
			view: { x: view.x, y: view.y, k: view.k },
			nodes: allNodes().map(function (n) {
				var out = { id: n.id, type: n.type, label: n.label, x: Math.round(n.x), y: Math.round(n.y) };
				if (n.fixed) out.fixed = true;
				if (n.type === 'task') {
					out.description = n.description || '';
					out.start = n.start || '';
					out.end = n.end || '';
					out.color = n.color;
					out.state = n.state;
				}
				return out;
			}),
			edges: allEdges().map(function (e) {
				return { id: e.id, from: e.from, to: e.to, auto: !!e.auto };
			})
		};
	}

	function deserialize(data) {
		if (!data || typeof data !== 'object') throw new Error('Not a PetriPlan file.');
		if (data.format && data.format !== FILE_FORMAT) throw new Error('Unrecognised file format.');
		if (!Array.isArray(data.nodes) || !Array.isArray(data.edges)) throw new Error('File is missing nodes or edges.');

		var next = { project: String(data.project || 'Untitled project'), nodes: {}, edges: {} };

		data.nodes.forEach(function (raw) {
			if (!raw || !raw.id) return;
			if (isUnsafeKey(raw.id)) return;
			var type = raw.type === 'task' ? 'task' : 'barrier';
			var n = {
				id: String(raw.id),
				type: type,
				label: String(raw.label || (type === 'task' ? 'Untitled task' : 'Barrier')),
				x: Number(raw.x) || 0,
				y: Number(raw.y) || 0
			};
			if (raw.fixed || raw.id === ROOT_ID || raw.id === END_ID) n.fixed = true;
			if (type === 'task') {
				n.description = String(raw.description || '');
				n.start = String(raw.start || '');
				n.end = String(raw.end || '');
				/* Must be a literal hex colour: this value is written straight into
				   a `fill` attribute, and nothing from a file should reach the DOM
				   unvalidated. Any other string falls back to the default. */
				n.color = HEX_COLOR.test(String(raw.color)) ? String(raw.color) : SWATCHES[0];
				n.state = STATE_BY_KEY[raw.state] ? raw.state : 'not-started';
			}
			next.nodes[n.id] = n;
		});

		/* The two fixed barriers are structural — rebuild them if a file lacks them. */
		if (!next.nodes[ROOT_ID]) {
			next.nodes[ROOT_ID] = { id: ROOT_ID, type: 'barrier', label: 'Project start', x: 0, y: 0, fixed: true };
		}
		if (!next.nodes[END_ID]) {
			next.nodes[END_ID] = { id: END_ID, type: 'barrier', label: 'Project complete', x: 520, y: 0, fixed: true };
		}

		var hasNode = function (id) {
			/* Own-property test, not a truthiness test: next.nodes['__proto__']
			   and ['toString'] both resolve up the prototype chain and would let
			   an edge pointing at a non-existent node through. */
			return Object.prototype.hasOwnProperty.call(next.nodes, id);
		};

		data.edges.forEach(function (raw) {
			if (!raw || !raw.from || !raw.to) return;
			if (isUnsafeKey(raw.from) || isUnsafeKey(raw.to)) return;
			if (!hasNode(raw.from) || !hasNode(raw.to)) return;            // drop dangling links
			if (raw.from === raw.to) return;
			var id = String(raw.id || uid('e'));
			if (isUnsafeKey(id)) id = uid('e');
			var dup = Object.keys(next.edges).some(function (k) {
				return next.edges[k].from === raw.from && next.edges[k].to === raw.to;
			});
			if (dup) return;
			next.edges[id] = { id: id, from: String(raw.from), to: String(raw.to), auto: !!raw.auto };
		});

		model = next;
		reattachDangling();

		if (data.view && isFinite(data.view.k)) {
			view.x = Number(data.view.x) || 0;
			view.y = Number(data.view.y) || 0;
			view.k = Math.min(MAX_K, Math.max(MIN_K, Number(data.view.k) || 1));
		}

		$('projectName').value = model.project;
		selection = null;
		undoStack = [];
		redoStack = [];
	}

	function downloadBlob(blob, filename) {
		var url = URL.createObjectURL(blob);
		var a = document.createElement('a');
		a.href = url;
		a.download = filename;
		document.body.appendChild(a);
		a.click();
		document.body.removeChild(a);
		/* Give the browser a moment to start the download before revoking. */
		setTimeout(function () { URL.revokeObjectURL(url); }, 1000);
	}

	function saveToFile() {
		var json = JSON.stringify(serialize(), null, 2);
		var name = slug(model.project) + '.json';
		downloadBlob(new Blob([json], { type: 'application/json' }), name);
		flash('Saved as ' + name);
	}

	/* ----------------------------------------------------------- PNG export */

	/* Properties that actually carry the look. Copied from the live element's
	   computed style onto the clone, because a serialised SVG loaded as an
	   <img> has no access to this page's stylesheet — every class-based rule
	   would otherwise be dropped and the export would come out unstyled. */
	var EXPORT_PROPS = [
		'fill', 'fill-opacity', 'stroke', 'stroke-width', 'stroke-dasharray',
		'stroke-linejoin', 'stroke-linecap', 'stroke-opacity', 'opacity',
		'paint-order', 'font-family', 'font-size', 'font-weight',
		'letter-spacing', 'text-anchor'
	];

	function inlineComputedStyles(src, dst) {
		var cs = window.getComputedStyle(src);
		var decl = '';
		EXPORT_PROPS.forEach(function (p) {
			var v = cs.getPropertyValue(p);
			if (v) decl += p + ':' + v + ';';
		});
		if (decl) dst.setAttribute('style', decl);

		var s = src.children, d = dst.children;
		for (var i = 0; i < s.length && i < d.length; i++) inlineComputedStyles(s[i], d[i]);
	}

	function exportBackground() {
		return window.getComputedStyle(svg).backgroundColor || '#ffffff';
	}

	function buildExportSVG(box, outW, outH, bg) {
		/* Selection is editor state, not part of the drawing. Lift the classes
		   for the duration of the clone so highlights are not baked in, then put
		   them straight back — this is synchronous, so nothing flickers. */
		var marked = Array.prototype.slice.call(
			svg.querySelectorAll('.is-selected, .is-connect-source'));
		marked.forEach(function (el) {
			el.classList.remove('is-selected', 'is-connect-source');
		});

		var clone, styleSrc = ['#edgeLayer', '#nodeLayer'];
		try {
			clone = svg.cloneNode(true);
			/* Inline only the drawn layers. Elements inside <defs> are never
			   rendered, so their computed style is meaningless and would
			   override the marker fills set as attributes. */
			styleSrc.forEach(function (sel) {
				var a = svg.querySelector(sel), b = clone.querySelector(sel);
				if (a && b) inlineComputedStyles(a, b);
			});
		} finally {
			marked.forEach(function (el) { el.classList.add('is-selected'); });
		}

		/* Strip everything that only exists for interaction. */
		['#gridRect', '#ghostLayer'].forEach(function (sel) {
			var el = clone.querySelector(sel);
			if (el && el.parentNode) el.parentNode.removeChild(el);
		});
		Array.prototype.slice.call(clone.querySelectorAll('.edge-hit'))
			.forEach(function (el) { if (el.parentNode) el.parentNode.removeChild(el); });

		/* The live transform is pan/zoom state; the export frames itself. */
		var vp = clone.querySelector('#viewport');
		if (vp) vp.removeAttribute('transform');

		clone.setAttribute('xmlns', SVGNS);
		clone.setAttribute('xmlns:xlink', 'http://www.w3.org/1999/xlink');
		clone.setAttribute('width', outW);
		clone.setAttribute('height', outH);
		clone.setAttribute('viewBox', box.x + ' ' + box.y + ' ' + box.w + ' ' + box.h);
		clone.removeAttribute('id');
		clone.removeAttribute('class');
		clone.removeAttribute('tabindex');

		/* The page background is CSS on the <svg>; a serialised copy has none,
		   so paint it explicitly or the PNG comes out transparent. Overhang the
		   viewBox slightly: an edge landing on a fractional device pixel leaves
		   the outermost row semi-transparent, which shows as a halo when the
		   image is dropped on a dark background. */
		var over = Math.max(box.w, box.h) * 0.01 + 2;
		var rect = document.createElementNS(SVGNS, 'rect');
		rect.setAttribute('x', box.x - over);
		rect.setAttribute('y', box.y - over);
		rect.setAttribute('width', box.w + over * 2);
		rect.setAttribute('height', box.h + over * 2);
		rect.setAttribute('fill', bg);
		var defs = clone.querySelector('defs');
		clone.insertBefore(rect, defs ? defs.nextSibling : clone.firstChild);

		return new XMLSerializer().serializeToString(clone);
	}

	function exportPNG() {
		var b = contentBounds();
		if (!b) { flash('Nothing to export.'); return; }

		/* Same framing as Fit, in graph units rather than screen pixels. */
		var pad = 40;
		var box = {
			x: b.minX - pad,
			y: b.minY - pad,
			w: Math.max(1, b.maxX - b.minX) + pad * 2,
			h: Math.max(1, b.maxY - b.minY) + pad * 2
		};

		/* Hold the aspect ratio and scale until the area hits the target, then
		   pull back if a side would exceed what canvas can allocate. */
		var scale = Math.sqrt(EXPORT_PIXELS / (box.w * box.h));
		var outW = Math.round(box.w * scale), outH = Math.round(box.h * scale);
		if (outW > EXPORT_MAX_SIDE || outH > EXPORT_MAX_SIDE) {
			scale *= Math.min(EXPORT_MAX_SIDE / outW, EXPORT_MAX_SIDE / outH);
			outW = Math.round(box.w * scale);
			outH = Math.round(box.h * scale);
		}

		var mp = (outW * outH / 1e6).toFixed(1);
		flash('Rendering ' + outW + '×' + outH + ' (' + mp + ' MP)…');

		var bg = exportBackground();
		var svgText;
		try {
			svgText = buildExportSVG(box, outW, outH, bg);
		} catch (err) {
			flash('Export failed while reading the diagram.');
			return;
		}

		var url = URL.createObjectURL(new Blob([svgText], { type: 'image/svg+xml;charset=utf-8' }));
		var img = new Image();

		img.onload = function () {
			var canvas = document.createElement('canvas');
			canvas.width = outW;
			canvas.height = outH;
			var ctx = canvas.getContext('2d');
			if (!ctx) { URL.revokeObjectURL(url); flash('Export failed: no canvas context.'); return; }

			/* Paint the backdrop on the canvas too, so every pixel is fully
			   opaque regardless of how the SVG edges land. */
			ctx.fillStyle = bg;
			ctx.fillRect(0, 0, outW, outH);
			ctx.drawImage(img, 0, 0, outW, outH);
			URL.revokeObjectURL(url);

			var finish = function (png) {
				if (!png) { flash('Export failed while encoding the PNG.'); return; }
				var name = slug(model.project) + '.png';
				downloadBlob(png, name);
				flash('Exported ' + name + ' — ' + outW + '×' + outH + ', ' + mp + ' MP');
			};
			if (canvas.toBlob) canvas.toBlob(finish, 'image/png');
			else finish(null);
		};

		img.onerror = function () {
			URL.revokeObjectURL(url);
			flash('Export failed while rasterising.');
		};

		img.src = url;
	}

	function slug(s) {
		var base = String(s || 'project').toLowerCase()
			.replace(/[^a-z0-9]+/g, '-')
			.replace(/^-+|-+$/g, '');
		if (!base) base = 'project';
		var d = new Date();
		var stamp = d.getFullYear() + '-' +
			String(d.getMonth() + 1).padStart(2, '0') + '-' +
			String(d.getDate()).padStart(2, '0');
		return base + '-' + stamp;
	}

	function loadFromFile(file) {
		var reader = new FileReader();
		reader.onload = function () {
			try {
				deserialize(JSON.parse(String(reader.result)));
				render();
				renderInspector();
				persist();
				flash('Opened ' + file.name);
			} catch (err) {
				flash('Could not open that file: ' + err.message);
			}
		};
		reader.onerror = function () { flash('Could not read that file.'); };
		reader.readAsText(file);
	}

	/* localStorage is best-effort — it can be unavailable on file:// or in
	   private browsing, and that must never break the editor. */
	function persist() {
		try {
			localStorage.setItem(STORAGE_KEY, JSON.stringify(serialize()));
		} catch (err) { /* no-op */ }
	}

	var persistTimer = null;
	function persistDebounced() {
		if (persistTimer) clearTimeout(persistTimer);
		persistTimer = setTimeout(persist, 400);
	}

	function restore() {
		try {
			var raw = localStorage.getItem(STORAGE_KEY);
			if (!raw) return false;
			deserialize(JSON.parse(raw));
			return true;
		} catch (err) {
			return false;
		}
	}

	/* ------------------------------------------------------------------ undo */

	function pushUndo() {
		try {
			undoStack.push(JSON.stringify(serialize()));
			if (undoStack.length > UNDO_LIMIT) undoStack.shift();
			redoStack = [];
		} catch (err) { /* no-op */ }
	}

	function undo() {
		if (!undoStack.length) { flash('Nothing to undo.'); return; }
		var current = JSON.stringify(serialize());
		var snapshot = undoStack.pop();
		try {
			deserialize(JSON.parse(snapshot));
			redoStack.push(current);
			render();
			renderInspector();
			persist();
			flash('Undone.');
		} catch (err) { flash('Could not undo.'); }
	}

	function redo() {
		if (!redoStack.length) { flash('Nothing to redo.'); return; }
		var current = JSON.stringify(serialize());
		var snapshot = redoStack.pop();
		try {
			deserialize(JSON.parse(snapshot));
			undoStack.push(current);
			render();
			renderInspector();
			persist();
			flash('Redone.');
		} catch (err) { flash('Could not redo.'); }
	}

	/* ---------------------------------------------------------- interactions */

	var pointers = {};          // pointerId -> {x, y}
	var pointerCount = 0;
	var drag = null;            // { ids, offs, clicked, moved }
	var pan = null;             // { sx, sy, vx, vy, moved }
	var pinch = null;           // { dist, k, cx, cy }
	var marquee = null;         // { x0, y0, x1, y1, sx, sy, moved, additive } world coords

	function nodeIdFromEvent(evt) {
		var t = evt.target;
		while (t && t !== svg) {
			if (t.dataset && t.dataset.nodeId) return t.dataset.nodeId;
			t = t.parentNode;
		}
		return null;
	}

	function edgeIdFromEvent(evt) {
		var t = evt.target;
		return (t && t.dataset && t.dataset.edgeId) ? t.dataset.edgeId : null;
	}

	/* Drop any half-finished gesture without touching the model. */
	function resetGesture() {
		pointers = {};
		pointerCount = 0;
		pinch = null;
		if (marquee) { marquee = null; svg.classList.remove('is-marqueeing'); clear(ghostLayer); }
		if (drag) {
			drag.ids.forEach(function (id) {
				var g = nodeEls[id];
				if (g) g.classList.remove('is-dragging');
			});
			drag = null;
		}
		if (pan) {
			svg.classList.remove('is-panning');
			pan = null;
		}
	}

	function nodesInRect(r) {
		var x0 = Math.min(r.x0, r.x1), x1 = Math.max(r.x0, r.x1);
		var y0 = Math.min(r.y0, r.y1), y1 = Math.max(r.y0, r.y1);
		/* Intersection, not containment: catching a node by clipping its corner
		   is far less fiddly than having to lasso it whole. */
		return allNodes().filter(function (n) {
			return n.x < x1 && n.x + nodeW(n) > x0 &&
			       n.y < y1 && n.y + nodeH(n) > y0;
		}).map(function (n) { return n.id; });
	}

	function drawMarquee() {
		clear(ghostLayer);
		if (!marquee) return;
		el('rect', {
			'class': 'marquee',
			x: Math.min(marquee.x0, marquee.x1),
			y: Math.min(marquee.y0, marquee.y1),
			width: Math.abs(marquee.x1 - marquee.x0),
			height: Math.abs(marquee.y1 - marquee.y0),
			'vector-effect': 'non-scaling-stroke'
		}, ghostLayer);
	}

	function onPointerDown(evt) {
		/* Middle button is allowed through so it can pan; other buttons are not. */
		if (evt.pointerType === 'mouse' && evt.button !== 0 && evt.button !== 1) return;

		/* A primary pointer means a brand new gesture is starting, so anything
		   still in the map is a pointerup we never heard about — released off
		   the window, capture lost, or a modal dialog swallowing the event.
		   Without this the leftovers make the next tap look like a two-finger
		   pinch and the editor stops responding until reload. */
		if (evt.isPrimary) resetGesture();

		pointers[evt.pointerId] = { x: evt.clientX, y: evt.clientY };
		pointerCount = Object.keys(pointers).length;

		if (pointerCount === 2) {
			drag = null; pan = null;
			if (marquee) { marquee = null; svg.classList.remove('is-marqueeing'); clear(ghostLayer); }
			var ids = Object.keys(pointers);
			var p1 = pointers[ids[0]], p2 = pointers[ids[1]];
			var rect = svg.getBoundingClientRect();
			pinch = {
				dist: Math.hypot(p2.x - p1.x, p2.y - p1.y),
				k: view.k,
				cx: (p1.x + p2.x) / 2 - rect.left,
				cy: (p1.y + p2.y) / 2 - rect.top
			};
			return;
		}
		if (pointerCount > 2) return;

		/* Capture can legitimately fail (stale pointer id, synthetic event);
		   losing it only costs us tracking outside the element. */
		try { svg.setPointerCapture(evt.pointerId); } catch (err) { /* no-op */ }

		var nodeId = nodeIdFromEvent(evt);

		if (connectMode) {
			if (nodeId) handleConnectClick(nodeId);
			else cancelConnect('Connection cancelled.');
			return;
		}

		if (nodeId) {
			if (evt.shiftKey) { toggleInSelection(nodeId); return; }

			/* Grabbing a node that is already part of a multi-selection drags the
			   whole set; grabbing anything else drags just that node. */
			var group = isSelected('node', nodeId) ? selectedIds().slice() : [nodeId];
			var w = screenToWorld(localPoint(evt).x, localPoint(evt).y);
			var offs = {};
			group.forEach(function (id) {
				var nd = model.nodes[id];
				if (nd) offs[id] = { dx: w.x - nd.x, dy: w.y - nd.y };
			});
			group = Object.keys(offs);
			drag = { ids: group, offs: offs, clicked: nodeId, moved: false };
			group.forEach(function (id) {
				var g = nodeEls[id];
				if (g) g.classList.add('is-dragging');
			});
			return;
		}

		var edgeId = edgeIdFromEvent(evt);
		if (edgeId) { select('edge', edgeId); return; }

		var lp = localPoint(evt);

		/* Empty canvas. A mouse rubber-band selects; Shift or the middle button
		   pans instead. Touch always pans, because there is no Shift on a phone
		   and one-finger panning is the expected gesture. */
		var wantsPan = evt.pointerType !== 'mouse' || evt.shiftKey || evt.button === 1;
		if (wantsPan) {
			pan = { sx: lp.x, sy: lp.y, vx: view.x, vy: view.y, moved: false };
			svg.classList.add('is-panning');
			return;
		}

		var wp = screenToWorld(lp.x, lp.y);
		marquee = {
			x0: wp.x, y0: wp.y, x1: wp.x, y1: wp.y,
			sx: lp.x, sy: lp.y, moved: false,
			additive: evt.ctrlKey || evt.metaKey
		};
		svg.classList.add('is-marqueeing');
	}

	function onPointerMove(evt) {
		if (pointers[evt.pointerId]) {
			pointers[evt.pointerId].x = evt.clientX;
			pointers[evt.pointerId].y = evt.clientY;
		}

		if (pinch) {
			var ids = Object.keys(pointers);
			if (ids.length < 2) return;
			var p1 = pointers[ids[0]], p2 = pointers[ids[1]];
			var dist = Math.hypot(p2.x - p1.x, p2.y - p1.y);
			if (!pinch.dist) return;
			var target = Math.min(MAX_K, Math.max(MIN_K, pinch.k * (dist / pinch.dist)));
			var factor = target / view.k;
			zoomAt(pinch.cx, pinch.cy, factor);
			return;
		}

		if (marquee) {
			var mp = localPoint(evt);
			if (Math.abs(mp.x - marquee.sx) > 3 || Math.abs(mp.y - marquee.sy) > 3) marquee.moved = true;
			var mw = screenToWorld(mp.x, mp.y);
			marquee.x1 = mw.x;
			marquee.y1 = mw.y;
			drawMarquee();
			return;
		}

		if (drag) {
			var w = screenToWorld(localPoint(evt).x, localPoint(evt).y);

			/* Snapshot before the first real movement, so undo restores the
			   whole group's original positions in one step. */
			if (!drag.moved) {
				var lead = model.nodes[drag.ids[0]];
				var o0 = drag.offs[drag.ids[0]];
				if (lead && o0 &&
					(Math.abs(Math.round(w.x - o0.dx) - lead.x) > 2 ||
					 Math.abs(Math.round(w.y - o0.dy) - lead.y) > 2)) {
					pushUndo();
					drag.moved = true;
				}
			}

			drag.ids.forEach(function (id) {
				var nd = model.nodes[id], o = drag.offs[id];
				if (!nd || !o) return;
				nd.x = Math.round(w.x - o.dx);
				nd.y = Math.round(w.y - o.dy);
			});
			moveNodeEls(drag.ids);      /* one re-route for the whole group */
			return;
		}

		if (pan) {
			var lp = localPoint(evt);
			var ddx = lp.x - pan.sx, ddy = lp.y - pan.sy;
			if (Math.abs(ddx) > 3 || Math.abs(ddy) > 3) pan.moved = true;
			view.x = pan.vx + ddx;
			view.y = pan.vy + ddy;
			applyViewTransform();
		}
	}

	function onPointerUp(evt) {
		delete pointers[evt.pointerId];
		pointerCount = Object.keys(pointers).length;

		try {
			if (svg.hasPointerCapture && svg.hasPointerCapture(evt.pointerId)) {
				svg.releasePointerCapture(evt.pointerId);
			}
		} catch (err) { /* no-op */ }

		if (pinch) {
			if (pointerCount < 2) pinch = null;
			return;
		}

		if (marquee) {
			svg.classList.remove('is-marqueeing');
			var box = marquee;
			marquee = null;
			clear(ghostLayer);

			if (!box.moved) {
				/* A click on empty canvas, not a drag: clear the selection. */
				if (selection) select(null, null);
				return;
			}

			var hits = nodesInRect(box);
			if (box.additive && selection && selection.kind === 'node') {
				selection.ids.forEach(function (id) {
					if (hits.indexOf(id) < 0) hits.push(id);
				});
			}
			select(hits.length ? 'node' : null, hits);
			if (hits.length) {
				flash(hits.length === 1 ? '1 node selected.' : hits.length + ' nodes selected.');
			}
			return;
		}

		if (drag) {
			drag.ids.forEach(function (id) {
				var g = nodeEls[id];
				if (g) g.classList.remove('is-dragging');
			});
			if (drag.moved) { persist(); render(); }
			/* A click without movement collapses a multi-selection to that node. */
			else { select('node', drag.clicked); }
			drag = null;
			return;
		}

		if (pan) {
			svg.classList.remove('is-panning');
			if (!pan.moved && selection) select(null, null);
			pan = null;
		}
	}

	function onWheel(evt) {
		evt.preventDefault();
		var lp = localPoint(evt);
		var factor = evt.deltaY < 0 ? 1.12 : 1 / 1.12;
		zoomAt(lp.x, lp.y, factor);
	}

	/* --------------------------------------------------------- connect mode */

	function setConnectMode(on) {
		connectMode = !!on;
		connectFrom = null;
		$('btnConnect').setAttribute('aria-pressed', connectMode ? 'true' : 'false');
		svg.classList.toggle('is-connecting', connectMode);
		clear(ghostLayer);
		setHint(connectMode ? 'Connect: click the source node, then the target. Esc to cancel.' : '');
		render();
	}

	function handleConnectClick(nodeId) {
		if (!connectFrom) {
			if (nodeId === END_ID) { flash('Nothing can start from Project complete.'); return; }
			connectFrom = nodeId;
			setHint('Now click the target node. Esc to cancel.');
			render();
			return;
		}
		if (nodeId === connectFrom) { cancelConnect('Connection cancelled.'); return; }

		pushUndo();
		var result = connect(connectFrom, nodeId);
		if (!result.ok) {
			undoStack.pop();
			connectFrom = null;
			setHint('Connect: click the source node, then the target. Esc to cancel.');
			render();
			/* After render(), which rewrites the status bar — otherwise the
			   reason the connection was refused is wiped out instantly. */
			flash(result.msg);
			return;
		}

		connectFrom = null;
		setHint('Connect: click the source node, then the target. Esc to cancel.');
		render();
		renderInspector();
		persist();
		flash(result.msg);
	}

	function cancelConnect(msg) {
		connectFrom = null;
		if (connectMode) setHint('Connect: click the source node, then the target. Esc to cancel.');
		render();
		if (msg) flash(msg);
	}

	/* ------------------------------------------------------------- toolbar */

	function addTaskAtCentre() {
		pushUndo();
		var c = viewportCentre();
		var n = createTask(Math.round(c.x - TASK_W / 2 + jitter()), Math.round(c.y - TASK_H / 2 + jitter()));
		render();
		select('node', n.id);
		persist();
		flash('Task added, wired from Project start to Project complete.');
	}

	function addBarrierAtCentre() {
		pushUndo();
		var c = viewportCentre();
		var n = createBarrier(Math.round(c.x - BAR_W / 2 + jitter()), Math.round(c.y - BAR_H / 2 + jitter()));
		reattachDangling();
		render();
		select('node', n.id);
		persist();
		flash('Barrier added.');
	}

	/* Nudge new nodes apart so repeated clicks do not stack them. */
	var jitterN = 0;
	function jitter() {
		jitterN = (jitterN + 1) % 8;
		return jitterN * 26;
	}

	function newProject() {
		if (!window.confirm('Start a new project? Anything unsaved will be lost.')) return;
		model = emptyModel();
		reattachDangling();
		view = { x: 0, y: 0, k: 1 };
		selection = null;
		undoStack = [];
		redoStack = [];
		$('projectName').value = model.project;
		render();
		fitToView();
		renderInspector();
		persist();
		flash('New project.');
	}

	function showProblems() {
		if (!analysis || !analysis.problems.length) return;
		var lines = analysis.problems.map(function (p, i) {
			return (i + 1) + '. ' + p.msg;
		});
		window.alert('Issues in this net:\n\n' + lines.join('\n'));
		var first = analysis.problems[0];
		if (first.nodeId && model.nodes[first.nodeId]) select('node', first.nodeId);
	}

	/* --------------------------------------------------------------- sample */

	function seedExample() {
		var design = createTask(240, -140);
		design.label = 'Design';
		design.description = 'Sketch the architecture and agree the interfaces.';
		design.color = SWATCHES[0];
		design.state = 'completed';

		var build = createTask(600, -220);
		build.label = 'Build firmware';
		build.color = SWATCHES[2];

		var docs = createTask(600, -40);
		docs.label = 'Write documentation';
		docs.color = SWATCHES[3];

		var test = createTask(960, -140);
		test.label = 'Integration test';
		test.color = SWATCHES[1];

		/* design -> [build, docs] -> test, with barriers doing the sync. */
		connect(design.id, build.id);
		var mid = allNodes().filter(function (n) {
			return n.type === 'barrier' && !n.fixed;
		})[0];
		if (mid) {
			mid.label = 'Design signed off';
			connect(mid.id, docs.id);
		}
		connect(build.id, test.id);
		var join = allNodes().filter(function (n) {
			return n.type === 'barrier' && !n.fixed && n.id !== (mid && mid.id);
		})[0];
		if (join) {
			join.label = 'Ready to test';
			connect(docs.id, join.id);
		}
		reattachDangling();
	}

	/* ----------------------------------------------------------------- menu */

	function setMenu(open) {
		var menu = $('offcanvas_menu'), scrim = $('scrim'), toggle = $('menuToggle');
		menu.classList.toggle('is-open', open);
		menu.setAttribute('aria-hidden', open ? 'false' : 'true');
		toggle.setAttribute('aria-expanded', open ? 'true' : 'false');
		scrim.hidden = !open;
	}

	function setHelp(open) {
		$('helpModal').hidden = !open;
		if (!open) return;

		/* Focus the X at the top, not the button at the foot: focusing a control
		   below the fold scrolls the card to it and the dialog opens with its own
		   title and disclaimer already scrolled off screen. */
		var card = document.querySelector('#helpModal .modal-card');
		if (card) card.scrollTop = 0;
		var x = $('helpX');
		if (x) x.focus();
	}

	/* ---------------------------------------------------------------- theme */

	/* An explicit choice wins over the OS setting and is remembered. With no
	   choice stored we follow prefers-color-scheme, which is what the CSS does
	   on its own — so "auto" needs no attribute at all. */
	function systemTheme() {
		return (window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches)
			? 'dark' : 'light';
	}

	function currentTheme() {
		var attr = document.documentElement.getAttribute('data-theme');
		return (attr === 'light' || attr === 'dark') ? attr : systemTheme();
	}

	function setTheme(theme) {
		document.documentElement.setAttribute('data-theme', theme);
		try { localStorage.setItem(THEME_KEY, theme); } catch (err) { /* no-op */ }
		syncThemeButton();
	}

	function syncThemeButton() {
		var dark = currentTheme() === 'dark';
		var ico = $('themeIco');
		var btn = $('btnTheme');
		if (!ico || !btn) return;
		/* Show the destination, not the current state. */
		ico.textContent = dark ? '☀' : '☾';
		var label = dark ? 'Switch to light theme' : 'Switch to dark theme';
		btn.setAttribute('aria-label', label);
		btn.title = label;
	}

	/* ------------------------------------------------------------------ init */

	function init() {
		svg = $('canvas');
		viewportG = $('viewport');
		edgeLayer = $('edgeLayer');
		ghostLayer = $('ghostLayer');
		nodeLayer = $('nodeLayer');
		inspector = $('inspector');
		inspectorInner = $('inspectorInner');
		statusMsg = $('statusMsg');
		problemsBtn = $('problemsBtn');
		canvasHint = $('canvasHint');
		zoomControls = document.querySelector('.zoom-controls');

		var restored = restore();
		if (!restored) { seedExample(); layoutGraph(); }

		$('projectName').value = model.project;
		$('projectName').addEventListener('input', function () {
			model.project = this.value;
			persistDebounced();
		});

		/* toolbar */
		$('btnAddTask').addEventListener('click', addTaskAtCentre);
		$('btnAddBarrier').addEventListener('click', addBarrierAtCentre);
		$('btnConnect').addEventListener('click', function () { setConnectMode(!connectMode); });
		$('btnArrange').addEventListener('click', autoArrange);
		$('btnFit').addEventListener('click', fitToView);
		$('btnSave').addEventListener('click', saveToFile);
		$('btnExport').addEventListener('click', exportPNG);
		$('btnNew').addEventListener('click', newProject);
		$('btnHelp').addEventListener('click', function () { setHelp(true); });
		$('helpClose').addEventListener('click', function () { setHelp(false); });
		$('helpX').addEventListener('click', function () { setHelp(false); });

		syncThemeButton();
		$('btnTheme').addEventListener('click', function () {
			setTheme(currentTheme() === 'dark' ? 'light' : 'dark');
		});

		/* With no explicit choice stored, keep following the OS if it changes
		   mid-session. Once the user picks a side we stop listening. */
		if (window.matchMedia) {
			var mq = window.matchMedia('(prefers-color-scheme: dark)');
			var onSystemChange = function () {
				if (!document.documentElement.getAttribute('data-theme')) syncThemeButton();
			};
			if (mq.addEventListener) mq.addEventListener('change', onSystemChange);
			else if (mq.addListener) mq.addListener(onSystemChange);
		}
		$('problemsBtn').addEventListener('click', showProblems);

		$('btnLoad').addEventListener('click', function () { $('fileInput').click(); });
		$('fileInput').addEventListener('change', function () {
			if (this.files && this.files[0]) loadFromFile(this.files[0]);
			this.value = '';                     // allow reopening the same file
		});

		$('btnZoomIn').addEventListener('click', function () { zoomAtCentre(1.2); });
		$('btnZoomOut').addEventListener('click', function () { zoomAtCentre(1 / 1.2); });
		$('btnZoomReset').addEventListener('click', function () {
			var rect = svg.getBoundingClientRect();
			zoomAt(rect.width / 2, rect.height / 2, 1 / view.k);
		});

		/* menu */
		$('menuToggle').addEventListener('click', function () {
			setMenu(!$('offcanvas_menu').classList.contains('is-open'));
		});
		$('scrim').addEventListener('click', function () { setMenu(false); });

		$('helpModal').addEventListener('click', function (e) {
			if (e.target === this) setHelp(false);
		});

		/* canvas */
		svg.addEventListener('pointerdown', onPointerDown);
		svg.addEventListener('pointermove', onPointerMove);
		/* Release is watched on the window so a pointer let go outside the
		   canvas still ends the drag instead of leaving it stuck to the cursor. */
		window.addEventListener('pointerup', onPointerUp);
		window.addEventListener('pointercancel', onPointerUp);
		svg.addEventListener('wheel', onWheel, { passive: false });
		svg.addEventListener('contextmenu', function (e) { e.preventDefault(); });

		document.addEventListener('keydown', onKeyDown);

		window.addEventListener('resize', function () {
			zoomControls.classList.toggle('is-lifted', !!selection && isSheet());
		});

		/* Keep the graph tidy if the user leaves and comes back. */
		window.addEventListener('beforeunload', persist);

		render();
		renderInspector();
		if (restored && isFinite(view.k)) applyViewTransform();
		else fitToView();

		/* The guide opens on every visit — it carries the disclaimer. */
		setHelp(true);
	}

	function zoomAtCentre(factor) {
		var rect = svg.getBoundingClientRect();
		zoomAt(rect.width / 2, rect.height / 2, factor);
	}

	function onKeyDown(e) {
		var tag = (e.target.tagName || '').toLowerCase();
		var typing = tag === 'input' || tag === 'textarea' || tag === 'select' || e.target.isContentEditable;

		/* Ctrl/Cmd shortcuts work even while typing. */
		if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 's') {
			e.preventDefault(); saveToFile(); return;
		}
		if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'a') {
			if (typing) return;
			e.preventDefault();
			var all = allNodes().map(function (n) { return n.id; });
			select('node', all);
			flash(all.length + ' nodes selected.');
			return;
		}
		if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') {
			if (typing) return;
			e.preventDefault();
			if (e.shiftKey) redo(); else undo();
			return;
		}

		if (e.key === 'Escape') {
			if (!$('helpModal').hidden) { setHelp(false); return; }
			if ($('offcanvas_menu').classList.contains('is-open')) { setMenu(false); return; }
			if (connectMode) { setConnectMode(false); return; }
			if (selection) select(null, null);
			if (typing) e.target.blur();
			return;
		}

		if (typing) return;

		if (e.key === 'Delete' || e.key === 'Backspace') {
			if (!selection) return;
			e.preventDefault();
			if (selection.kind === 'node') doDelete(selection.ids);
			else {
				pushUndo();
				removeEdge(selection.ids[0]);
				reattachDangling();
				selection = null;
				render();
				renderInspector();
				persist();
				flash('Link deleted.');
			}
			return;
		}

		switch (e.key.toLowerCase()) {
			case 't': addTaskAtCentre(); break;
			case 'b': addBarrierAtCentre(); break;
			case 'c': setConnectMode(!connectMode); break;
			case 'a': autoArrange(); break;
			case 'f': fitToView(); break;
			case 'e': exportPNG(); break;
			default: break;
		}
	}

	if (document.readyState === 'loading') {
		document.addEventListener('DOMContentLoaded', init);
	} else {
		init();
	}

})();
