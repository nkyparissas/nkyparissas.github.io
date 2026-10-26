/* ==========================================================================
   /bp: example programs. Each one is chosen to make some predictor shine
   and another struggle.

   Copyright (c) 2026 Nick Kyparissas
   Licensed under CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
   ========================================================================== */

(function (BP) {
	'use strict';

	const EXAMPLES = [
		{
			name: 'Mixed: data-dependent and periodic',
			src: `// One data-dependent branch, one periodic branch, two loops.
// Compare 2bc, GAg and PAg: which branch does each one learn?
int a[256] = rand(-9, 9);
int sum = 0;
for (int r = 0; r < 4; r++) {
    for (int i = 0; i < 256; i++) {
        if (a[i] > 0)          // depends on the data: hard
            sum += a[i];
        if ((i & 3) == 0)      // period 4: needs history
            sum ^= i;
    }
}
`
		},
		{
			name: 'Loop exits (local history, Sec. II-A)',
			src: `// The inner loop test is taken 4 times, then falls through:
// a T T T T N pattern. Per-address history (PAg, PAp) learns
// the exit; a plain counter (2bc) mispredicts it every time.
int s = 0;
for (int i = 0; i < 1000; i++) {
    for (int j = 0; j < 4; j++)
        s += j;
}
`
		},
		{
			name: 'Correlated branches (Fig. 6a)',
			src: `// Pan et al., Fig. 6(a): B3 is decided by B1 and B2.
// p and q start as 1 or 2; after B1 and B2, p != q exactly
// when one of them was 2. A (2,2) correlation predictor or a
// global-history predictor learns B3; 2bc is a coin toss.
int hits = 0;
for (int n = 0; n < 2000; n++) {
    int p = rand(1, 2);
    int q = rand(1, 2);
    if (p == 2)        // B1
        p = 0;
    if (q == 2)        // B2
        q = 0;
    if (p != q)        // B3
        hits++;
}
`
		},
		{
			name: 'Aliasing stress: twelve periodic branches',
			src: `// Twelve branches with periods 2 to 13 in one loop body.
// Shrink the tables (fewer rows, smaller k, m or a) and watch
// them turn orange and red as branches start to collide.
int x = 0;
for (int i = 0; i < 2000; i++) {
    if (i % 2 == 0) x++;
    if (i % 3 == 0) x++;
    if (i % 4 == 0) x++;
    if (i % 5 == 0) x++;
    if (i % 6 == 0) x++;
    if (i % 7 == 0) x++;
    if (i % 8 == 0) x--;
    if (i % 9 == 0) x--;
    if (i % 10 == 0) x--;
    if (i % 11 == 0) x--;
    if (i % 12 == 0) x--;
    if (i % 13 == 0) x--;
}
`
		},
		{
			name: 'Bubble sort',
			src: `// The swap test depends on the data, but becomes biased
// as the array gets sorted; the inner loop bound shrinks.
int a[48] = rand(0, 999);
for (int i = 0; i < 47; i++) {
    for (int j = 0; j < 47 - i; j++) {
        if (a[j] > a[j + 1]) {
            int t = a[j];
            a[j] = a[j + 1];
            a[j + 1] = t;
        }
    }
}
`
		},
		{
			name: 'Short-circuit && and ||',
			src: `// Every && and || is its own conditional branch,
// so one if statement here becomes three branches.
int c = 0;
for (int i = 0; i < 1500; i++) {
    int v = rand(0, 9);
    if (v > 2 && v < 7 || i % 5 == 0)
        c++;
}
`
		}
	];

	BP.examples = { EXAMPLES };

})(window.BP = window.BP || {});
