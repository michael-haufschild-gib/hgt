# TT C89 — Convexity of the kinetic first derivative

- Stage: 5-failed shape candidate; Route TT and direct monotonicity remain active.
- Parent: `../1-in-progress/tt-kinetic-contraction-source.md`.
- Lean: scratch proofs complete, standard axioms only. Nine production leaves,
  164 declarations staged and wired; direct/imported production audits pending.

Candidate: the complete reduced source P has P''' >= 0 on the positive-drift
clock box. Then P' would be convex, and C88's two negative endpoint derivatives
would force P' < 0 throughout the interval. C88 endpoint signs are proved;
this proposed shape mechanism is false.

The exact source structure gives P''' = V times a complete degree16 core.
At z=0 and V=9-r*h², this core is h⁵*Q(h,r). Q has179 monomials and degree34
in h and8 in r. All contributing source rows and drift columns are retained.
All nine coefficients of its final clock tensor row are strictly negative.
Exact Bernstein reconstruction therefore proves Q(4/5,r)<0 for EVERY
0<=r<=361/25, not merely negativity of an isolated certificate coefficient.

Whenever V=9-r*(4/5)²>0, the full P'''(0) is strictly negative. Continuity
extends this to small positive z. Convexity of P' would make P'' monotone,
contradicting that negative derivative at an interior point. Thus P' is NOT
convex on ANY interval [0,Z] with Z>0 at this clock and every such drift.
This is a shape obstruction; it does not falsify P'<0 or RH.

Positive survivor: exact drift-independent normalized clock-zero value

    Q(0,r)=615974148349919265846014022600622080 > 0.

For every fixed real r, continuity gives strictly positive full P'''(0)
at sufficiently small positive clock, with positive V proved there.
For EACH0<=r<=361/25, continuity and the high-clock negative sign give an
intrinsic normalized clock root h in(0,4/5), Q(h,r)=0. The full third
derivative vanishes there by the exact factorization; the root is not caused
by discarding source terms or merely setting the clock to zero.

Paper proof and scratch dependencies are closed. Capstones:
`thirdValue_initial_defect_factor`,
`thirdInitialQuotient_high_clock_neg`,
`kineticSlope_nonconvex_high_clock`,
`reducedKineticThirdValue_initial_small_clock_pos`,
`thirdInitialQuotient_clock_root`,
`reducedKineticThirdValue_initial_clock_root`.
Production manifest: `/tmp/tt_c89_shape_production_manifest.json`.

Next hard attack: prove the complete negative first derivative directly,
starting with interior Bernstein control17. Endpoint controls0 and18 are
closed. Full physical source sign, source quadratic, fourth Schur gap,
compact join, all-rank closure and RH remain open.
