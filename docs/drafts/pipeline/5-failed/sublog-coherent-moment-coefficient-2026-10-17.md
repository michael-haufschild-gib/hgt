# A universally smaller coherent moment coefficient is impossible

- **ID:** sublog-coherent-moment-coefficient
- **Stage:** 5-failed
- **Type:** FALSIFIED (Lean); positive survivor and full capstone formalized
- **Source:** ../1-in-progress/hyperbolic-multiplier-lifting-2026-10-17.md
- **Statement tested:** Replace log2 by a smaller universal coefficient in
  O(F)²<=log2*C_exact(F) for every actual compact continuous odd source F,
  while retaining the same full signed coherent price.

## Exact obstruction

Write d=log2. The explicit source F_1 below has O(F_1)=d and
C_exact(F_1)=d. A coefficient c therefore requires d²<=c*d, hence d<=c.
More precisely, `coherent_moment_constant_iff` proves that the universal
inequality holds exactly for coefficients c>=d. No analytic or blindness
premise remains unproved.

## Strongest positive survivor

Let t(x)=max(0,1-|x|), p(u)=(t(u/d-2)+t(u/d+2))/2, and
F_a(u)=a*p(u)/sinh(u/2). The profile is even, compact, and vanishes
on [-d,d]. Thus F_a is an actual compact continuous odd source and its
sinh multiplier is exactly a*p everywhere, including0.

Its fold is a throughout the unit cell, so
O(F_a)=d*a, E_cell(F_a)=0 and C_exact(F_a)=d*a². Also F_a=0 iff a=0.
This constructs nonzero-mean equality cases and evaluates their complete
signed coherent price; it is stronger than a bare obstruction to improvement.
The full functional transfer is
I_opt(F_a,N)+R_plastic(F_a)-2d²a²<=P_plastic(F_a).

## New insight and boundary

Exact coherent moment pricing is attained in the actual odd hyperbolic
image. Finite-filter Cauchy--Schwarz pricing is still strictly unattained
for nonzero sources, as contribution19 proves. These are different prices.

Only a smaller universal scalar coefficient on the full compact-continuous
odd source class is retired. Source-dependent cell corrections, other price
functionals, and extra source constraints remain possible. This result does
not establish source-grid blindness or differentiability beyond continuity,
and makes no universal plastic positivity claim.

## Proof status

- [x] Well-posed source-pure universal coefficient question.
- [x] Dependency-closed paper proof and explicit positive survivor.
- [x] Exact source construction, survivor and full capstone compile in Lean.
- [x] Public theorem axiom audit complete.

Module: `formal/GaloisForLFunctions/BiScaleUncertainty/CoherentMomentAttainment.lean`.
Key declarations in namespace `CoherentMomentAttainment`:
`attainingSource`, `sinhCompact_attainingSource`, `cellFold_attainingSource`,
`moment_attainingSource`, `exactBudget_attainingSource`,
`coherent_moment_constant_iff`, `plastic_attainingSource_bound`.

Actual-source audit53536 exited0 without warnings. Source SHA256
`f97dc36c6f8330117cdf3ebc823250ff6dd79573fe9f4d6f06123684beb3b161`.
All12 public theorem axiom audits9459 exited0 without warnings, using only
`propext`, `Classical.choice`, `Quot.sound`. User requires leaf audits rather
than full builds; no umbrella build was run. Local corpus audit found no
actual attainment predecessor; no external priority claim.
Umbrella wired; all14 public declarations indexed. Global lint independently
reports unrelated modules and concurrent generated drift; exact snapshot on
the master card. No repository-wide clean-gate claim.
