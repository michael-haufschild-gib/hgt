# Theta rank-three projective drift

- **ID:** S6F-PD
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `rh-current-frontier-map.md` · S6F/TCD finite physical-orbit gate
- **Statement:** On the physical theta source orbit, positivity of one exact projective drift numerator would make native rank-three order-eight curvature strictly increasing and close its remaining finite interval from seam positivity.

## Goal

Prove

```text
thetaCuspReflectedEighthSourceProjectiveDrift x > 0
```

for `0 < x < 137/2000`. This is a source-orbit sign law, not a reformulation assuming rank-three curvature positivity. Existing seam positivity plus the proved derivative identity would then discharge the remaining finite S6F/TCD physical-orbit positivity gate. Cofinal/all-order landing remains separate.

## Gates

- [x] 0 → 1 in-progress: exact source-pure observable and attack target; whole-chamber shortcut already excluded
- [ ] 1 → 2 fully-proven: prove drift positivity on physical interval with no numerical certificate or imported enclosure
- [ ] 2 → 3 formalized: formalize drift sign theorem and interval-to-curvature discharge
- [ ] 3 → 4 publication-ready: integrate with full S6F/TCD landing

## Exact bridge already formalized

`GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveDrift` proves unconditionally:

1. `projectiveValue = sourcePositiveD1Value.re / Q^6` has derivative `projectiveDrift / Q^7`;
2. for `x > 0`, `projectiveValue = 4 * thetaCuspFullReflectionEighthHankelCurvature`;
3. native rank-three curvature has derivative `projectiveDrift / (4 * Q^7)`;
4. since physical `Q > 0`, derivative positivity is equivalent to projective-drift positivity.

The Lean module contains no computation result, decimal, interval certificate, route premise, or added axiom. Targeted build and `#print axioms` pass; theorem dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

## Approach

Let `P` be the exact source-positive modular polynomial for raw rank-three D1, `L` its exact Lie derivative, and `Q` the literal positive source coordinate. The new numerator is

```text
N = Q * L(P) - 6 * P * L(Q).
```

Attack `N` only on the actual three-state theta trajectory. Search for an exact polynomial shear, invariant cone, barrier, or factorization built from already formalized positive/monotone source coordinates. First finite target is `0 < x < 137/2000`; do not promote to the whole source-positive orthant.

## Hostile audit

- **Killed shortcut:** positivity on the whole source-positive chamber is false; an exact rational seam state already makes the universal source-positive D1 polynomial negative.
- **Current attempted kill:** computation motivated testing the projective normalization, but contributes no theorem. It exposed no sign reversal on the finite physical interval. This is reconnaissance only.
- **Survivor:** exact physical-orbit drift sign. Status: `SURVIVES PRELIMINARY ATTACK`.
- **Next kill tests:** derive `N` explicitly in intrinsic coordinates; search exact admissible source-chamber counterstates; test whether every plausible cone/barrier includes the known negative rational state; inspect endpoint and cusp asymptotics symbolically before attempting interval proof.

## Literature position

Planat--Solé, *Second-Level Concavity of the Riemann Ξ Kernel* (arXiv:2608.19160), uses a related autonomous phase-space, elliptic-monotonicity, and polynomial-shear strategy at rank two. It does not prove this rank-three eighth-order drift sign. Salazar, *Order-Moment Transport and Hankel Determinants in Special-Function Inequalities* (arXiv:2606.31647), develops moment/total-positivity methods but does not supply this physical theta-orbit theorem. No novelty claim is made without a dedicated audit.

## Log

- 2026-08-29 — computation-free projective derivative bridge derived, formalized, targeted-build verified, and reduced to exact physical-orbit sign core.
- 2026-08-29 — A 2,000,001-point/27,400-Arb-box hostile follow-up found no negative drift;
  Arb certified all boxes from `0.00211` to `137/2000` and failed only near seam. Exact parity audit
  explains that failure: raw D1, projective D1, and `Q` are even; projective drift is odd and
  vanishes exactly at zero. These facts are now unconditional Lean theorems, independent of the
  run. Sharpened open core is positivity of desingularized drift `N(x)/x` on the finite interval,
  with exact second variation as seam value. Computation report:
  `../2-fully-proven/computations/2026-08-29-s6f-projective-drift-unimodality/REPORT.md`.
- 2026-08-29 — Exact rational recurrence discovery computed the physical-flow derivative of the
  projective drift at an arbitrary algebraic seam scale `X`.  After `X=191/10+Y`, all 15
  coefficients of its degree-14 numerator are strictly positive.  Thus the actual drift has the
  correct strict inward seam orientation; unresolved work begins with extending this sign along
  the physical orbit, not resolving the forced seam cancellation.  Diagnostic record:
  `../2-fully-proven/computations/2026-08-29-modular-seam-certificate-discovery/REPORT.md`.
  The same exact recurrence kills local absolute monotonicity: the third physical-flow derivative
  has all shifted coefficients strictly negative, while the fifth has all shifted coefficients
  strictly positive.  The surviving local candidate is alternating/Stieltjes-like odd-jet
  structure.  Paper rederivation and computation-free Lean formalization remain pending.
- 2026-08-29 — Normalized-clock search factors exact physical drift as
  `projectiveDrift/R = z*C(X,z,y)`, with `v=z*y`. Whole physical simplex is false: exact rational
  state `X=199989/10000`, `z=465/1000`, `y=999/1000` has `Q>0` and negative `C`. For chamber
  `191/10<=X<=20`, `0<=y<=1`, `0<=z<=3/10`, all 10,584 exact diagnostic Bernstein coefficients
  are positive. This certificate is reconnaissance and is forbidden as Lean input. Report:
  `../2-fully-proven/computations/2026-08-29-s6f-normalized-chamber-search/REPORT.md`.
- 2026-08-29 — Trajectory-localization survivor was independently rederived and formalized without
  computational input. New module
  `ThetaCuspFullReflectionEighthProjectiveClockChamber` sharpens theta mass to `<2173/2000`, proves
  seam scale squared `<360000/18769`, bounds modular-lambda speed by `600/137`, and proves
  `-Z(x)<3/10` for every `0<x<137/2000`. Targeted module build and axiom audit pass. Remaining open
  core is now only computation-free positivity of `C` on this rational chamber, followed by
  existing derivative bridge. Next kill attempt must find compact algebraic decomposition or an
  exact counterexample inside `z<3/10`; copying computed coefficient table into Lean is forbidden.
- 2026-08-29 — Exact coordinate-monotonicity attack partially succeeds and sharply compresses open
  core. On normalized cube, diagnostic Bernstein certificates make `C` strictly increasing in
  `X` and nonincreasing in `z`; monotonicity in `y` is false. Thus chamber positivity reduces to
  degree-27 boundary polynomial `C(191/10,3/10,y)`, whose 28 univariate Bernstein coefficients are
  all strictly positive. Independent exact verifier passes. Report:
  `../2-fully-proven/computations/2026-08-29-s6f-monotonicity-hostile/REPORT.md`. Computed
  coefficients remain forbidden in Lean. New paper target is two compact derivative-sign
  decompositions plus one degree-27 univariate positive decomposition, not original
  three-variable 10,584-coefficient table.
- 2026-08-29 — Thin-clock-cone attack materially sharpens physical orbit. Exact modular ODE proves,
  without computational input, `(2/5)z < v < (1/2)z` throughout `0<x<137/2000`; theorem is
  formalized as `thetaCuspModularProjectiveClocks_mem_thinCone`. Lower wall is global consequence
  of discriminant gap `<20`; upper wall uses increasing scale square `>191/10`, existing
  `z<3/10`, and strict clock simplex. Independent RunPod diagnostics then find `C>0` not only for
  `X<=20` but on full half-cone `X>=191/10`, `0<=z<=3/10`, `2/5<=y<=1/2`; `C` is concave in `y`
  there, while direct `y` monotonicity remains false. Exact verifier passes. Report:
  `../2-fully-proven/computations/2026-08-29-s6f-thin-clock-cone/REPORT.md`. Computed certificates
  remain forbidden in Lean. Open core is now conceptual proof of one half-cone polynomial sign;
  no upper scale bound is needed.
- 2026-08-29 — Failure-driven wall iteration sharpens actual clock ratio again, now entirely by
  paper algebra and Lean: `13/32 < y < 7/16` on `0<x<137/2000`. Lower wall uses exact source gap
  `A<(600/137)^2<96/5`; upper wall then uses lower ratio, `X>191/10`, and `z<3/10`. Main theorem
  `thetaCuspModularProjectiveClocks_mem_sharpThinCone` passes direct Lean, exact-module build, and
  axiom audit. New RunPod hostile search kills ordinary danger-slack and intrinsic ratio-only
  shortcuts: `(B,Q,U)=(1,1,5/2)` has negative projective drift despite `2B<U<3B`, so physical
  amplitude cap is essential. On formal sharp cone, direct `y` monotonicity revives: diagnostics
  find `C_X>0`, `C_z<=0`, and `C_y>0`, reducing remaining sign to exact corner
  `C(191/10,3/10,13/32)>0`. Tables remain forbidden in Lean. Report:
  `../2-fully-proven/computations/2026-08-29-s6f-conceptual-certificate-search/REPORT.md`.
- 2026-08-29 — Failure of the positive-Laplace/Vandermonde interpretation led to a stronger
  ODE-native survivor. Exact paper algebra and Lean now prove the parabolic physical cone
  `(13/32+z^2/32)z < v < (33/80+z^2/12)z` and
  `191/10+(147/20)z^2 < X`. Main theorem
  `thetaCuspModularProjectiveClocks_mem_parabolicThinCone` passes scratch, tree source, exact-module
  build, and axiom audit. No computed result enters it.
- 2026-08-29 — Exact RunPod hostile test kills the hoped-for increasing and completely monotone
  parabolic drift laws. On the formal lower wall, diagnostic `C_p` is positive, strictly decreasing,
  strictly convex in `w=z^2`, and increasing in scale slack; the sign-corrected third derivative is
  already mixed. Ordinary outer-slack coefficients are mixed as well. Strong survivor reduces the
  trajectory-faithful diagnostic minimum to outer corner
  `(X,z,y)=(39523/2000,3/10,1309/3200)`. Remaining paper core is a conceptual proof of the combined
  signs `dC_p/dS>0`, `dC_p/dw<0` and that corner sign, not a Stieltjes hierarchy. Independent exact
  verifier passes. Report:
  `../2-fully-proven/computations/2026-08-29-s6f-parabolic-cone-hostile/REPORT.md`.
- 2026-08-29 — Direct determinant hostile test supersedes projective drift as the primary finite
  route without falsifying it. Native D1 itself is diagnostically positive on the full old
  parabolic cone, increasing/convex in scale slack and concave in `w=z²`; the alternating hierarchy
  fails at order four, and source/gap-coordinate factorization is irreducible. A computation-free
  ODE proof then sharpened the physical cone to
  `v<(33/80+z²/16)z`, `X>191/10+(37/5)z²`, now Lean-proved. Active successor card:
  `theta-rank-three-direct-parabolic-determinant.md`. Computation report:
  `../2-fully-proven/computations/2026-08-29-s6f-parabolic-d1-contact/REPORT.md`.
