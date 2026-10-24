# Arithmetic Orientation Geometry (AOG)

- **ID:** arithmetic-orientation-geometry-2026-10-24
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — research programme
- **Source:** `docs/reports/review-2410/hard-obstacles-summary.md` §2.3 (the proposed field)
- **Statement:** Develop the geometry of the scaling correspondence: how the sign of the
  Castelnuovo–Severi defect propagates along the scaling (Frobenius) orbit of a cycle, which
  arithmetic structures can orient it, and which cannot.

## Goal
A Lean programme `formal/GaloisForLFunctions/ArithmeticOrientationGeometry/` with umbrella
`ArithmeticOrientationGeometry.lean`, a foundational README, and unconditional theorems answering
the seven questions and building the six tools of the summary §2.3.

## Plan (topics → modules)
- **A. Scaling data and Weil planes.** Abstract polar surface with a scaling action; orbit
  correlation `c_x(t) = δ(ψ_t x, x)`; Lefschetz number and Lefschetz–adjunction identity for every
  scaling datum; Weil-plane Castelnuovo–Severi ⇔ Hasse–Weil; orbit Hodge index; instance ℤ.
- **B. Correspondence algebra.** Group algebra of the scale group acting on cycles; Rosati
  involution; trace at a cycle; Rosati positivity ⇔ orbit Hodge index (Weil's second proof shape).
- **C. Orbit spectral theory on configurations.** Orbit correlation as an exponential sum over
  zeros; self-upgrade bounded ⇔ positive; orientation index = number of seen right zeros; growth
  rate = deepest seen zero; model computations (curves, golden, shifted pair, clusters).
- **D. Euler products on the Bohr polydisk (Q5).** Payment of the damped Möbius receiver is
  invariant under every finite set of Euler factors (tail law); absolute-convergence region.
- **E. Sieve half-orientation.** One-sided Lefschetz bound for narrow nonnegative cycles from
  Brun–Titchmarsh, uniform in width; the missing half.
- **F. Selectivity of orientation mechanisms.** Soft-structure no-go with the battery models.
- **G. Answers to Q1–Q7** as theorems; README.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized: modules compiled with `lake --old env lean`, wired, no axioms/sorries
- [ ] 3 → 4  publication-ready: README

## Status
- Compiled with `lake --old env lean`, `#print axioms` audited (propext, Classical.choice,
  Quot.sound only), wired into `ArithmeticOrientationGeometry.lean`: `ScalingDataAndWeilPlanes`,
  `TheCorrespondenceAlgebra`, `TheScalingDatumOfAConfiguration`, `TheOrientationOfACycle`,
  `EulerFactorsAndPayment`, `TheArchimedeanPlaceOrientsOrbitSegments`,
  `TheOrientationRateIsTheDepthOfTheDeepestSeenZero`, `TheSelectivityBatteryOfOrientation`,
  `TheShiftedPairAndTheClusterModels`, `SectionsOnTheOrbitOfACycle`, `EventualHasseWeilIsHasseWeil`,
  `TheOrientationIndexOfACycle`, `CorrectorsAndTheLefschetzTrace` (topics A–D, F, G),
  `TheOrientationOfScaleStableFamilies`, `TheThetaH0OfSpecZ`, `CorrectorsInTheDampingParameter`,
  `QuantitativeReadingsOnCurveOrbits` (topics H–K).
- Not built: topic E (sieve one-sided Lefschetz bound).
- Open: ℤ shifted pair as a zero-side datum (its zeros leave the strip unless the zero width is
  below `½ − a`); planted Euler factors; parity twins; mechanism equivalence; surface `h⁰` for
  classes with a test component; quantitative readings over ℤ.

## Plan: the four remaining tools
- **H. Families beyond single orbits** (`OrientationOfScaleStableSubspaces`): joint blindness of a
  subspace of tests; Hodge index of a scale-stable subspace ⇔ joint blindness (FES configs; union of
  two subspaces argument); maximal oriented subspaces indexed by choice functions; index of a
  scale-stable subspace = number of jointly seen right zeros (generic element + seen configuration);
  Riemann–Roch on multi-orbit surfaces.
- **I. Arithmetic `h⁰` of `Spec ℤ`** (`TheThetaSectionsOfSpecZ`): `h⁰(d) = log Σ_n e^{−πn²e^{−2d}}`;
  Riemann–Roch `h⁰(d) − h⁰(−d) = d` by Poisson (Jacobi); positivity, monotonicity, limits; product
  `h⁰` on the pole plane with `h⁰(D) − h⁰(−D) = D·(H + V)`; Mellin link to `Λ(s)` if available.
- **J. Correctors in the damping parameter** (`CorrectorsInTheDampingParameter`): damping as the
  character automorphisms `ξ ↦ e^{−εs}ξ` of the correspondence algebra; damped Lefschetz trace and
  damped correctors; damped orbit energy `E_x(ε) = sup_t e^{−εt}|c_x(t)|`, finite iff blind above `ε`;
  finiteness at every `ε > 0` (any constants) ⇒ `E_x(0) = c_x(0)` (orientation).
- **K. Quantitative readings** (`QuantitativeReadingsOnCurveOrbits`): on a curve configuration the orbit
  correlation at lags `ν log q` is a weighted power sum over the `2g` eigenvalues; Turán
  (`HTGeometry.exists_norm_weightedPowerSum_ge_scaled`) gives a violating scale in every window
  `[M + 1, M + 2g]` with explicit precision; contrast: finite windows over `ℤ` admit mimics.

## Log
- 2026-10-24 — created; corpus survey of ACS (λ-ring, Lefschetz identity, envelope cone), AOT
  (Wiener algebra, trichotomy, width functor), SRT (bounded exponential sums, critical-line
  forcing), BiScale (translated-pairing envelope law), PNTPlus Brun–Titchmarsh.
