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
- Built and compiled (`lake --old env lean`, no errors): `ScalingDataAndWeilPlanes`,
  `TheCorrespondenceAlgebra`, `TheScalingDatumOfAConfiguration`, `TheOrientationOfACycle`,
  `EulerFactorsAndPayment`; wired into `ArithmeticOrientationGeometry.lean`, umbrella imported by
  `MainTheorems.lean`. README first version written.
- Also built: `TheArchimedeanPlaceOrientsOrbitSegments`.
- Next: orientation rate = depth of the deepest seen zero (σ-version of the orientation theorem);
  multiplicity-blindness (Q3); battery (golden curve, cluster configuration); answers synthesis.

## Log
- 2026-10-24 — created; corpus survey of ACS (λ-ring, Lefschetz identity, envelope cone), AOT
  (Wiener algebra, trichotomy, width functor), SRT (bounded exponential sums, critical-line
  forcing), BiScale (translated-pairing envelope law), PNTPlus Brun–Titchmarsh.
