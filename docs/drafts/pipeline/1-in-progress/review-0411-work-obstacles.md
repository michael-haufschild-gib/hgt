# Formalization of review-0411 work obstacles

- **ID:** review-0411-work-obstacles
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0411/obstacles-summary.md`, §2.1.
- **Goal:** Resolve all 35 listed tasks with exact Lean statements and audited dependencies.

## Scope

Open: A1–A7, A9–A11, A13–A15, A17–A18, A20–A21, A23–A25, A28, A31, A33, A35–A36, A38. A row with several obligations remains
open until every obligation is discharged. Existing results are prerequisites, not new solutions.
No numerical experiments or trusted computation; certificates require kernel proofs.

**Closed:**

- A8, [even cosh-credit gauges](../3-formalized/even-cosh-credit-gauges.md):
  existing window-adapted signed theta gauges, positive on the window, with
  positive or zero cosh-charge coefficient and the exact retained-variance identity.
  Direct source check, eight transitive axiom audits, and import checks passed.
  This is existing mathematics; the remaining signed-energy inequality is unchanged.
- A12, [arithmetic heat identity](../3-formalized/gaussian-cone-coupling-arithmetic-heat-identity.md):
  the Gaussian kernel and coupling equal heat averages of the actual arithmetic Weil functional.
- A19, existing `ArithmeticIncidencePositivity.totalAntiDiagonalKernel_pos_forall_iff`:
  exactly `{2,3,4,5,7,8,9,11,13}`; every other modulus has nonpositive midpoint kernel.
  Direct source check and three transitive axiom audits passed; umbrella already imports it.
  This is existing mathematics, not a new result.
- A22, [Björner's wedge decomposition](../3-formalized/bjorner-wedge-realization.md):
  actual homotopy equivalence to Euclidean spheres of dimension `ω(m)−1`, indexed
  by odd squarefree `N/2<m≤N`; empty realization below the first prime.
- A26, [VK caps and WD receivers](../3-formalized/vinogradov-korobov-window-caps.md):
  zero-free outer rectangles at square-root prefixes, exact cap/source identities,
  and both fixed-degree and all-stage receivers after prefix enlargement.
- A27, [explicit cluster detectors](../3-formalized/explicit-cluster-detector-constant.md):
  global local-count constant `240`, numerical cluster and product apertures,
  smooth negative tests at a closed-form aperture, and an inverse depth bound.
- A29, [reflection-pair receiver bridge](../3-formalized/reflection-prime-count-receiver-bridge.md):
  all five requested receivers are equivalent to the exact smoothed-count band.
- A32, [Cayley–Li and Suzuki receivers](../3-formalized/cayley-li-and-suzuki-receivers.md):
  existing primitive-sign and complete first-variation receivers, including uniform
  grid-scale transfer. Three source checks and nine transitive axiom audits passed.
  This is existing mathematics, not a new result.
- A37, [growing simultaneous receiving](../3-formalized/growing-simultaneous-receiving-modes.md):
  monotone unbounded mode and conductor cutoffs, uniform receiving on bounded charge
  cubes, and profile-dependent cutoffs for arbitrary infinite real charge profiles.
  Direct source check, six transitive axiom audits, and umbrella wiring passed.

## Partial results and current target

**A3.** [Joint periodic windows](joint-periodic-window-coercivity.md):
the residue-averaged mass matrix and one high-frequency mean-value bound give
a candidate uniform coercivity proof for mixed twists and spatial profiles.

**A10.** For the window index `ι(A)`, define
`Lₙ = sup {A : ι(A) ≤ n}` in `EReal`. Prove
`ι(A) = #{n : Lₙ < A}`, local finiteness of the thresholds, and
`Lₙ < ∞ ↔ n < #{ρ : Re ρ > 1/2}`. The existing jump-multiple theorem
varies the critical ratio, not the length.

The [formalized theorem](../3-formalized/window-index-counts-critical-lengths.md)
uses inward dilation and finite-matrix inertia to prove continuity from below.
Both leaf checks, eight transitive axiom audits, and umbrella imports are complete.

**Remaining A10 scope:** `ArithmeticHodgeTheoryOfDegenerations/README.md`, §9.1,
also asks to close the gap between resolved right-zero counts and the Shannon bound,
and locate the critical multiples in terms of right zeros. Abstract critical-length
counting alone does not discharge that requirement.

## Other first candidates

- A7: evaluate the first-stage Schur complement.
- A28: the atomic-lattice spectral bound.
- A6: [graph-to-window converse](../3-formalized/rational-hecke-graphs-determine-window-positivity.md)
  by finite Følner averaging. The final source check and transitive axiom audit passed.
  The [finite-template reduction](../3-formalized/finite-templates-control-rational-hecke-graphs.md)
  also passed its final source check and axiom audit. Third-stage regimes split at `A=log(9/2)`:
  [seven vertices](../3-formalized/third-stage-tate-horizon-before-nine-halves.md),
  [twelve vertices](../3-formalized/third-stage-tate-horizon-after-nine-halves.md).
  The [24-vertex theorem](../3-formalized/fourth-stage-tate-horizon-before-eighty-one-sixteenths.md)
  gives the exact criterion for `log 5<A≤log(81/16)`; its final source check and
  four transitive axiom audits passed.
  Both third-stage sources passed their final direct checks and transitive axiom audits.
  [Infinite bounded Hecke orbits](../3-formalized/rational-hecke-orbits-at-ratio-six.md)
  are also formalized and audited: ratio-two and ratio-three edges already rule out
  finite closed templates at ratio six. The [sign distinction](../3-formalized/third-stage-tate-sign-frustration.md)
  is formalized and audited: dimension-one Tate positivity coexists with a smooth
  absolute-cost violation, ruling out the corresponding Barta weights.
  [Global Tate horizon](../3-formalized/tate-positivity-is-downward-closed-in-dimension.md):
  positive dimensions form a closed initial interval, with a positive endpoint above
  the first prime and an explicit positive floor below it. The intervals decrease
  in aperture and shrink to zero. Both final source checks and ten transitive
  axiom audits passed.
  Later stages and the critical balancing-weight obligation remain open.

## Scope corrections

- A36's original claims exceed the current formalized card. See
  [remaining obligations](onset-law-remaining-obligations.md), including the
  uniform RvM requirements. The [distinct-ordinate law](../3-formalized/distinct-coherent-clusters-have-the-multiplicity-threshold.md)
  and [complex-amplitude interferometer](../3-formalized/two-bump-interferometer-retains-complex-amplitudes.md)
  are formalized and audited; the full row remains open.

## Verification

Each completed theorem requires direct `lake --old env lean` checking, transitive
`#print axioms` inspection, and its owning umbrella import. A8, A12, A19, A22, A26, A27, A29, A32 and A37 satisfy all three.
