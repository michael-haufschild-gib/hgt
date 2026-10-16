# CHMD: dimension of the bound-state space; RH ⟺ dim P = 1

- **ID:** chmd-bound-state-dimension-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional
- **Source:** CHMD route; closes chmd-bound-state-inertia (MUST-1557) and chmd-quarter-zero-bound (MUST-1558)
- **Statement:** (1) eigenvectors of `R` for distinct eigenvalues are orthogonal; on combinations of eigenvectors with eigenvalues `≥ a`, `⟪Ru,u⟫ ≥ a‖u‖²`. (2) `a > ½` and `⟪Ru,u⟫ ≥ a‖u‖²` give `E(Riesz u) ≤ −a(2a−1)‖u‖²`. (3) The span of finitely many bound states above `½` has dimension `≤ 2·#quarter + 1` (off-line set finite). (4) `P` is finite-dimensional with `dim P ≤ 2·#quarter + 1`. (5) `RH ⟺ dim P = 1` (no finiteness needed). (6) `weilNegIndex ζ a ε ≤ 2·#quarter + 1`; visible separated deep zero sets have `|T| ≤ 2·#quarter + 3`.
- **Status:** STATUS MUST-1559. One leaf (`CHMDBoundStateDimension`; 12 declarations), standard axioms; `lake env lean` clean; `lake build --old` green; wired; global lint clean of proof debt (remaining error is another agent's unwired `PaperThetaContourFubini`).

## Gates
- [x] 0 → 1, [x] 1 → 2, [x] 2 → 3 (`inner_resolvent_sum_ge`, `finrank_span_eigen_le`, `finiteDimensional_boundStateSpace`, `finrank_boundStateSpace_le`, `riemannHypothesis_iff_finrank_boundStateSpace_eq_one`)
- [ ] 3 → 4

## Obstacle addressed
The two-sided count of MUST-1557/1558 was stated for orthonormal eigenfamilies and under a
finiteness hypothesis on `P`. The missing step was that `P` is spanned by finitely many bound
states when the off-line set is finite; the usual route (orthogonal eigenspace decomposition) is
replaced by the reweighting identity `⟪Ru,u⟫ − a‖u‖² = ‖Σ cᵢ√(μᵢ−a)eᵢ‖²`, which needs only the
pairwise orthogonality of eigenvectors with distinct eigenvalues.

## Assessment (recorded with the user's remark of 2026-10-16)
The spectral layer is now a closed receiver: `RH ⟺ P = ℝ·1 ⟺ dim P = 1`, with `dim P` squeezed
between the Weil negative index (visible deep zeros) and the quarter-zero count. None of these
statements is sensitive to the primes beyond the bounded prime generator: they hold for any
bounded symmetric operator of the form `SS*` on a closed difference graph. Exclusion of bound
states requires arithmetic input through the prime edges; see the lane memory for the pivot.

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDBoundStateDimension.lean` — `inner_eigen_eq_zero_of_ne`, `inner_resolvent_sum_ge`,
`sourceEnergy_rieszLift_le_of_lower_bound`, `finrank_span_eigen_le`, `card_le_of_linearIndependent_eigen`,
`boundStateSpace_eq_span_of_finite`, `finiteDimensional_boundStateSpace`, `finrank_boundStateSpace_le`,
`oneL_ne_zero`, `riemannHypothesis_iff_finrank_boundStateSpace_eq_one`, `weilNegIndex_le_two_mul_quarter_add_one`,
`card_visible_le_two_mul_quarter_add_three`.
