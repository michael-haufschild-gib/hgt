# PW-B sequential endpoint tomography

- **ID:** PW-B-SEQ
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · PW-B conditional-convergence survivor
- **Statement:** Natural-order convergence of every physical PW endpoint antidiagonal energy to zero forces every coefficient to vanish; symmetry plus pairwise positivity forces the matrix to vanish.

## Route edge discharged

Kills conditionally convergent, non-absolutely-admissible positive matrices in
`endpoint darkness -> response uniqueness -> PW-B balance -> Borel partner balance -> shared Ward endpoint -> RH`.

## Proof

At the largest node, convergence bounds anchored coefficients. The exact node semigroup turns all
smaller-node zero limits into zeros of one bounded power series accumulating at zero. Coefficient
uniqueness kills each antidiagonal; symmetry and pairwise positivity then kill every row. Hypotheses
use natural ordered partial sums, never `tsum` or absolute summability.

## Gates

- [x] 0 -> 1: corpus edge reconstructed; source-pure; no corpus duplicate
- [x] 1 -> 2: paper proof closed
- [x] 2 -> 3: Lean proof; direct check; targeted module build; axiom audit; umbrella wired
- [ ] 3 -> 4: publication-ready

## Lean certificate

`ThetaCuspHawkingParikhWilczekSequentialMatrixEndpointTomography.lean`:
`pwMatrixEndpointAntidiagonalCoefficient_eq_zero_of_sequentiallyDark`,
`symmetric_pairwisePositive_kernel_eq_zero_of_sequentiallyDark`, and
`schwarzschildParikhWilczekSequentiallyAdmissiblePairwisePositiveEndpointDarkRouteKilled`.

Direct Lean and targeted module build pass. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
Repo-global lint currently fails only on unrelated existing unwired modules; no reported error names
this module.
