# Central reciprocal moments of the actual xi divisor

- **ID:** central-reciprocal-moments
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean
- **Source:** actual xi divisor, inverse-square convergence exponent, functional equation, and Schwarz reflection
- **Statement:** The multiplicity-bearing centered coordinates `lambda_rho = -((rho - 1/2)⁻¹)^2` are summable; the coordinates remain summable after multiplicities are forgotten, tend to zero off finite sets, and every positive-order divisor moment is real.

## Goal

Supply the previously missing target-free analytic interface for a positivity attack on RH: an actual trace-class spectrum attached to every xi zero, with exact conjugation symmetry and all positive moments defined without truncation or an RH assumption.

## Gates

- [x] 0 → 1 in-progress: the actual divisor and centered coordinate are fixed, with no abstract carrier hypothesis
- [x] 1 → 2 fully-proven: comparison with the proved inverse-square xi-divisor sum and divisor symmetries closes every claim
- [x] 2 → 3 formalized: `CentralReciprocalMoments.lean` builds and uses only standard axioms
- [ ] 3 → 4 publication-ready: integrate with a proved unconditional positivity provider and the resulting RH theorem

## Lean certificate

- `xi_zero_multiplicity_centered_inv_sq_summable`
- `xi_central_reciprocal_square_summable`
- `xi_central_reciprocal_square_unweighted_summable`
- `xi_central_reciprocal_square_tendsto_cofinite_zero`
- `xi_central_reciprocal_moment_summable`
- `xiCentralReciprocalMoment_conj`
- `xiCentralReciprocalMoment_im_eq_zero`
- `mem_xi_divisor_support_of_eq_zero`
- `xi_divisor_support_re_mem_open_unit`
- `xi_divisor_support_im_ne_zero`
- `xiCentralReciprocalSquare_im_eq_zero_iff`
- `xi_divisor_support_re_eq_half_of_rh`
- `xiCentralReciprocalSquare_pos_real_of_rh`

The proofs are in `formal/GaloisForLFunctions/RHTower/CentralReciprocalMoments.lean`.

## Remaining open core

`[OPEN CORE]` Prove, from the prime-archimedean or theta source itself, a positivity statement strong enough to force every trace-class coordinate `lambda_rho` to be a nonnegative real. This card does not call a conditional characterization unconditional.

## Log

- 2026-07-10 — formalized the centered trace-class spectrum and all-order real moments for the actual xi divisor.
