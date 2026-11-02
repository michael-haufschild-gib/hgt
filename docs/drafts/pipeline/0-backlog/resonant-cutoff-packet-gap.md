# Hecke gap for arbitrary cutoff packets

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Parent:** [arithmetic measure rigidity](../1-in-progress/resonant-state-arithmetic-measure-rigidity.md).

## Statement

Fix a resonant parameter `u`, with `a=Re u<0`. For arbitrary finite complex
coefficients `c_j` and heights `Y_j≥2`, set
`F=Σ_j c_j Λ_aut^(Y_j) E_u` and `λ=2^u+2^(-u)`.
Conjecture:

`||(T₂−λ)F||² ≥ (2^a+2^(-a)−2)² ||F||²`.

This would exclude cancellation of the Hecke source by arbitrary finite
superpositions of high cutoffs, including approximations to smooth truncations.
It would not select a critical decay rate.

## Candidate mechanism

The exact finite-combination cusp isometry sends `Λ^Y E_u` to
`B(u)y^(-u-1/2) 1_(0,Y](y)`. Since `Y_j≥2`, both shifted cutoffs remain at least
one and the genuine automorphic Hecke action has no modular-return correction.
On the cusp model it becomes `D+D⁻¹`, where `Df(y)=√2 f(2y)` is unitary.
For `q=2^u`, the factorization

`D+D⁻¹−(q+q⁻¹) = −q⁻¹(D−q)(D⁻¹−q)`

suggests the bound `(1−|q|)²/|q|` by two reverse-triangle inequalities.
The required result concerns actual packets and their full residual norms;
a theorem only about an abstract unitary is insufficient.

## Existing ingredients and gap

- `ResonantStates.resonant_finite_combination_isometry` and `hecke_cutoff_shifts`.
- `ResonantStates.dyadicEigenResidualAt_eq_heckeRemainder` at cutoffs at least two.
- `RHTower.dilationUnitary`, `dilation_ae`, `dilation_dilation_inv` in `SoninL2Model`.
- `RHTower.norm_sub_smul_lower_bound` in `UnitaryResolventOffCircle`.

The cutoff powers still need an explicit `L²` realization and an audited
intertwining of the actual packet residual. No new analytic hypothesis is allowed.
