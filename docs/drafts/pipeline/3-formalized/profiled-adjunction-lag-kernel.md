# The adjunction lag charge on translated source profiles

- **ID:** SSH-PROFILED-ADJUNCTION-LAG
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q1/O1, retaining the source profile on the logarithmic mesh.

## Statement

Let `G(v)=∫φ(u)φ(u+v)du`, with continuous compactly supported real `φ`.
For every finite signed sequence `x`, arbitrary real shifts `θ_i`, and `m≥1`,

`Σ_(i,j) x_i x_j G(θ_j−θ_i)c_m(|i−j|)`
`  ·[tameDifferent(m)−λ_(m/gcd(m,|i−j|))] ≥ 0`,

where `λ_d=log d+tameDifferent(d)`.
In particular the same assertion holds at `θ_i=log(i)/w` for every `w>0`.

The profile conductor weight is
`b_k=φ(k)⁻¹Σ_(i,j)x_i x_j G(θ_j−θ_i)c_k(|i−j|)`.
It equals the integral of the finite-source autocorrelation weight
of `a_i(u)=x_iφ(u+θ_i)`, hence be nonnegative. These actual profile weights
then give the exact positive weighted divisor-jet completion. The displayed
adjunction Gram is exactly `Σ_(k|m)Λ(m/k)φ(k)b_k`, its incoming charge.

## Proof

Integrate the finite-source identity pointwise in `u`; compact support
justifies every finite sum interchange. Translation invariance gives
`∫φ(u+θ_i)φ(u+θ_j)du=G(θ_j−θ_i)`.
The identity
`Σ_(k|m)Λ(m/k)c_k(h)=c_m(h)[tameDifferent(m)−λ_(m/gcd(m,h))]`
follows from the conductor expansion and exact adjunction formula for the
divisor jet. Finite sum interchange identifies the incoming profile charge.
Every summand `Λ(m/k)φ(k)b_k` is nonnegative. The weighted divisor energy is
therefore again a sum of nonnegative edge squares.

## Lean status

`SuccessorShellArithmetic/Conductor/ProfiledAdjunctionLagKernel.lean` proves:

- `ramanujanProfileWeight_eq_integral` and `ramanujanProfileWeight_nonneg`;
- `sum_divisor_profileWeight_eq_adjunction_charge`;
- `profiled_adjunction_lag_charge_nonneg` and its exact logarithmic-mesh specialization;
- `weightedDivisorJetEnergy_profile_nonneg`.

The exact energy identity is `weightedDivisorJetEnergy_eq_period_pairing`
from `SmoothedDivisorJet`, instantiated at these profile weights.
Direct leaf audit passed. All six capstone axiom checks contain only
`propext`, `Classical.choice`, and `Quot.sound`; umbrella import is wired.

## Boundary

Arbitrary source shifts are retained exactly. Identification of this
positive kernel inside the complete Weil matrix, including its prime
ratio couplings and horizon boundary, remains open.
