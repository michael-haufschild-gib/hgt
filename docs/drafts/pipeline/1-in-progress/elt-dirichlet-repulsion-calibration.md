# Dirichlet exceptional-zero repulsion calibration

- **ID:** ELT-DH
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / FORMALIZATION TARGET
- **Target:** A complete Deuring–Heilbronn law for the actual infinite divisor of `ζ(s)L(s,χ)`, with χ primitive, real and nonprincipal. A real zero β₁ near 1 forces every other zero ρ near 1 to satisfy
  `1−Re ρ ≥ log(1/[C(1−β₁)log(q(|Im ρ|+3))])/[C log(q(|Im ρ|+3))]`
  for an absolute positive constant C.

## Mechanism to validate

Positive coefficients `(1+χ(n))(1+cos(t log n))Λ(n)` control all even
reciprocal moments of the complete divisor at `σ` and `σ+it`.
Removing β₁ from both copies pairs its moments with the pole at 1;
their difference is bounded by `4k(1−β₁)/(σ−1)^(2k+1)`.

An infinite power-sum lemma must detect a remaining zero with order
`k≤C M`, where M is the total normalized reciprocal-square mass.
Put `H=1+log q+log(|t|+3)`. For a target at `1−δ+it`, with
`0≤δ≤½`, choose `α=δ+1/(2H)` and `σ=1+α≤2`.
The target contributes a reciprocal square of modulus `(α+δ)⁻²`.
Since `δ≤α`, the normalized mass satisfies `M≤C(1+δH)`.
The detected moment and pole cancellation give
`1≤C(1−β₁)H exp(CδH)`. Finally
`H≤(1+1/log 3)log(q(|t|+3))`, giving the stated logarithmic law
after changing the absolute constant.
All nontrivial and trivial zeros, multiplicities, and Gamma terms must
be retained. No finite truncation may replace the divisor.

## Status and role

This is the classical calibration required by §2.10, not a claim of new
repulsion for ζ. Corpus search found Siegel's theorem and the two-torsion
positivity exception; no declaration named Deuring–Heilbronn was found.
The final logarithmic repulsion statement remains under formalization.
The infinite power-sum lemma, all-order Euler inequality, and completed
divisor identities are proved in Lean; no Dirichlet repulsion theorem is claimed.

Euler input: `ExceptionalLayerTheory/ThePositiveDirichletMomentKernel.lean`,
`exceptionalEuler_odd_jet_nonneg`. It proves
`Re[Dχ^(2k+1)(σ)+Dχ^(2k+1)(σ+it)]≥0` for actual
`Dχ=ζ′/ζ+L′/L`, every quadratic χ, σ>1, real t and k≥0.
Absolute convergence and the exact logarithmic weights are discharged.

The ζ analogue must explain how to replace real pole–zero cancellation
when the isolated layer is a nonreal conjugate pair.

## Infinite power-sum argument

Normalize a summable sequence by its attained maximal modulus. Write
`M=Σ|z_j|`, `|z_j|≤1`, and choose `|w|=1` among its terms.
For `P_N(z)=Σ_{j<N}Σ_{k<j}z^(k+1)`, the Fejér square identity gives
`Re P_N(z)≥−N/2`. For `|z|≤1/2`, geometric summation gives the
stronger summable majorant `Re P_N(z)≥−2N|z|`; together these give
that majorant on the whole unit disc.

The weighted polynomial
`U_N(z)=Re[P_N(z)+(P_N(zw)+P_N(z conj(w)))/2]`
has nonnegative moment weights `1+Re(w^k)≤2`, satisfies
`U_N(z)≥−4N|z|`, and at the selected term satisfies
`U_N(w)≥N(N−4)/4`. If every real power sum through order `N−1`
were at most `1/8`, summing would give `N−7≤32M`.
Choose `N=ceil(32M)+9`. Since `M≥1`, some `1≤k≤64M` has
`Re Σ z_j^k>1/8`. Absolute summability justifies every exchange;
no gap below the maximal modulus or finite-support premise is needed.

Lean: `ExceptionalLayerTheory/InfinitePowerSumsDetectAMaximalTerm.lean`,
`infinite_real_power_sum_detects_maximal_term`. The maximal modulus is
proved to be attained. This is a component of the calibration.

## Full-divisor inputs

Normalize the completed Dirichlet function by `q^(s/2)`. Its reflection
equation cancels the unknown affine Hadamard factor, giving the paired
logarithmic-derivative sum without assuming a nonzero central value.
For `σ=1+α`, every completed zero lies in `0≤Re ρ≤1`, so
`α Σ|σ+it−ρ|⁻² ≤ 2 Re E′/E(σ+it)`.
The Euler series bounds `|L′/L(σ+it)|` by `−ζ′/ζ(σ)`; the Gamma
factor contributes `O(log(q(|t|+3)))`. Thus the required nontrivial-zero
mass is `O(α⁻²+log(q(|t|+3))/α)`.

The higher completed identity retains the entire trivial-zero series.
For each real trivial zero b≤0 and every k≥1,
`Re[(σ−b)^(-2k)+(σ+it−b)^(-2k)]≥0`, since the second term's
modulus is at most the first term. Consequently the full trivial-zero
contribution has the sign needed to bound the nontrivial moments from
above. This avoids transporting the uncompleted divisor through Gamma
poles; it does not discard an uncontrolled remainder.

Corpus inputs: `CompletionZeroPairs.hasSum_logDeriv_zeroPairs`,
`CompletionZeroPairs.exists_reflect_zeroCopy`,
`completedLFunction_orderOneEnvelope`, and
`SelbergClass.DegreeOne.orderOneEnvelope_LFunction`.
Lean: `ExceptionalLayerTheory/TheCompletedDirichletDivisor.lean` proves
`exceptionalCompletion_logarithmic_moments` and
`exceptionalCompletion_mass_le_logDeriv` for the actual completed product
`ξ(s)q^(s/2)Λχ(s)`. Central zeros and multiplicities are retained.
`TheDirichletPoleControlsTheInfiniteDivisor.lean` proves the Gamma-sign
comparison, logarithmic conductor mass bound, and removal of exactly one
exceptional copy. Its `pairedExceptionalResolvent_mass_le` and
`pairedExceptionalResolvent_moment_le` are the two arithmetic inputs to
the power-sum detector. The final logarithmic repulsion law remains pending.
