# Exact coefficient of the positive model's averaged deficit

- **ID:** SPL-positive-model-exact-average
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For the positive odd-prime model with extra norms three and
  four, `(x²/2−R(x))/(x log x) → 1/(4 log 3)`, where `R(x)=∫₀ˣN(t)dt`.

## Paper proof

Let `F(x)` count positive integers whose two-adic valuation is even,
`R₄(x)=∫₀ˣF(t)dt`, and `H(x)=x²/3−R₄(x)`. Write
`r(x)=dist(x/2,ℤ)²`. The first `J=⌊(x+1)/2⌋` positive odd integers
have weighted count `Jx−J²`; its deficit from `x²/4` is `r(x)≤1/4`.
Summing over powers of four gives `H(x)≥0` and

`H(4x)=4H(x)+r(4x)`.

For `x>0`, define

`P(x)=H(x)/x + Σ_{j≥1} r(4^j x)/(4^j x)`.

The series converges uniformly on every compact positive interval. Both
`r` and `H` are continuous, the latter because its weighted count is locally
a finite sum of positive parts. Thus `P` is continuous, `P(4x)=P(x)`, and

`0≤xP(x)−H(x)≤1/12`.

The exact parity partition `F(x)+F(x/2)=⌊x⌋` implies

`H(x)+2H(x/2)=x/2−{x}(1−{x})/2`.

Replace `x` by `4^j x`, divide by `4^j x`, and let `j→∞`. This gives
`P(x)+P(x/2)=1/2`. In particular `0≤P≤1/2`. Consequently
`h(u)=P(4^u)` is continuous, has period one, and satisfies
`h(u)+h(u−1/2)=1/2`.

Set `α=log 3/log 4`. It is irrational: a rational relation would equate
positive powers of three and four, contradicting unique factorization.
For each `ε>0`, density of integer multiples of `α` modulo one and uniform
continuity of `h` give a fixed integer `k` such that, uniformly in `u`,

`|h(u)+h(u−kα)−1/2|≤ε`.

Let `S_n(u)=Σ_{a<n}h(u−aα)`. Shifting this sum by `k` changes only its
boundary terms, so `|S_n(u−kα)−S_n(u)|≤|k|`. Summation gives

`|S_n(u)/n−1/4|≤ε/2+|k|/(2n)`.

Thus these averages converge uniformly in the starting point to `1/4`.

For `x≥1`, put `A=⌊log x/log 3⌋`. The actual coordinate bijection yields
`R(x)=Σ_{a≤A}3^a R₄(x/3^a)`. Hence

`(x²/2−R(x))/x = Σ_{a≤A}h(log₄x−aα)+E(x)`.

The omitted quadratic main terms contribute `x/(2·3^(A+1))≤1/2`.
The accumulated replacement error has magnitude at most
`Σ_{a≤A}3^a/(12x)≤1/8`. Therefore `|E(x)|≤5/8`.
Uniform convergence of the averages and `(A+1)/log x→1/log 3` prove
the stated limit.

## Lean declarations and boundary

Namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount`:

- `PositiveNearCountProfile.lean`: `fourProfile_approx`, `fourProfile_four`,
  `fourProfile_half`, `continuousAt_fourProfile`.
- `PositiveNearCountProfileBridge.lean`: `sum_normBall_eq_rectangle`,
  `rieszCount_eq_three_sum`, `normalized_deficit_profile_error`.
- `PositiveNearCountExactAverage.lean`: `uniform_profile_average`,
  `riesz_deficit_converges`, `tendsto_riesz_deficit`,
  `tendsto_integral_count_deficit`.

`ComplementaryRotationAverages.lean` supplies the general uniform averaging
principle. All mathematical inputs are discharged for the concrete model.
Direct source checks pass; capstone axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.

No pointwise `O(log x)` count bound or exceptional-zero conclusion follows.
No external novelty claim.
