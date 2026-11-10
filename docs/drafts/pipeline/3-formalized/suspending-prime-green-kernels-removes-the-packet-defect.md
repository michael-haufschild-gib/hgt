# Suspending prime Green kernels removes the packet defect

- **ID:** suspending-prime-green-kernels-removes-the-packet-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B133; the actual prime-fibre Green kernels and the archimedean Green damping.
- **Statement:** Translation averages of actual prime Green ladders give positive
  continuum channels. One arithmetic mass clock couples them to the hyperbolic
  Green damping with limit equal to Weil's form on every real compact C² packet,
  including overlaps, without a discriminant defect.

## Gates

- [x] 0 → 1: explicit kernels and a packet-independent clock.
- [x] 1 → 2: dependency-closed derivation below `[PROVED HERE]`.
- [x] 2 → 3: five modules pass plain `lake --old env lean`; audited declarations
  depend only on `[propext, Classical.choice, Quot.sound]`.

## Proof `[PROVED HERE]`

Write `q=p^(−1/2)`, `L=log p`, `M(f)=∫f²`, and `h=autocorr(f)`.
The actual normalized prime-fibre Green matrix on `1,p,…,p^(N−1)` has entries
`log p·q^|i−j|`. For `N≥1`, average its quadratic form against `f(u+iL)` over
`u`, dividing by `N`. Its complement in
`log p·(1+q)/(1−q)·M(f)` is nonnegative by the KMS upper bound. Translation
invariance of Lebesgue measure and counting pairs at each lag give exactly

`T_(p,N)(f)=c_p M(f)−2 log p Σ_(1≤k<N)(1−k/N)q^k h(kL)`,

where `c_p=2 log p/(√p−1)`. The diagonal is the actual continuum mass;
no packet-profile orthogonalization enters.

Compact support leaves finitely many nonzero correlations. Define

`P_p(f)=2 log p Σ_(k≥1)q^k h(kL)`,
`J_p(f)=2 log p Σ_(k≥1)k q^k h(kL)`,
`T_p(f)=c_p M(f)−P_p(f)`.

For all sufficiently large `N`, `T_(p,N)=T_p+J_p/N`. Therefore
`T_(p,N)→T_p`, and `T_p≥0` for every real continuous compact packet.

Let `C_n=Σ_(p<n)c_p`, summing over primes. Since `c_p≥2log(2)/p`, Euler's
prime reciprocal divergence gives `C_n→∞`. For `S≥0`, set

`a_p(S)=[min(S,C_(p+1))−min(S,C_p)]/c_p`.

These weights lie in `[0,1]`, have finite support, and telescope to
`Σ_p a_p(S)c_p=S`. Moreover, `a_p(S)=1` once `S≥C_(p+1)`.
Thus `T_S(f)=Σ_p a_p(S)T_p(f)` is a positive quadratic form, with the same
weights for every packet.

Choose `B` such that `h(log n)=0` for all integers `n>B`. Regrouping the
von Mangoldt sum by prime powers gives `primeSum(f)=Σ_(p≤B)P_p(f)`, and
`P_p(f)=0` for primes `p>B`. Consequently, for every `S≥C_(B+1)`,

`T_S(f)−S M(f)=−primeSum(f)`.

This identity is exact. The established geometric constant bridge supplies

`c₀=−4 regularMean−log(4π)−γ=2γ₀`.

Set `S(r)=selfEnergy(r)+c₀`. This clock tends to infinity as `r→1⁻`.
The archimedean finite-part theorem gives
`smoothGreenEnergy(r,f)−selfEnergy(r)M(f)→−levyEnergy(f)`. Hence

`pole(f)−smoothGreenEnergy(r,f)+T_(S(r))(f)`
`→ pole(f)+c₀M(f)+levyEnergy(f)−primeSum(f)=weilQuad(f)`.

The kernels and the arithmetic clock are defined before comparison with
Weil's form. No separation condition on the packet is used.

## Lean declarations

All modules lie in `formal/GaloisForLFunctions/HyperbolicArakelovTheory/`,
namespace `GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension`.

- `TheSuspensionOfThePrimeGreenKernel.lean`:
  `prime_ladder_entry`, `integral_ladder`, `positiveChannel_eq`, `positiveChannel_nonneg`.
- `TheContinuumPrimeGreenChannel.lean`:
  `positiveChannel_eventually_eq`, `tendsto_positiveChannel`, `continuumChannel_nonneg`.
- `TheArithmeticMassClockOfThePrimeGreenKernel.lean`:
  `tendsto_cumulativeCapacity_atTop`, `clockWeight_finite_support`, `clockWeight_total`.
- `TheContinuumGreenChannelsRecoverThePrimeSum.lean`:
  `primeSum_eq_finite_channels`.
- `TheArithmeticClockLocksTheContinuumGreenChannels.lean`:
  `clockedPrimeChannel_nonneg`, `eventually_clockedPrimeChannel_sub_mass`,
  `tendsto_coupledGreenEnergy`.

## Boundary and new insight

Translation averaging replaces the atomic diagonal by continuum mass before
global coupling. Arithmetic capacity filling then removes the packet defect
for a single family of positive prime channels. The existing prime Markov
and arithmetic ladder decompositions are inputs, not new results.

The construction uses the real translation representation and global
arithmetic ordering. It supplies no separately descended or torus-periodized
Green kernel on the refuted adelic quotient. Positivity of the full coupled
difference, and therefore RH, remains unproved.
