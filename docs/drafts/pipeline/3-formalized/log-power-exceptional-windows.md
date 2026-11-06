# Logarithmic-power exceptions and eventual geometric-ray corridors

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Π6
- **Statement:** For `b>1` and `0<η<b−1`, bad unit-window heights in `[U,2U]` have measure `O(U/(log U)^η)`. For `b>2`, almost every `x∈[1,2]` eventually has no zero of depth at least `b log log T/log T` in the unit windows at `T=e^n x`.

## Proof [PROVED HERE]

Fix `b>1` and `0<η<b−1`, and put `c=(1+η)/(2b)∈(0,1/2)`.
The unconditional theorem `exists_dyadicMean_corridor_and_polynomialTheta_le_log_up_to_half`
gives `∫_[U,2U] Q(T,c log T) dT ≤ K_c U log U` eventually, where `Q` is
the sum of nonnegative depth kernels with positive integer zero multiplicities.
For `T∈[U,2U]` and a zero of depth `d≥b log log T/log T`, its kernel is
`2cosh(2cd log T)−2 ≥ exp(2cd log T)−2 ≥ (log U)^(1+η)−2`.
Eventually this is at least `(log U)^(1+η)/2`. Markov's inequality therefore
bounds bad-window measure by `2K_c U/(log U)^η`. Integrability is supplied by
`integrableOn_unitWindowDepthCharge_log_Icc`; outer-measure monotonicity avoids
any extra measurability assumption on the bad-window set.

For `b>2`, choose `η∈(1,b−1)`. Let `E_n⊆[1,2]` consist of those `x` whose
window at `T=e^n x` is bad. Dilation of Lebesgue measure gives
`|E_n| ≤ 2K_c/n^η` for all sufficiently large `n`. Initial sets have measure
at most one, and the remaining series converges because `η>1`.
The first Borel–Cantelli lemma gives `|limsup E_n|=0`. Thus almost every
`x∈[1,2]` has the claimed strict corridor for every sufficiently large `n`.

## Frontier

Existing sharp-corridor theorems retain only `O(U/log log U)` exceptions.
The new summable estimate controls every sufficiently late sampled window
for almost every geometric ray. It supplies no all-height corridor.

## Lean

Module: `GaloisForLFunctions/ConjugateDiagonalGeometry/LogScaleHeckeDefect/LogPowerExceptionalWindows.lean`.
Namespace: `GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect`.

- `eventually_volume_badLogLogWindows_le_logPower`: every exponent `0<η<b−1`.
- `ae_eventually_geometric_unitWindow_corridor`: eventual strict corridor for almost every geometric ray, `b>2`.

Audit passed: `lake --old env lean GaloisForLFunctions/ConjugateDiagonalGeometry/LogScaleHeckeDefect/LogPowerExceptionalWindows.lean` from `formal/`.
Both declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Imported by the programme umbrella.
