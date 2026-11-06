# Theta endpoint energy on a Vinogradov–Korobov band

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ76
- **Statement:** For the literal Wold residual and weights `(n+1)^(2t)`, one constant bounds endpoint energy whenever `0 ≤ t ≤ 1/2` and `t ≤ vkKappa*vkScale(N+2)/(96*log(N+2))`.

## Mathematical route

Abel summation transfers the actual Vinogradov–Korobov Chebyshev error to the centered prime harmonic residual. Euler-depletion tails are smaller. The monotonicity of `vkScale(x)/log x` transfers the cutoff restriction to every earlier index. Squaring leaves a summable logarithmic tail after paying the power weights. Concavity of `x^(2t)` controls their increments.

This supplies a shrinking positive-exponent band, not boundedness at a fixed positive exponent. The existing square-root-log residual estimate gives a narrower band.

## Paper proof

Write `Q=vkScale`, `κ=vkKappa`, and `R` for the literal centered Wold residual. The actual PNT gives `abs(ψ(x)-x) ≤ B x exp(-κQ(x)/24)`. Proper prime powers cost at most `2√x log x`; `κQ(x) ≤ log x` eventually absorbs this cost with constant 8.

Abel summation gives the centered prime harmonic discrepancy as `(θ(x)-x)/x - ∫_x^∞(θ(u)-u)/u² du`. For large `u ≥ x`, monotonicity of `Q` and `κQ(u) ≥ 2√log u` give
`exp(-κQ(u)/24) ≤ exp(-κQ(x)/48) exp(-√log u/24)`.
The latter logarithmic density has tail integral at most 2304. Thus the harmonic residual is at most `2305B exp(-κQ(x)/48)`. Its center equals the canonical Mertens constant by uniqueness of limits. The Euler-depletion tail is at most `3(log N+1)/N ≤ 15 exp(-κQ(N)/48)`. Consequently `abs(R(N)) ≤ B₁ exp(-κQ(N)/48)` eventually.

Set `T=N+2`. Since `Q(x)/log x` decreases eventually, the stated band implies `2t log m ≤ κQ(m)/48` for every sufficiently large `m ≤ T`. Hence
`m^(2t)R(m)² ≤ B₁² exp(-κQ(m)/48) ≤ B₁² exp(-√log m/24)`.
Finitely many earlier indices are absorbed uniformly using `m^(2t) ≤ m`. Thus one constant `C` bounds this weighted square by `C exp(-√log m/24)` for every `1 ≤ m ≤ T`.

Concavity gives `w(n+1)-w(n) ≤ 2t(n+1)^(2t-1) ≤ 2(n+2)^(2t)/(n+2)`. The weighted residual sum is bounded by `2C Σ_(m≥2) exp(-√log m/24)/m`, a convergent series. The boundary square is at most `C`. The existing endpoint-variance estimate now bounds every admitted endpoint energy by `2R(1)²+2C+4C Σ_(m≥2) exp(-√log m/24)/m`. At `t=0` the sum vanishes and the same bound follows directly.

All four declarations are kernel-checked and depend only on `propext`, `Classical.choice`, and `Quot.sound`:

- `ArithmeticCompensationTheory/WoldResidualVinogradovKorobov.lean`: `exists_abs_theta_sub_self_vk_rate`, `exists_abs_canonical_mertensA_vk_rate`, `exists_abs_woldResidual_vk_rate`.
- `ArithmeticContinuationAndCriticalEnergy/ThetaEndpointVinogradovKorobov.lean`: `exists_thetaEndpointEnergy_le_on_vinogradovKorobovBand`.

Final audits passed from `formal/`, without writing oleans:

```sh
lake --old env lean GaloisForLFunctions/ArithmeticCompensationTheory/WoldResidualVinogradovKorobov.lean
lake --old env lean GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/ThetaEndpointVinogradovKorobov.lean
```
