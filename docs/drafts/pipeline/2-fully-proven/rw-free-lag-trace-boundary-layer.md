# Free-lag trace certificate: source boundary layer

- **ID:** RW-FREE-LAG-TRACE-BOUNDARY
- **Stage:** 2-fully-proven
- **Type:** THEOREM (coarse paper obstruction); Lean and novelty audits pending
- **Statement:** At every sufficiently large aperture, the scalar constrained plane-wave trace certificate for the all-prime free-lag symbol is strictly negative for every positive reference level, with an upper bound tending to minus infinity like `-c exp(a)/a`. Its successful small-aperture mechanism cannot itself supply cofinal positivity. The sharper locally uniform boundary limit `a exp(-a) S_a(t/(4πa))→-4t sin t` remains a separate conjecture.

## Dependency-closed paper proof of the coarse obstruction

Use the actual finite-prime symbol with the free-lag correction, as checked from the inspected source APIs below. Put `C=log 4+4`. THIS mathlib's `Chebyshev.psi_le_const_mul_self` proves `psi(X)≤CX` for `X≥0`; the extra `+4` is retained.

Abel summation on `[1,X]`, where `psi(1)=0`, gives

`Σ_{2≤n≤X} Λ(n)/sqrt(n) = psi(X)/sqrt(X) + (1/2)∫_1^X psi(u)u^(-3/2)du ≤ 2C sqrt(X)`.

Thus `M0(a)≤2C exp(a)`. Finite-sum layer-cake integration, with no limit interchange, gives for `a≥0`

`M2(a)=2∫_0^(2a)(2a-s)M0(s/2)ds ≤ 4C∫_0^(2a)(2a-s)exp(s/2)ds = 16C(exp(a)-1-a) ≤ 16C exp(a)`.

The already proved source theorem supplies `M1(a)≥exp(a)/4` for all large `a`. Taylor's remainder bound below consequently gives, on any fixed compact set with `t sin t≥η>0`,

`S_a(t/(4πa)) ≤ W(1) - η exp(a)/(4a) + 4C T² exp(a)/a²`,

where `T` bounds `|t|` and the shrinking frequencies eventually lie in `[-1,1]`. Source monotonicity of `W` bounds its contribution by `W(1)`. The remainder and this fixed constant are eventually absorbed, yielding `S_a≤-κ exp(a)/a` with a fixed `κ>0`.

Take the two intervals `[π/6,5π/6]`, `[13π/6,17π/6]` and their reflections, denoted `U`. Their total length is `8π/3`, and `t sin t` is strictly positive with a positive minimum on this compact union. Their frequency image `U/(4πa)` has length `2/(3a)`.

The exact residual formulas below imply the uniform lower bound `R_a(ξ)≥2a-64` at all sufficiently large apertures. Its mass over those four bands is therefore at least `4/3-128/(3a)`, eventually at least `7/6`. For every `α>0`, the trace defect over these bands alone is at least

`(α+κ exp(a)/a)(7/6)`.

Hence even the upper bound obtained by retaining only these bands satisfies

`α-defect ≤ -α/6-(7κ/6)exp(a)/a ≤ -κ exp(a)/a`.

The full optimal scalar trace cost includes this nonnegative band defect, so it cannot certify positivity. Any valid finite shell certificate has pointwise density bounds no smaller than the exact projected-plane-wave residual, and symbol deficits no smaller than the negative-band deficit; the same obstruction applies. This is a failure of this specific scalar certificate, not a negative Weil witness. No RH assumption is used.

## Source-derived mechanism under investigation

The existing prime-2 symbol is `W(ξ)-sqrt(2)log(2)(cos(2π log(2) ξ)-cos(4πa ξ))`. Its coefficient is **twice** `Λ(2)/sqrt(2)`. Thus the candidate all-prime symbol is `W(ξ)-2 Σ_{2≤n≤exp(2a)} Λ(n)/sqrt(n)(cos(2π log(n) ξ)-cos(4πa ξ))`. The literal free-lag correction should preserve the supported form because the autocorrelation at lag `2a` vanishes. The exact all-prime identity must be verified before any conclusion is formalized.

Set `v=2a-log n` and `ω=t/(2a)`. The source prime moments predicted by the corpus PNT are

- `exp(-a) Σ Λ(n)/sqrt(n) → 2`;
- `exp(-a) Σ Λ(n)/sqrt(n) v → 4`;
- `exp(-a) Σ Λ(n)/sqrt(n) v² → 16`.

Taylor's formula gives `cos(t-ωv)-cos t = ωv sin t + O(ω²v²)`. Hence the normalized two-sided prime correction tends to `4t sin t`; the fixed-frequency archimedean symbol is negligible after multiplication by `a exp(-a)`. The factor two was checked against the actual prime-2 source definition before retaining this conjecture. This is an analytic asymptotic conjecture, not a numerical experiment.

The optimal two-pole residual should obey `dist²(e_ω,span e^{±x/2})/(2a)→1` uniformly on this frequency scale. Since `dξ=dt/(4πa)`, its weighted observation mass tends to `dt/(2π)`. Choose the intervals `[π/6,5π/6]`, `[13π/6,17π/6]` and both reflections. Their total t-length is `8π/3`, limiting residual mass `4/3>1`; `t sin t` has a strictly positive minimum on their union. The extended symbol should therefore be bounded above by a negative multiple of `exp(a)/a` there.

For any `α>0`, the certificate `α-∫(α-S_a)_+ residual_a` is then negative: on these intervals it is at most `α(1-mass)-c exp(a)/a`. This would be a uniform obstruction to this specific scalar trace mechanism, not a negative Weil witness or a failure of RH.

## Required audits

1. Search the complete corpus for the exact free-lag extension and prime moment asymptotics; use true source definitions and Fourier normalization.
2. Close the local-uniform limit and optimal residual estimate on paper without computation.
3. Audit public novelty for the coupled trace obstruction, not for classical PNT or Taylor expansion.
4. Formalize the source identity and exact asymptotic survivor; retain no unproved cofinal sign premise.

The coarse paper theorem is proved above; native Lean verification and novelty audit remain pending. Deep search `free lag boundary layer trace certificate large aperture` returned partial coverage and no matching inspected candidate; exhaustive source searches found the prime-2 certificate and generic finite-prime symbol APIs. Any failed cofinal-certificate route must retain its strongest source boundary-layer survivor before retirement.

## Coarse route avoiding the sharp PNT moment limit

The inspected corpus theorem `PoleFreePrimeTranslationResonance.exists_primeHinge_ge` already proves `M1(a)≥exp(a)/4` at all large apertures. With `C=log 4+4`, the paper Chebyshev bound gives `M0(a)≤2C exp(a)` and finite-sum layer-cake integration gives `M2(a)≤16C exp(a)`. Then Taylor's exact remainder gives

`S_a(t/(4πa)) = W(t/(4πa)) - (t/a) sin(t) M1(a) + error`,

`|error|≤t² M2(a)/(4a²)`.

On a fixed finite union of intervals where `t sin t>0`, the negative leading term has size at least a fixed positive multiple of `exp(a)/a`, while the remainder is smaller by a factor `1/a`. This suffices for a uniform negative trace certificate; the sharp locally uniform `-4t sin t` limit can remain a separate positive survivor. Every moment estimate and source identity is still awaiting formal proof.

Exact source APIs now inspected: `ccmRestrictedWeilSourceQuadraticWith_eq_integral_symbol` identifies every finite-prime multiplier; `ccmRestrictedWeilSourceQuadraticWith_eq` recovers the actual form with `lam=Λ` and the native cutoff. `inner_logTranslationCLM_two_aperture_eq_zero` and `re_inner_logTranslation_eq_integral_cos` give the free-lag null integral. Thus the candidate all-prime representation requires no new spectral or positivity premise.

The inspected optimal-residual formulas have the exact cancellation

`C(a,ω)²+S(a,ω)² = 16(cos(aω)² sinh(a/2)² + sin(aω)² cosh(a/2)²)/(1+4ω²)`.

Consequently the two-pole projection loss is uniformly bounded at all large apertures: `sinh(a)-a≥exp(a)/4` eventually because `a exp(-a)→0`; `a+sinh(a)` is larger. The numerator sum is at most `16 cosh(a/2)²≤16 exp(a)` for `a≥0`. This gives `residual≥2a-64` uniformly in frequency and makes the four-interval observation mass eventually greater than one. The archimedean symbol is uniformly bounded on these shrinking bands by its already proved monotonicity in absolute frequency. Together with the proved-on-paper Chebyshev age-moment bound these estimates close the coarse paper mechanism; no sign of the full Weil form follows.
