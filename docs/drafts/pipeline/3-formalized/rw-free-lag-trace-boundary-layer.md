# Free-lag trace certificate: source boundary layer

- **ID:** RW-FREE-LAG-TRACE-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
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

The coarse paper theorem is proved above and formalized in Lean (see the Lean certificate); the novelty audit remains pending. Deep search `free lag boundary layer trace certificate large aperture` returned partial coverage and no matching inspected candidate; exhaustive source searches found the prime-2 certificate and generic finite-prime symbol APIs. Any failed cofinal-certificate route must retain its strongest source boundary-layer survivor before retirement.

## Coarse route avoiding the sharp PNT moment limit

The inspected corpus theorem `PoleFreePrimeTranslationResonance.exists_primeHinge_ge` already proves `M1(a)≥exp(a)/4` at all large apertures. With `C=log 4+4`, the paper Chebyshev bound gives `M0(a)≤2C exp(a)` and finite-sum layer-cake integration gives `M2(a)≤16C exp(a)`. Then Taylor's exact remainder gives

`S_a(t/(4πa)) = W(t/(4πa)) - (t/a) sin(t) M1(a) + error`,

`|error|≤t² M2(a)/(4a²)`.

On a fixed finite union of intervals where `t sin t>0`, the negative leading term has size at least a fixed positive multiple of `exp(a)/a`, while the remainder is smaller by a factor `1/a`. This suffices for a uniform negative trace certificate; the sharp locally uniform `-4t sin t` limit can remain a separate positive survivor. Every moment estimate and source identity is now formalized (see the Lean certificate).

Exact source APIs now inspected: `ccmRestrictedWeilSourceQuadraticWith_eq_integral_symbol` identifies every finite-prime multiplier; `ccmRestrictedWeilSourceQuadraticWith_eq` recovers the actual form with `lam=Λ` and the native cutoff. `inner_logTranslationCLM_two_aperture_eq_zero` and `re_inner_logTranslation_eq_integral_cos` give the free-lag null integral. Thus the candidate all-prime representation requires no new spectral or positivity premise.

The inspected optimal-residual formulas have the exact cancellation

`C(a,ω)²+S(a,ω)² = 16(cos(aω)² sinh(a/2)² + sin(aω)² cosh(a/2)²)/(1+4ω²)`.

Consequently the two-pole projection loss is uniformly bounded at all large apertures: `sinh(a)-a≥exp(a)/4` eventually because `a exp(-a)→0`; `a+sinh(a)` is larger. The numerator sum is at most `16 cosh(a/2)²≤16 exp(a)` for `a≥0`. This gives `residual≥2a-64` uniformly in frequency and makes the four-interval observation mass eventually greater than one. The archimedean symbol is uniformly bounded on these shrinking bands by its already proved monotonicity in absolute frequency. Together with the proved-on-paper Chebyshev age-moment bound these estimates close the coarse paper mechanism; no sign of the full Weil form follows.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.FreeLagTraceCertificateObstruction`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module (clean under `lake env lean`, built as a module, axiom audit `[propext, Classical.choice, Quot.sound]` only):
new `GaloisForLFunctions.RHTower.FreeLagTraceCertificateObstruction` (namespace `RHTower.FreeLagTrace`), on top of
the corpus modules `RHTower.PoleVanishingWeilTraceCertificate` (plane-wave pairing, closed residual integral),
`RHTower.PoleVanishingWeilPrimeTwoEntry` (translation pairing, prime-two symbol), `RHTower.SelbergTruncatedVonMangoldtKreinCompletion`
(finite-atom symbol representation), `RHTower.PoleFreePrimeTranslationResonance` (`primeHinge = M₁ ≥ e^a/4`),
`RHTower.HardyZPhaseAsymptotic` (divergence of the Gamma phase rate). No RH hypothesis anywhere.

| Claim | Lean declaration |
|-|-|
| Free-lag all-prime symbol `S_a`; `= ` finite-atom symbol + null full-lag correction | `freeLagSymbol`, `freeLagSymbol_eq_weilAtomSymbol` |
| Prime-2 symbol coefficient is twice `Λ(2)/√2` | `freeLagSymbol_eq_primeTwoShiftSymbol` (corpus `primeTwoShiftSymbol`) |
| Actual form = `∫ S_a |û|²` on the pole-vanishing subspace (free-lag null integral) | `ccmRestrictedWeilSourceQuadratic_eq_integral_freeLagSymbol` |
| `C = log 4 + 4`, `ψ(X) ≤ CX` | `chebyshevConst`, mathlib `Chebyshev.psi_le_const_mul_self` |
| Abel summation `Σ Λ(n)/√n = ψ(X)/√X + ½∫ψ(u)u^{-3/2}du`, bound `≤ 2C√X` | `sum_vonMangoldt_div_sqrt_eq`, `sum_vonMangoldt_div_sqrt_le` |
| `M₀(a) ≤ 2C e^a` | `primeMass`, `primeMass_le` |
| Layer cake `M₂(a) = 2∫₀^{2a}(2a−s)M₀(s/2)ds`, `M₂ ≤ 16C(e^a−1−a)` | `primeSecondMoment`, `primeSecondMoment_eq_layerCake`, `primeSecondMoment_le` |
| `M₁(a) ≥ e^a/4` at large aperture | corpus `exists_primeHinge_ge` |
| Taylor remainder `cos(t−h) − cos t ≥ h sin t − h²/2`; `S_a ≤ W − (t sin t/a)M₁ + t²M₂/(4a²)` | `cos_sub_sub_cos_ge`, `freeLagSymbol_le_taylor` |
| Four bands, `t sin t ≥ π/12`, `|t| ≤ 17π/6`; `W ≤ W(1)` on shrinking bands; `S_a ≤ −κ e^a/a` on bands (`κ = π/96`) | `IsNegativeBand`, `isNegativeBand_mul_sin`, `exists_freeLagSymbol_le_on_band` |
| Optimal two-pole residual, minimum of the closed residual | `optimalResidual`, `optimalResidual_eq_closedForm`, `optimalResidual_le_closedForm`, `optimalResidual_nonneg` |
| Exact cancellation `C²+S² = 16(cos²sinh²(a/2)+sin²cosh²(a/2))/(1+4ω²) ≤ 16e^a` | `poleCosCosh_sq_add_poleSinSinh_sq`, `poleCosCosh_sq_add_poleSinSinh_sq_le` |
| `sinh a − a ≥ e^a/4`, `R_a ≥ 2a − 64` uniformly | `optimalResidual_ge` |
| Fourier density bound `|f̂(ξ)|² ≤ R_a ‖f‖²` | `norm_fourier_sq_le_optimalResidual` |
| Trace defect and certificate; integrability (`W → ∞`); validity `Q(u) ≥ (α − ∫(α−S_a)₊R_a)‖f‖²` | `traceDefect`, `traceCertificate`, `exists_archimedeanWeilSymbol_ge`, `integrable_traceDefect`, `traceCertificate_mul_le` |
| Band mass `≥ 4/3 − 128/(3a) ≥ 7/6`, `α − defect ≤ −α/6 − (7κ/6)e^a/a ≤ −κe^a/a` | `sub_integral_le_of_band` |
| **Main theorem**: certificate `≤ −κ e^a/a` for all large `a`, all `α > 0`; strictly negative | `exists_traceCertificate_le`, `traceCertificate_neg_eventually` |
| Residual bound is attained (projected plane wave); every valid density bound `≥ R_a` | `planeWaveApertureVector`, `inner_ccmPolarL2Vector_planeWaveL2_eq`, `optimalResidualVector`, `inner_optimalResidualVector_eq_zero`, `fourier_optimalResidualVector`, `norm_optimalResidualVector_sq`, `optimalResidual_le_of_density_bound` |
| Every valid scalar (finite shell) certificate obeys the same obstruction | `exists_certificate_le` |

The sharp locally uniform limit `a e^{−a} S_a(t/(4πa)) → −4t sin t` and the PNT moment limits `2, 4, 16` are recorded on
the card as conjectures and are not claimed.

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.

## Sharp boundary layer (2026-10-07, loop row 545) — formerly the open conjecture
Both sharp statements left open above are now theorems in Lean: module `RHTower/FreeLagSymbolBoundaryLayer` (namespace `RHTower.FreeLagTrace`), wired after `FreeLagTraceCertificateObstruction`. Axioms `[propext, Classical.choice, Quot.sound]`; zero messages.

| Claim | Declaration |
|-|-|
| `Σ_{n ≤ x} Λ(n)/√n ~ 2√x` (Abel summation + PNT) | `tendsto_sum_vonMangoldt_div_sqrt` |
| `M₀(b) ~ 2e^b` | `tendsto_primeMass_div_exp` |
| layer cake `M₁(a) = ∫₀^{2a} M₀(s/2) ds` | `primeHinge_eq_layerCake` |
| `M₁(a) ~ 4e^a` | `tendsto_primeHinge_div_exp` |
| `\|cos(t−h) − cos t − h sin t\| ≤ (3/2)h²` | `abs_cos_sub_sub_cos_sub_mul_sin_le` |
| `S_a(t/4πa) = W − (t/a) sin t·M₁ + E`, `\|E\| ≤ (3t²/4a²)M₂` | `abs_freeLagSymbol_scaled_sub_le` |
| **`a e^{−a} S_a(t/(4πa)) → −4t sin t`, uniformly on `[−T, T]`** | `tendstoUniformlyOn_scaled_freeLagSymbol` |
| **`R_a(ω)/(2a) → 1`, uniformly in `ω`** | `tendstoUniformly_optimalResidual_div` |

Proof. The constant `4` is `∫₀¹ s^{−½}(½ log(1/s) + 1) ds`, obtained through the layer cake. The PNT enters only through `ψ(x)/x → 1`, used as `|ψ(t) − t| ≤ εt + B_ε`. The residual limit follows from `2a − 64 ≤ R_a ≤ 2a`.

Reading. At aperture `a`, the restricted Weil symbol on the scale `1/a` has the exact profile `−(e^a/a)·4t sin t`, and pole-vanishing plane waves keep their full mass `2a` there. The coarse obstruction is therefore sharp: the four negative bands carry exactly `(4/3)` of residual mass at depth `≍ e^a/a`. Mathematically this is PNT plus Taylor. It is a closure of a stated open item, not new arithmetic.
