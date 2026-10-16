# CHMD: conjugated-Laplacian transport of the integrated Chebyshev deficit and the Möbius-dilation injection

- **ID:** chmd-deficit-conjugated-transport-mobius
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/cmhd-plan.md (Phase 2, concrete next step) · STATUS MUST-1569
- **Statement:** With `D(s) = ∫_0^s (e^t − ψ(e^t)) dt`, `f_y(s) = e^{−s/2} K_y(s)` and
  `Δ(s) = Σ_{log n < s} Λ(n)/√n − 2e^{s/2}`:
  `∫_0^∞ ∂_sK_y(s) Δ(s) ds = K_y(0) + ∫_0^∞ D(s) f_y''(s) ds`, where `f_y'' = e^{−s/2}(∂_s − ½)² K_y`
  obeys `|f_y''(s)| ≤ C e^{−s/2}` with `C` independent of `y`. Substituting the Möbius-dilation
  reconstruction `D = Explicit + ℓ·M(e^s) + Head + Tail`, the head pairs to at most `C·∫_0^∞ (s+14)/4·e^{−s/2}`
  for every `y`; hence `RH ⟺ ∫_0^∞ (Explicit + ℓ·M + Tail)(s) f_y''(s) ds` bounded above on `[0,∞)`
  `⟺` bounded below.

## Goal
Phase 2 of the plan diagnosed that the derivative pairing `∫ ∂_sK_y Δ` is arithmetic-blind beyond
Chebyshev's bound and must be rewritten through `Λ * 1 = log`. The corpus holds the Möbius-dilation
reconstruction of the integrated deficit `D`, with a uniformly bounded centered source, a small-divisor
head of size `O(s)` and a large-divisor tail. The missing bridge was the exact passage from the
`√`-weighted discrepancy `Δ` to the unweighted integrated deficit `D`. It is the conjugation
`K_y ↦ e^{−s/2}K_y` followed by two derivatives: the `√` weight becomes the conjugation and the two
Abel summations become the two derivatives. Nothing uses zeros or positivity premises.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof (below), no open dependency
- [x] 2 → 3  formalized: `RHTower/CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection`,
  `lake env lean` clean, `lake build --old` olean, standard axioms only, wired into `RHTower.lean`
- [ ] 3 → 4  publication-ready (not pursued; RH-only policy)

## Approach
1. **Termwise structure of `D`.** For `s ≥ 0`, `D(s) = e^s − 1 − Σ_n Λ(n)(s − log n)_+` (finite sum).
2. **Tent integration by parts.** For `ℓ ≥ 0`, with `g = (s − ℓ)f_y' − f_y`, `g' = (s − ℓ) f_y''`,
   `g(ℓ) = −f_y(ℓ)`, `g(∞) = 0`: `∫_ℓ^∞ (s − ℓ) f_y''(s) ds = f_y(ℓ)`; at `ℓ = log n`,
   `Λ(n) f_y(log n) = (Λ(n)/√n) K_y(log n)`.
3. **Pole-density integration by parts.** With `g = (e^s − 1) f_y' − e^s f_y`,
   `g' = (e^s − 1) f_y'' − e^s f_y`, `g(0) = −K_y(0)`, `g(∞) = 0` (decay rate `π − ½ > 1`):
   `∫_0^∞ (e^s − 1) f_y'' = K_y(0) + ∫_0^∞ K_y e^{s/2}`.
4. **Interchange.** `Σ_n Λ(n) ∫_{log n}^∞ (s − log n)|f_y''| ≤ (4C/c²) Σ_n Λ(n) n^{−c}`, `c = π − ½ > 1`,
   through `(s − ℓ)e^{−c(s−ℓ)} ≤ (2/c)e^{−c(s−ℓ)/2}`; Tonelli gives
   `∫_0^∞ D f_y'' = K_y(0) + ∫_0^∞ K_y e^{s/2} − Σ_n (Λ(n)/√n) K_y(log n) = K_y(0) − T(y)`,
   and `∫ ∂_sK_y Δ = 2K_y(0) − T(y)` (function-form transport law) gives the identity.
5. **Decay and uniform bound of `f_y''`.** `D'' = −2π²v/sinh(πv) − 4π cosh(πv)/sinh²(πv) + 4π²v cosh²(πv)/sinh³(πv)`
   off the origin, `|D''(v)| ≤ (64π + 264π²)(1+|v|)e^{−π|v|}` for `|v| ≥ 1`, compactness near `0`;
   `∂_s²K_y` in light-cone form decays like `e^{−(π−1)|s|}`; its Fourier form
   `−(1/π)∫cos(y√(r²+2)) sech²(r/2) r² cos(rs) dr` (dominated differentiation, uniqueness of derivatives)
   gives `|∂_s²K_y| ≤ (1/π)∫ r² sech²(r/2) dr` for all `y, s`; hence `|f_y''| ≤ C e^{−s/2}` with
   `C = (1/π)∫r²sech²(r/2) + 8 log 2/π + 1/π`.
6. **Möbius injection.** `D = Explicit + ℓ·M(e^s) + Head + Tail` for `s ≥ 0` (corpus split);
   `|Head(s)| ≤ (s+14)/4`, so `|∫_0^∞ Head f_y''| ≤ C ∫_0^∞ (s+14)/4 e^{−s/2}` uniformly in `y`;
   measurability of the head through the product-with-ℕ lemma for sums over `1 ≤ n ≤ ⌊φ(s)⌋₊`.

## No-go closure
Not a no-go. The Λ-free part `Explicit + ℓ·M + Tail` is a Mertens-type functional
`Σ_n μ(n) Φ_y(log n)` with `Φ_y(v) = ∫_0^∞ S(u) f_y''(u+v) du`; its one-sided bound is Wall 1
(`√x` cancellation) in Möbius coordinates. The injection of `Λ * 1 = log` changes the basis of the
zero-mode expansion (coefficients of `1/ζ'(ρ)` type on each piece summing to `1/ρ²`), not the
cancellation problem.

## Lean
Module `formal/GaloisForLFunctions/RHTower/CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection.lean`
(namespace `RHTower.CHMDChebyshevTransport`): `dAlembertDeriv2`, `hasDerivAt_dAlembertDeriv`,
`dAlembertDeriv2_of_ne`, `abs_dAlembertDeriv2_le_of_one_le`, `exists_abs_dAlembertDeriv2_le`,
`kernelDeriv2`, `hasDerivAt_kernelDeriv`, `exists_abs_kernelDeriv2_le`, `integrable_sq_mul_sechSqHalf`,
`sechSecondMoment`, `kernelDeriv2Fourier`, `hasDerivAt_kernelDerivFourier`,
`kernelDeriv2_eq_kernelDeriv2Fourier`, `abs_kernelDeriv2_le`, `conjugatedKernel`,
`conjugatedKernelDeriv`, `conjugatedLaplacian`, `laplacianBound`, `abs_conjugatedLaplacian_le`,
`exists_abs_conjugatedLaplacian_le`, `integral_Ioi_sub_mul_conjugatedLaplacian`,
`integral_Ioi_exp_sub_one_mul_conjugatedLaplacian`, `continuous_ccmLogChebyshevDeficitPrimitive`,
`abs_ccmLogChebyshevDeficitPrimitive_le`, `ccmLogChebyshevDeficitPrimitive_eq_tsum`,
`integral_deficitPrimitive_mul_conjugatedLaplacian`, `integral_kernelDeriv_mul_discrepancy_eq_conjugated`,
`riemannHypothesis_iff_integral_deficitPrimitive_mul_conjugatedLaplacian_bddAbove` / `_bddBelow`,
`mobiusDeficitRest`, `measurable_sum_Icc_floor`, `measurable_ccmPrimeDeficitMobiusTransientHead`,
`headBudget`, `abs_integral_head_mul_conjugatedLaplacian_le`,
`integral_mobiusDeficitRest_mul_conjugatedLaplacian`,
`riemannHypothesis_iff_integral_mobiusDeficitRest_mul_conjugatedLaplacian_bddAbove` / `_bddBelow`.
Audit: `lake env lean` clean; `lake build --old` olean; `#print axioms` on the main theorems in a
scratch file: only `propext`, `Classical.choice`, `Quot.sound`. Wired in `RHTower.lean` after
`CHMDPrimeKernelDerivativeUniformBound`. No full or umbrella build was run.

## Log
- 2026-10-17 — created directly in 3-formalized; STATUS MUST-1569.
