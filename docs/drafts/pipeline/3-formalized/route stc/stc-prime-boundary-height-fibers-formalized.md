# Spectral height fibres of the critical Euler prime boundary — Lean certificate

- **Paper card:** `stc-prime-boundary-height-fibers.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.STCPrimeBoundaryHeightFibers`,
  `GaloisForLFunctions.RHTower.STCPrimeLogSquarePoleScaling`,
  `GaloisForLFunctions.HTGeometry.ExponentialFeatureTangentSpace`; inputs `STCPrimeHeightFiberAbel`,
  `STCPrimeSquarePositivityWall`, `ZetaLogDerivResidue`, `STCGammaPrimeWallScaling`,
  `CoordinateMonomialTotality`
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` of all 57
  theorems = `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`x_{a,t,v} = primeHeightSource a t v`, `F(z) = primeLogSquareComplex (1 + z)`,
`L²((0,∞), r dr) = ExpTangentSpace`, `e^{-ar/2} = tangentExpFeature a`.

| Card item | Lean theorem |
|-|-|
| source `x_{a,t,v}(p) = v (log p) p^{-(1+av)/2} e^{it log p}` | `primeHeightSource`, `primeHeightSource_apply` |
| (1) exact ℓ² Gram `v² Σ (log p)² p^{-1-cv} e^{i(t-s)log p}` | `inner_primeHeightSource`, `primeLogSquareComplex_height_series`, `inner_stcVerticalPhaseTwist_stcBoundaryVec` |
| (2) equal heights `→ 4/(a+b)²`; distinct fixed heights `→ 0` | `tendsto_inner_primeHeightSource_same`, `tendsto_inner_primeHeightSource_ne` |
| (3) `(t-s)/v → κ` gives `(c - iκ)^{-2}` | `tendsto_inner_primeHeightSource_moving`, `tendsto_sq_mul_primeLogSquareComplex` |
| height continuity at fixed `v`; limits do not commute | `continuous_primeHeightSource`, `continuousOn_primeLogSquareComplex`, `primeHeightSource_limits_noncommuting` |
| (4) realization in `⊕_t L²(r dr)` with Gram (2); dense span | `HeightBoundarySpace`, `heightBoundaryVector`, `inner_heightBoundaryVector`, `dense_span_heightBoundaryVector` |
| same-height Gram of `e^{-ar/2}`; exponential span dense (Laplace uniqueness) | `inner_tangentExpFeature`, `dense_span_tangentExpFeature`, `dense_span_tangentExpFeature_nat` |
| (4) nonseparable; no separable strong realization / Gram-preserving maps | `not_separableSpace_heightBoundarySpace`, `not_separable_of_orthogonal_family`, `no_separable_strong_realization`, `no_separable_gram_preserving_realization` |
| (5) `F = (log ζ)'' - E`, `E = -H'` holomorphic on `Re > 1/2` | `primeLogSquareComplex_eq_logDeriv_deriv` (with `differentiableOn_xiPrimeLogHigherValuation_halfPlane`) |
| (6) `F(z) = z^{-2} + O(1)` from `Re z > 0` | `primeLogSquareContinuation_laurent_one`, `tendsto_sq_mul_primeLogSquareComplex` |
| zero-free line at nonzero height | `analyticAt_primeLogContinuation_one_line`, `tendsto_primeLogSquareComplex_fixed_nonzero_height` (existing) |
| (7) reader `Λ_τ`, domain, probes `z = v x`, `‖z‖² = v⁴F(av) → 0` | `boundaryReader`, `boundaryReaderDomain`, `readerProbe`, `readerProbe_mem_domain`, `norm_sq_readerProbe`, `tendsto_readerProbe` |
| (7) `Λ_τ(z) = v² F(av/2 - i(t-τ))`, `→ 4/a²` at `t = τ`, `→ 0` otherwise | `boundaryReader_readerProbe`, `tendsto_boundaryReader_readerProbe_same`, `tendsto_boundaryReader_readerProbe_ne` |
| (7) not closable | `boundaryReader_not_closable`, `boundaryReader_charge_ne_zero` |
| fixed grade: `v² P_{b_{v+2|g|}} → 0` in operator norm | `tendsto_norm_fixedGrade_channel` |
