# Continuum tangent space of the critical Euler prime source — Lean certificate

- **Paper card:** `stc-euler-prime-boundary-tangent-space.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.STCPrimeBoundaryTangentSpace`,
  `GaloisForLFunctions.RHTower.STCPrimeBoundaryGammaLaw`, `GaloisForLFunctions.RHTower.STCPrimeLogSquarePoleScaling`,
  `GaloisForLFunctions.HTGeometry.ExponentialFeatureTangentSpace`; inputs `STCEulerPrimeBoundaryTangentGram`,
  `STCGammaPrimeHilbertChamber`, `STCGammaPrimeWallScaling`, `STCSourceWorkSeamEnergy`, mathlib Lévy continuity
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` = `propext`,
  `Classical.choice`, `Quot.sound` (45 theorems in the two card modules, plus the audited shared
  layers); no `sorry`.

`b_u = stcBoundaryVec u`, `S(u) = ‖b_u‖²`, `v b_{av} = tangentProbe a v`,
`f_a = tangentExpFeature a ∈ ExpTangentSpace = L²((0,∞), t dt)`, `μ_{a,v} = primeBoundaryLaw a v`.

| Card item | Lean theorem |
|-|-|
| `S(u) = Σ (log p)² p^{-1-u}` | `norm_sq_stcBoundaryVec_eq_moment` |
| (1) `S(v) = v^{-2} + O(1)` | `exists_tendsto_norm_sq_stcBoundaryVec_sub_pole`, `exists_bound_norm_sq_stcBoundaryVec_sub_pole` |
| (1) `v² ⟪b_{bv}, b_{av}⟫ → 4/(a+b)² = ⟪f_b, f_a⟫` | `inner_tangentProbe`, `tendsto_inner_tangentProbe`, `inner_tangentExpFeature`, `tendsto_stcEulerPrimeBoundaryTangentGram` (existing) |
| (2) `‖Σ c_j v b_{a_j v}‖² → ∫ t |Σ c_j e^{-a_j t/2}|² dt` | `tendsto_norm_sq_sum_tangentProbe`, `norm_sq_sum_tangentExpFeature_integral` |
| (2) strict positivity for distinct `a_j` | `tangent_limit_integral_pos`, `linearIndependent_tangentExpFeature`, `norm_sum_tangentExpFeature_pos` |
| exponential span dense in `L²((0,∞), t dt)` | `dense_span_tangentExpFeature`, `dense_span_tangentExpFeature_nat` |
| `v b_{av} ⇀ 0` weakly in `ℓ²(primes)` | `tendsto_inner_tangentProbe_weak`, `tendsto_inner_lp_of_coord_eventually` |
| `μ_{a,v}` probability law; Laplace `S((a+λ)v)/S(av) → (a/(a+λ))²` | `primeBoundaryLaw`, `isProbabilityMeasure_primeBoundaryLaw`, `laplace_primeBoundaryLaw`, `tendsto_laplace_primeBoundaryLaw` |
| weak convergence to the Gamma law `a² t e^{-at} dt` | `charFun_primeBoundaryLaw`, `tendsto_charFun_primeBoundaryLaw`, `charFun_gammaMeasure_two`, `tendsto_primeBoundaryProbability` |
| (3)–(4) Euler identity and pole | `primeLogSquareComplex_eq_logDeriv_deriv`, `primeLogSquareContinuation_laurent_one`, `tendsto_sq_mul_primeLogSquareComplex` |
| `Q_{u,g} = (P_{b_{u-g}} - P_{b_{u+g}})/2` in the chamber | `stcGammaChamberOp`, `hasLpMatrix_stcGammaChamberOp` |
| (5) `v² Q_{κv,λv} = (P_{v b_{(κ-λ)v}} - P_{v b_{(κ+λ)v}})/2`; bounded; strongly null | `sq_smul_stcGammaChamberOp`, `eventually_norm_sq_smul_stcGammaChamberOp_le`, `tendsto_sq_smul_stcGammaChamberOp_apply` |
| (6) moving matrix elements → those of `Q^tan` | `tangentGradeOp`, `tendsto_matrixElement_sq_smul_stcGammaChamberOp` |
| (6) rank two for `λ ≠ 0`; compact | `finrank_range_tangentGradeOp`, `isCompactOperator_tangentGradeOp` |
| (7) kernel `e^{-κ(t+s)/2} sinh(λ(t+s)/2)` relative to `s ds` | `tangentGradeOp_kernel` |
| fixed grade: `v² Q_{|g|+v,g} = sign(g)(P_{v b_v} - P_{v b_{v+2|g|}})/2` | `sq_smul_stcGammaWallOp`, `hasLpMatrix_stcGammaWallOp` (existing) |
| second vector → 0; matrix elements → `sign(g) P_{f_1}/2` | `tendsto_norm_smul_stcBoundaryVec_shift`, `tendsto_matrixElement_fixedGrade` |
| finite part `Q_{|g|+v,g} - sign(g)P_{b_v}/2 → -sign(g)P_{b_{2|g|}}/2` in operator norm | `tendsto_stcGammaWallOp_sub_leading`, `tendsto_stcBoundaryVec`, `continuous_rankOne_self` |
