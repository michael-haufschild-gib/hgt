# Mertens-clock prime defect is trace class, the Xi inverse is not — Lean certificate

- **Paper card:** `stc-mertens-trace-class-xi-divisor-barrier.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.SchurKernelComposition`,
  `GaloisForLFunctions.RHTower.MertensClockDefectTraceClass`,
  `GaloisForLFunctions.RHTower.MertensClockDefectSignedSpectrum`,
  `GaloisForLFunctions.RHTower.SourceInverseTraceIdealNoGo`,
  `GaloisForLFunctions.RHTower.MertensClockRelativeDeterminant`; inputs
  `PoissonPrimeKernelCalkinModel` (Mertens clock, `A`, `W`, cells), `LidskiiSelfAdjoint`,
  `ProlateFourierSignSectors` (negative eigenfamilies), `BurnolDepthCompletion` (moment
  uniqueness), `VitaliConvergence`, `RegularizedDeterminantAlgebraicMultiplicity` (`entireDet2`),
  `HedenmalmThetaSourceDeterminantIdentity` (`det₂ = XiC(z)/XiC(0)`), `LpBoundedMultiplier`
- **Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build` of every module; `lake --old env lean` clean (no warnings);
  `#print axioms` of all 52 main theorems = `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

Notation: `A = mertensStepSechOp`, `W = wienerHopfSechOp`, `E = mertensClockDefectOp = A - W`,
`B_θ = thetaKernelOperator`, `D_rel = relativeDet`, band `[0,4] = weylIntervalZeroFour`.

| Card item | Lean theorem |
|-|-|
| `e = e₂ + e₃ + r` through the oriented displacement indicator; `E = T₂ + T₃ + T₅`, each HS∘HS | `ClockDefectProfile.op_eq_sum`, `comp_weight_first`, `comp_firstRev_weight`, `comp_orient_second`, `lintegral_clockOrientKernel_sq_lt_top`, `lintegral_clockOrientWeightKernel_sq_lt_top` |
| (1) `E ∈ S₁` (only the Mertens rate, exponential decay and `C²` of `h` are used) | `memSchattenClass_one_mertensStepSechOp_sub`, `isTraceClass_mertensStepSechOp_sub`, generic `ClockDefectProfile.memSchattenClass_one_op` |
| (1) `Tr E = 0` (`= ∫ e(y,y) dy`) | `opTrace_mertensStepSechOp_sub`, `ClockDefectProfile.opTrace_op`, `SchurKernel.opTrace_adjoint_comp_op`, `SchurKernel.hsInner_op` |
| (1) `E` self-adjoint, `E ≠ 0` | `isSelfAdjoint_mertensClockDefectOp`, `mertensClockDefectOp_ne_zero` |
| `det(I - zE) = det₂(I - zE)` | `fredholmDetOp_smul_mertensClockDefectOp` |
| `W` strictly positive | `re_inner_wienerHopfSechOp_pos` (Laplace Gram form + `eq_zero_of_sechLaplaceTransform_nat`) |
| `U* f = 0 ⇒ A f = 0`, `⟨E f, f⟩ < 0` on mean-zero cell functions | `mertensStepSechOp_eq_zero_of_mem`, `re_inner_mertensClockDefectOp_neg`, `cellHaar`, `finrank_cellHaarSpan` |
| (1) infinitely many negative eigenvalues | `exists_orthonormal_negative_eigenfamily_mertensClockDefectOp` (every `m`), `infinite_setOf_sgVal_neg_mertensClockDefectOp` |
| (1) a positive eigenvalue (trace neutrality, Lidskii) | `exists_sgVal_pos_mertensClockDefectOp`, `exists_pos_eigenpair_mertensClockDefectOp` |
| (2) `B_θ` (with `det₂ = XiC(z)/XiC(0)`) is not trace class | `not_isTraceClass_thetaKernelOperator`, `not_memSchattenClass_one_thetaKernelOperator`; general `not_isTraceClass_sourceInverse` |
| (3) no `B_θ = L E R + F` (`L, R` bounded, `F ∈ S₁`) | `thetaKernelOperator_ne_transport_mertensClockDefect`, general `sourceInverse_ne_transport_add`, `exists_sum_norm_inner_transport_le` |
| (4) `(λ-A)⁻¹ - (λ-W)⁻¹ = (λ-A)⁻¹ E (λ-W)⁻¹ ∈ S₁` | `resolvent_sub_resolvent_eq`, `isTraceClass_resolvent_sub_resolvent` |
| (4) `σ(W) ⊆ [0,4]`; `λ - A = (I + E(W-λ)⁻¹)(λ - W)` | `spectrum_wienerHopfSechOp_subset`, `algebraMap_sub_mertensStepSechOp_eq` |
| (4) `D_rel(λ) = det(I + E(W-λ)⁻¹)` analytic on `ℂ \ [0,4]` | `relativeDet`, `analyticOnNhd_relativeDet`, `differentiableOn_relativeDet` (Vitali: `differentiableOn_det2Op_comp`) |
| (4) zeros = eigenvalues of `A` off the band; real, `> 4`; isolated | `relativeDet_eq_zero_iff`, `relativeDet_zero_real_gt_four`, `eventually_relativeDet_ne_zero` |

The Fredholm determinant of a trace-class `T` is implemented as
`det(I + T) = det₂(I + T) e^{Tr T}` with `det₂` the corpus Carleman determinant of the coordinate
matrix (`fredholmDetOp`, `det2Op`, zero criterion `fredholmDetOp_eq_zero_iff`).

Three proof mechanisms differ from the paper (same conclusions): global HS factorization of the
clock defect instead of local nuclear block estimates; the pinned Volterra pairing
`⟨√2 sin(a_n t), P √2 cos(a_n t)⟩ = 1/a_n - 2/a_n³` (`a_n = (n+½)π`) instead of the
Riemann–von Mangoldt count for `B_θ ∉ S₁`; the Laplace Gram form of `W` with integer moments
instead of Plancherel for strict positivity.
