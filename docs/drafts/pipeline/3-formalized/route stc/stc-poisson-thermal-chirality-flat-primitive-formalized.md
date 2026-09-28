# Prime Poisson commutator carries the flat theta primitive's bulk chirality — Lean certificate

- **Paper card:** `stc-poisson-thermal-chirality-flat-primitive.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier`,
  `GaloisForLFunctions.HTGeometry.FlatPrimitiveFourierCalculus`,
  `GaloisForLFunctions.HTGeometry.SchurKernelHalfLineCompression`,
  `GaloisForLFunctions.RHTower.PoissonThermalSymbolCalculus`,
  `GaloisForLFunctions.RHTower.PoissonThermalFullLineMultipliers`,
  `GaloisForLFunctions.RHTower.PoissonThermalTraceClassLift`,
  `GaloisForLFunctions.RHTower.PoissonThermalBoundaryTrace`; inputs `STCPoissonThermalChirality`,
  `SechSquareConvolutionKernel` (`ĥ = 4π|ξ|/|sinh πξ|`), `L2FourierMultiplier` (`fourierMulCLM`),
  `L2FourierIntegralBridge`, `CausalFourierBridge` (L¹ convolution theorem),
  `PoissonPrimeKernelCalkinModel`/`PoissonPrimeClockCommutator` (`U`, `K`, `C`, `A`, `A_j`, `W`,
  `W_j`), `MertensClockDefectTraceClass` (`A - W, A_j - W_j ∈ S₁`), `SchurKernelComposition`,
  `DiagonalEllTwoIndexed`, `TraceClassCyclicity`, `SoninOrthonormalCompactVanishing`
- **Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build` of every module; `lake --old env lean` clean (no warnings);
  `#print axioms` of all 257 declarations of the seven modules = `propext`, `Classical.choice`,
  `Quot.sound`; no `sorry`; lint gate has no finding in these modules.

Fourier convention.  Lean uses mathlib's `𝓕 f (w) = ∫ e^{-2πixw} f(x) dx`; the card's convention
`f̂(ξ) = ∫ f(x) e^{iξx} dx` is `ξ = -2πw`.  In Lean the multipliers are therefore stated as
`m(-2πw)`, `m'(-2πw)` and `σ(w) = (2πw)⁻¹ = -1/ξ` — literally the card's `m(ξ)`, `m'(ξ)`, `-1/ξ`.

Notation: `m = thermalSymbol`, `m' = thermalSymbolDeriv`, `F = primitiveThermalSymbol`,
`G = primitiveThermalSymbolDeriv`, `W_full = thermalConvOp`, `J_full = thermalCommOp`,
`S = flatPrimitiveOp` (maximal Fourier multiplier by `σ = flatSymbol`), `Φ(S) = flatCalculus Φ`,
`P₊ T P₊ = halfLineRestrict ∘L T ∘L halfLineExtend`, `C_P = poissonPrimeClockCommOp`,
`U = primeCellOp`.

| Card item | Lean theorem |
|-|-|
| `m` positive, even, strictly decreasing in `|ξ|`, `m ≤ 4`, `m(0) = 4` | `thermalSymbol_pos`, `thermalSymbol_even`, `thermalSymbol_strictAntiOn_pos`, `thermalSymbol_lt_of_abs_lt`, `thermalSymbol_le_four`, `thermalSymbol_zero` |
| `m'` odd, sign `-sgn ξ`, `sgn m' = sgn(-1/ξ)`, `m' = deriv m` | `thermalSymbolDeriv_neg`, `thermalSymbolDeriv_neg_of_pos`, `thermalSymbolDeriv_pos_of_neg`, `sign_thermalSymbolDeriv`, `hasDerivAt_thermalSymbol` |
| `m` identifies `|ξ|` only; joint symbol `(m, m')` injective | `thermalSymbol_eq_iff`, `thermalSymbol_joint_injective`, `thermal_orientation` |
| `F(t) = 4π/(t sinh(π/t))`, `G(t) = m'(-1/t)`, `F(0) = G(0) = 0`; `F(-1/ξ) = m`, `G(-1/ξ) = m'` | `primitiveThermalSymbol_of_ne`, `primitiveThermalSymbol_zero`, `primitiveThermalSymbolDeriv_zero`, `primitiveThermalSymbol_neg_inv`, `primitiveThermalSymbolDeriv_neg_inv` |
| `F` even, bounded (`0 ≤ F ≤ 4`); `G` odd, bounded, `sgn G = sgn` | `primitiveThermalSymbol_neg`, `primitiveThermalSymbol_nonneg`, `primitiveThermalSymbol_le_four`, `primitiveThermalSymbolDeriv_neg`, `abs_primitiveThermalSymbolDeriv_le`, `sign_primitiveThermalSymbolDeriv` |
| `∫ h e^{iξx} = m(ξ)`, `i ∫ x h e^{iξx} = m'(ξ)` | `fourier_thermalKernel`, `fourier_thermalTiltKernel` (derivative under the integral, `Real.hasDerivAt_fourier`), `sechSqHalfSymbol_eq_thermalSymbol` |
| (1) `W_full ↔ m`, `J_full ↔ m'` on `L²(ℝ)` | `thermalConvOp_eq_fourierMulCLM`, `thermalCommOp_eq_fourierMulCLM`; generic `convolutionKernel_op_eq_fourierMulCLM` |
| `J_full = i[X, W_full]` (bounded extension), kernel `i(x-y)h(x-y)`; self-adjoint | `thermalCommOp_ae_eq_commutator`, `SchurKernel.op_ae_eq_commutator`, `isSelfAdjoint_thermalCommOp` |
| (1) `S ↔ -1/ξ`: mean-zero compact tests lie in `dom S` and `S f = i∫_{-∞}^x f` | `FlatTest.fourier_I_flatPrimitive`, `FlatTest.mem_flatDomain`, `FlatTest.flatPrimitiveOp_apply` |
| `S` = maximal multiplier by `-1/ξ`: symmetric; `Φ ↦ Φ(S)` is a bounded `*`-calculus; `(t-λ)⁻¹ ↦ (S-λ)⁻¹` | `flatPrimitiveOp`, `inner_flatPrimitiveOp`, `flatCalculus_comp`, `flatCalculus_add`, `flatCalculus_one`, `adjoint_flatCalculus`, `norm_flatCalculus_le`, `flatResolvent_mem_flatDomain`, `flatPrimitiveOp_flatResolvent`, `flatResolvent_flatPrimitiveOp` |
| (1) `W_full = F(S)`, `J_full = G(S)` | `thermalConvOp_eq_flatCalculus`, `thermalCommOp_eq_flatCalculus` |
| (2) `sgn(J_full) = sgn(S)` | `sign_thermalCommSymbol`, `thermalCommSign_eq_flatPrimitiveSign`, `flatCalculus_sign_comp_primitiveThermalSymbolDeriv` |
| (3) `C_P = i[X_P, K]`, bounded self-adjoint; `U C_P U* = i A_j` | `poissonPrimeClockCommOp_core`, `isSelfAdjoint_poissonPrimeClockCommOp`, `primeCellOp_conj_poissonPrimeClockCommOp` |
| (3) `P₊ W_full P₊ = W`, `P₊ J_full P₊ = i W_j = i[Y, W]`; `U C_P U* = i[M_φ, A]` | `halfLine_compression_thermalConvOp`, `halfLine_compression_thermalCommOp`, `wienerHopfTiltOp_ae_eq_commutator`, `mertensStepTiltOp_ae_eq_commutator`, `adjoint_halfLineExtend`, `halfLineRestrict_comp_halfLineExtend` |
| (3) `U C_P U* - P₊ J_full P₊ ∈ S₁` (and `U K U* - P₊ W_full P₊ ∈ S₁`) | `memSchattenClass_one_primeClockComm_sub_compression`, `isTraceClass_primeClockComm_sub_compression`, `memSchattenClass_one_primeGram_sub_compression` |
| sign instability: `L = diag 2^{-n}`, `L' = diag (-1)ⁿ2^{-n}` compact self-adjoint, `L - L' ∈ S₁`, `sgn L - sgn L'` not compact | `sign_not_stable_under_traceClass`, `diagSignOp_dyadic`, `diagSignOp_signedDyadic_apply`, `not_isCompactOperator_diagSign_sub` |
| (5) `4 - m = (2π²/3)ξ² + O(ξ⁴)`, `m' = -(4π²/3)ξ + O(ξ³)`, `(-1/ξ)m' → 4π²/3` | `isBigO_four_sub_thermalSymbol`, `isBigO_thermalSymbolDeriv_add`, `tendsto_neg_inv_mul_thermalSymbolDeriv`, `tendsto_four_sub_thermalSymbol_div_sq` |
| (5) square-root edge law `|S| ∼ π√(2/3)/√(4 - W_full)` | `tendsto_sqrt_four_sub_thermalSymbol_div_abs` |
| (7) `[W, J]` kernel `i∫_{z<0}(x+y-2z)h(x-z)h(y-z)dz = i(PQ* + QP*)` | `wienerHopf_commutator_kernel`, `wienerHopf_commutator_eq`, `wienerHopf_commutator_smul` |
| (6) `[W, J] ∈ S₁`, `tr[W, J] = 2i∫₀^∞ u²h(u)² du` | `memSchattenClass_one_wienerHopf_commutator`, `opTrace_wienerHopf_commutator_eq_anomaly`, `integral_Ici_integral_Ici_add` |
| (6) `= i/(2π)∫|m'|²` (Plancherel) | `integral_thermalSymbolDeriv_sq`, `integral_sq_mul_sechSqHalf_sq` |
| (6) `[A, C] ∈ S₁`, `tr[A, C] = tr[W, J] ≠ 0` | `boundary_trace_anomaly`, `commutator_add_traceClass`, `opTrace_commutator_eq_zero`, `boundaryAnomaly_pos` |

Proof-mechanism differences from the paper (same conclusions): the trace-class lift (3) is the
global HS factorization of the clock defect for the tilted profile `j = s h(s)` (already proved for
the MTC card) instead of the block decomposition (4) with local nuclear estimates; the Fourier
multiplier theorem for convolution is proved on Schwartz functions and extended by density; the
bounded Borel calculus of `S` is the multiplier calculus of its maximal Fourier realization, pinned
to `S` by its resolvents; the sign of a diagonal operator is its diagonal Borel calculus.
