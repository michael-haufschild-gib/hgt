# Poisson prime history: Mertens-clock Calkin model and physical-clock wall — Lean certificate

- **Paper card:** `stc-poisson-mertens-clock-commutator.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.PoissonPrimeKernelCalkinModel`,
  `GaloisForLFunctions.RHTower.PoissonPrimeClockCommutator`,
  `GaloisForLFunctions.RHTower.PoissonPrimePhaseTwistThetaNoGo`,
  `GaloisForLFunctions.RHTower.MertensPrimeCellClock`,
  `GaloisForLFunctions.RHTower.WeylSpectrumCompactTransfer`,
  `GaloisForLFunctions.HTGeometry.SechSquareConvolutionKernel`,
  `GaloisForLFunctions.HTGeometry.WienerHopfPlaneWaveWeyl`,
  `GaloisForLFunctions.HTGeometry.SchurKernelOperator`; inputs `STCPoissonPrimePhysicalClockWall`,
  `Sieve.MertensSecondSharp`, `Sieve.PrimeLogPowerTail`, `HyperbolicLevyKhintchine`
  (`transform_sech_sq`), `SoninCalkinNormBound` (`essentialNorm`), `HedenmalmThetaTrace`,
  `HedenmalmThetaCompactDivisorEigenmode`, `HedenmalmPinnedVolterraBoundaryDefect`
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** `lake --old build` of every module; `lake --old env lean` clean (no warnings);
  `#print axioms` of all 57 main theorems = `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

Notation: `K = poissonPrimeOp` (matrix `stcPrimePoissonKernel`), `C = poissonPrimeCommOp`,
`h = sechSqHalf`, `j = sechSqHalfTilt`, `x_p = mertensPrimeClock p`, `t_p = stcClock p`,
`U = primeCellOp`, `A = mertensStepSechOp`, `W = wienerHopfSechOp`, `A_j = mertensStepTiltOp`,
`W_j = wienerHopfTiltOp`, `σ_ess = weylEssentialSpectrum` (unit weakly-null approximate eigenvectors),
`[0,4] = weylIntervalZeroFour`.

| Card item | Lean theorem |
|-|-|
| `K(p,q) = ∫_0^∞ u b_u(p) b_u(q) du = 4t_pt_q/(√(pq)(t_p+t_q)²)` | `stcPrimePoissonKernel_eq_integral_aperture`; history Gram `stcPrimePoissonKernel_eq_historyGram` (existing) |
| `K(p,q) = (pq)^{-1/2} h(x_p - x_q)`, `h = sech²(·/2)` | `stcPrimePoissonKernel_eq_sechSqHalf`, `sechSqHalf_eq_cosh` |
| (1) `K` bounded with matrix `K(p,q)`, positive, self-adjoint | `hasLpMatrix_poissonPrimeOp`, `isPositive_poissonPrimeOp`, `isSelfAdjoint_poissonPrimeOp` |
| (1) `σ_ess(K) = [0,4]`, `‖K‖_ess = 4`, noncompact | `weylEssentialSpectrum_poissonPrimeOp`, `essentialNorm_poissonPrimeOp`, `not_isCompactOperator_poissonPrimeOp` |
| (2) `X` (mult. by `x_p`) unbounded | `not_exists_hasLpMatrix_mertensClock` |
| (2) `K` maps the finite-support core into `Dom X`; `XK - KX = C` there | `memℓp_mertensClock_mul_poissonPrimeOp_core`, `mertensClock_mul_poissonPrimeOp_core` |
| (2) `C` bounded with matrix `(x_p-x_q)K(p,q)`, skew-adjoint | `hasLpMatrix_poissonPrimeCommOp`, `adjoint_poissonPrimeCommOp` |
| (2) `‖C‖_ess ≥ h(3)`, `C` noncompact (shell pairing `S_n × S_{n+2}`) | `sechSqHalf_three_le_essentialNorm_poissonPrimeCommOp`, `not_isCompactOperator_poissonPrimeCommOp`, `re_inner_mertensShellVec_le`, `clock_gap_of_shell` |
| (3) `K δ_q ∉ Dom T` for every `q` | `stcPrimePoissonKernel_physical_column_not_summable` (existing) |
| (4) `β < 0`: `T^β` compact, `[T^β,K]` compact | `isCompactOperator_physicalClockPowOp`, `isCompactOperator_physicalClockPow_commutator` |
| (4) `β = 0`: commutator `0`, `β`-derivative `= C(p,q)` | `physicalClockPow_commutator_zero`, `hasDerivAt_physicalClockPow_commutator` |
| (4) `0<β<1`: `K δ_q ∈ Dom T^β`; no bounded extension (all `β>0`) | `summable_physicalClockPow_column`, `not_exists_hasLpMatrix_physicalClockPow_commutator` |
| (4) `β ≥ 1`: `K δ_q ∉ Dom T^β` | `not_summable_physicalClockPow_column` |
| (5) `g ≠ 0`: no column of `K cosh`/`K sinh` in `H`; `g = 0` identities | `not_summable_evenReflected_column`, `not_summable_oddReflected_column`, `not_summable_reflected_column`, `reflected_kernels_zero` |
| shells `S_n`, `m_n → 1` (Mertens II) | `mertensShell`, `mem_mertensShell`, `mertensShellMass_eq`, `tendsto_mertensShellMass` |
| cells `I_p = [y_p, y_p+1/p)` tile `[0,∞)` | `primeCell`, `iUnion_primeCell`, `pairwise_disjoint_primeCell`, `primeCellIndex_spec` |
| sharp Mertens: `|y - x_p - B| ≤ D/log p`, `|φ(y) - y| ≤ D e^{-y}` | `abs_primeRecipMass_ceil_sub_le`, `abs_mertensStepClock_sub_le_div_log`, `exists_abs_mertensStepClock_sub_le` |
| `U` isometry onto step functions; `U* U = 1` | `primeCellIsometry`, `primeCellOp_single`, `adjoint_primeCellOp_comp`, `adjoint_primeCellOp_apply` |
| `U K U* = A` (step kernel `h(φ(y)-φ(z))`), `U C U* = A_j` | `primeCellOp_conj_poissonPrimeOp`, `primeCellOp_conj_poissonPrimeCommOp`, `clockKernel_range_proj` |
| (†) `UKU* - W` Hilbert–Schmidt; `UCU* - W_j` Hilbert–Schmidt | `isHilbertSchmidt_conj_poissonPrimeOp_sub`, `isHilbertSchmidt_conj_poissonPrimeCommOp_sub`, `lintegral_clock_sub_sq_lt_top`, `SchurKernel.isHilbertSchmidt_op` |
| `W ≥ 0` (Gram of translated histories), `‖W‖ ≤ 4` (`∫ h = 4`) | `isPositive_wienerHopfSechOp`, `SchurKernel.inner_op_eq_of_sechSqHalf`, `integral_sechLaplace`, `norm_wienerHopfSechOp_le`, `integral_sechSqHalf` |
| `ĥ(ξ) = 4π|ξ|/|sinh πξ|`, continuous, attains every value in `(0,4]` | `sechSqHalfSymbol_eq`, `continuous_sechSqHalfSymbol`, `exists_sechSqHalfSymbol_eq` |
| plane-wave Weyl sequences for `W`; `σ_ess(W) = [0,4]` | `norm_op_planeWavePacket_sub_sq_le`, `tendsto_norm_op_planeWavePacketSeq_sub`, `orthonormal_planeWavePacketSeq`, `weylEssentialSpectrum_wienerHopfSechOp` |
| `0 ∈ σ_ess(K)` via `‖K δ_p‖² ≤ A/p` | `zero_mem_weylEssentialSpectrum_poissonPrimeOp`, `SchurKernel.norm_op_cellVec_sq_le` |
| compact equivalence transfers Weyl spectra | `weylEssentialSpectrum_eq_of_isCompactOperator`, `mem_weylEssentialSpectrum_compression`, `mem_weylEssentialSpectrum_of_compression` |
| phase twist `D_τ`: `K_τ` matrix, `σ_ess`, `‖·‖_ess`, commutator class, physical wall | `phaseTwistEquiv`, `hasLpMatrix_twistedPoissonPrimeOp`, `weylEssentialSpectrum_twistedPoissonPrimeOp`, `essentialNorm_twistedPoissonPrimeOp`, `hasLpMatrix_twistedPoissonPrimeCommOp`, `sechSqHalf_three_le_essentialNorm_twistedPoissonPrimeCommOp`, `not_summable_twisted_physical_column` |
| theta source inverse `B` is not self-adjoint; no unitary `V` with `V B V* = UKU* - W` | `not_isSelfAdjoint_sourceInverse`, `not_isSelfAdjoint_thetaKernelOperator`, `not_exists_unitary_thetaKernelOperator_eq_poissonCalkinDefect` |

The non-self-adjointness is proved with the test vectors `1` and `t` (`B1 = 0`,
`⟪1, Bt⟫ = -(i/2)∫ q t(1-t) ≠ 0`) instead of the paper's a.e. kernel comparison; the
conclusion is the same.
