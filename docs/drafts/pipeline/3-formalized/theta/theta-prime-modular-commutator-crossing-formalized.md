# Ordered prime–modular theta commutator — Lean certificate

- **Paper card:** `theta-prime-modular-commutator-crossing.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaDeletionInversionCommutator` (items (1)–(10)),
  `GaloisForLFunctions.RHTower.ThetaQuadratureDefectSpectralKernel` (items (11)–(16)),
  `GaloisForLFunctions.RHTower.ThetaCommutatorKernelInertia` (infinite indices)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `lake env lean` audit clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no `sorry`.

Dictionary: `Θ = HurwitzZeta.evenKernel 0`, `S = thetaInversion`, `D_q = scaleDeletion q`,
`C_q(y) = deletionInversionCommutator q y`, `F(q, y) = commutatorProfile q y`,
`P = thetaLogProfile`, `R = thetaLogTail`, `K(a, b) = deletionInversionKernel a b`,
`L(λ) = halfLineLaplace thetaLogProfile λ` (continuation `thetaLogLaplaceC`), `M_z = wardMellin z`,
`H = thetaOneSidedConnection`, `B = quadratureDefect`, `w(τ) = commutatorSpectralWeight τ`
(`= Xi (2τ)/(τ² + 1/16)`, `XiC_ofReal`).

| Card item | Lean theorem |
|-|-|
| `S Θ = Θ`, `S² = 1` | `thetaInversion_evenKernel`, `thetaInversion_thetaInversion`, `evenKernel_zero_one_div` |
| (1) `C_q = q^{-1/2}Θ(y/q) - Θ(qy) = y^{-1/2}Θ(q/y) - Θ(qy)` | `deletionInversionCommutator_eq'`, `deletionInversionCommutator_eq`, `evenKernel_zero_div_inversion` |
| `D_{p²}Θ` deletes the atoms with `p ∣ n` | `hasSum_scaleDeletion_prime_sq` |
| (2) `C_q > 0` on `(0,1)`, `C_q(1) = 0`, `C_q < 0` on `(1,∞)` | `deletionInversionCommutator_pos`, `deletionInversionCommutator_one`, `deletionInversionCommutator_neg` |
| `S C_q = -C_q` | `thetaInversion_deletionInversionCommutator` |
| (3)/(6) `∂_q[-C_q(y)] = 2π Σ n²[y^{-3/2}e^{-πn²q/y} - y e^{-πn²qy}] > 0` | `hasDerivAt_neg_deletionInversionCommutator`, `hasDerivAt_commutatorProfile`, `commutatorProfileDeriv_pos`, `sqrt_pow_five_lt_exp` |
| (3) `0 < -C_q(y) < 1 - y^{-1/2}`, limit `y^{-1/2} - 1` | `neg_deletionInversionCommutator_bounds`, `tendsto_deletionInversionCommutator_atTop`, `strictMonoOn_commutatorProfile` |
| below the seam: strict increase from `0` to `y^{-1/2} - 1` | `strictMonoOn_deletionInversionCommutator`, `deletionInversionCommutator_lt`, `commutatorProfile_one_left` |
| (4) exchange symmetry, monotone in both arguments, boundary zeros, limits | `commutatorProfile_symm`, `strictMonoOn_commutatorProfile_right`, `commutatorProfile_one_left`, `commutatorProfile_one_right`, `tendsto_commutatorProfile_atTop`, `tendsto_commutatorProfile_atTop_right` |
| (5) `P` even, `e^{(a+b)/4}F(e^a,e^b) = P(a+b) - P(a-b)` | `thetaLogProfile_neg`, `exp_mul_commutatorProfile_exp` |
| (5a) `R = 2Σ e^{t/4-πn²e^t}` positive, strictly decreasing; vacuum/arithmetic split; both positive; `K_vac > K_arith` | `hasSum_thetaLogTail`, `thetaLogTail_pos`, `strictAntiOn_thetaLogTail`, `deletionInversionKernel_eq_vacuum_sub_arith`, `vacuumKernel_pos`, `arithKernel_pos`, `arithKernel_lt_vacuumKernel`, `deletionInversionKernel_pos` |
| (5b) Gram form of the vacuum | `vacuumKernel_eq_integral` |
| (7) two-scale Laplace pairing, `= 2[G(μ)-G(λ)]/(λ²-μ²) > 0` | `thetaLaplacePairing`, `thetaLaplacePairing_eq_G`, `thetaLaplacePairing_pos` (general: `laplacePairing`, `laplacePairing_of_ne`, `integral_triangle_swap`) |
| diagonal value (continuous derivative) | `thetaLaplacePairing_diag`, `hasDerivAt_halfLineLaplace`, `laplacePairing_diag_eq_deriv` |
| `G` strictly decreasing on `(1/4, ∞)` | `strictAntiOn_thetaLogLaplace_mul` |
| (8) `L(λ) = 1/(λ - 1/4) + M_{2iλ}` | `thetaLogLaplace_eq`, `integral_exp_mul_thetaLogTail` |
| (9) `H(2iλ) = (λ² - 1/16) L(λ) - λΘ(1)` (pole-free form for all `λ`) | `thetaOneSidedConnection_eq_laplace`, `thetaOneSidedConnection_two_I_mul` |
| (10) `Ξ(2iλ) = (λ² - 1/16)[L(λ) + L(-λ)]` | `XiC_two_I_mul_eq_laplace` |
| (11) `B` even, positive, integrable; Gaussian and `{x}` forms | `quadratureDefect_neg`, `quadratureDefect_pos`, `integrable_quadratureDefect`, `quadratureDefect_eq_gaussian`, `quadratureDefect_eq_fract`, `integral_gaussian_sub_tsum_eq_fract` |
| `P(t) = 2cosh(t/4) - B(t)` | `thetaLogProfile_eq_cosh_sub` |
| (12) `B̂(τ) = Ξ(2τ)/(τ² + 1/16)` | `fourier_quadratureDefect`, `integral_cexp_mul_thetaLogTail`, `integral_Ioi_cexp_mul_quadratureDefect` |
| Fourier inversion `B(t) = (1/π)∫₀^∞ w(τ) cos(τt) dτ` | `quadratureDefect_eq_inverse`, `quadratureDefect_eq_integral_cos`, `integrable_commutatorSpectralWeight` |
| (13) `K = 4 sinh sinh + (2/π)∫₀^∞ w sin sin` | `deletionInversionKernel_eq_spectral`, `deletionInversionKernel_eq_sinh` |
| (14) finite quadratic form | `quadraticForm_deletionInversionKernel` |
| (15) continuum quadratic form (continuous compactly supported `g`) | `integral_deletionInversionKernel_quadratic` |
| Hardy sign change of `Ξ` / `w` | `exists_Xi_neg`, `exists_commutatorSpectralWeight_neg` |
| infinite positive and negative index on the continuum of positive scales | `exists_positive_scales_positive_index`, `exists_positive_scales_negative_index` |
| (16) `K(A+x, A+y) = 4 sinh sinh + B(x-y) - B(2A+x+y)` | `deletionInversionKernel_translate` |
| infinite positive and negative index at prime scales `a_p = 2 log p` | `exists_primes_positive_index`, `exists_primes_negative_index` (Poisson: `tsum_quadratureDefect_lattice`, `exists_lattice_symbol_neg`; Toeplitz: `sum_range_sum_range_sub`, `tendsto_toeplitz_average`, `exists_negative_block`; Gram: `quadratic_neg_of_gram`, `blockGram_bounds`, `negIndex_of_block`; primes: `exists_prime_log_near`) |
