# Complex renewal resonances and infinite Pick index of the theta feedback loop — Lean certificate

- **Paper card:** `theta-renewal-complex-resonance-stieltjes-obstruction.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaRenewalDenominatorOrder` ((3)–(5c), real root,
  order one, infinite type), `GaloisForLFunctions.RHTower.ThetaRenewalResonanceDivisor` ((5d),
  infinitely many nonreal zeros, left location, resonance escape),
  `GaloisForLFunctions.RHTower.ThetaRenewalPhaseKernelNotMonotone` ((2), (6)–(8), residues of `J`,
  no real-rate mixture), `GaloisForLFunctions.RHTower.ThetaRenewalFeedbackLoop` ((9)–(14), infinite
  Pick index), `GaloisForLFunctions.RHTower.ThetaRenewalResonancePhase` ((11c)–(11e), Zeno law,
  Stokes rejection), `GaloisForLFunctions.RHTower.ThetaRenewalNuclearBoundary` ((15), (16));
  general layers `GaloisForLFunctions.HTGeometry.LogDerivativeResidue`,
  `GaloisForLFunctions.HTGeometry.DiagonallyDominantPosDef`; corpus `ThetaRenewalIncrement`,
  `ThetaRenewalLogKernel`, `OrderOneHadamardFactorization`, `CanonicalProductE1LogDeriv`,
  `XiHorizontalStripDecay`, `ThetaHalfPortStieltjesSpectral`, `ThetaHalfLinePortCrossings`,
  `HTGeometry.BernsteinWidder`, `HTGeometry.BoundedMultiplierHilbert`,
  `HTGeometry.BoundedMultiplierNonclosedRange`
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** targeted `lake build`; `lake env lean` audit clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound` for all 29 audited theorems; no `sorry`, no hypotheses
  beyond the card's own quantifiers.

Dictionary: `a = 1/4`, `c = Θ 1` (`Θ = evenKernel 0`), `ν = thetaRenewalIncrement`,
`N = thetaRenewalLaplace`, `D = thetaRenewalDenominator`, `Q = thetaRenewalLogKernel`,
`Q̂ = thetaRenewalLogKernelLaplace`, `W = thetaRenewalOddKernel`, `J = thetaRenewalPhaseTransform`,
`β = thetaRenewalDrift`, `A = thetaLoopA`, `B = thetaLoopB`, `K = thetaLoopK`,
`v = thetaLoopCharge`, `g = thetaLoopEnergy`, `P_K = thetaLoopPick`,
`d(y) = thetaLoopBoundaryValue y`, `θ = thetaResonancePhase`, `θ' = thetaResonancePhaseDeriv`,
`{y_j} = thetaSimpleOrdinates`, `d_j = thetaBoundaryDiagonal j`, `T = thetaBoundaryOperator`,
`H(-2y), H(2y)` via `thetaOneSidedConnection`.

| Card item | Lean theorem |
|-|-|
| (2) `Re[λ/(s²-λ²)] = Re λ (s²-|λ|²)/|s²-λ²|²` | `re_div_sq_sub_sq` |
| (3) `N` entire, `D = c - N` | `differentiable_thetaRenewalLaplace`, `differentiable_thetaRenewalDenominator`, `thetaRenewalLaplace_eq_sub` |
| (4) `0 < ν(t) ≤ K e^{(a+1)t - πe^t}` | `thetaRenewalIncrement_pos`, `thetaRenewalIncrement_le` (corpus) |
| (5) `|N(z)| ≤ K Γ`-envelope, `D` of finite order | `thetaRenewalLaplaceReal_neg_le`, `norm_thetaRenewalDenominator_le`, `exists_norm_thetaRenewalDenominator_le`, `exists_norm_thetaRenewalDenominator_le_sq` |
| `N` strictly decreasing on ℝ, `N' < 0`, limits `0` and `∞` | `strictAnti_thetaRenewalLaplaceReal`, `hasDerivAt_thetaRenewalLaplaceReal`, `tendsto_thetaRenewalLaplaceReal_atTop`, `tendsto_thetaRenewalLaplaceReal_atBot` |
| `N(-a) = q c < c`; exactly one real root `x_* < -a` | `thetaRenewalLaplaceReal_neg_quarter`, `thetaRenewalLaplaceReal_neg_quarter_lt`, `existsUnique_real_thetaRenewalDenominator_eq_zero`, `lt_of_thetaRenewalDenominator_ofReal_eq_zero` |
| (5b) `log M_D(R) = R log R + O(R)` | `thetaRenewalDenominator_log_growth` |
| (5c) `N(-R) ≥ (2π/R) exp((R+a+1) log R - π(R+2))` | `thetaRenewalLaplaceReal_neg_ge`, `self_le_thetaRenewalLaplaceReal_neg` |
| order exactly one, infinite type | `thetaRenewalDenominator_order_le_one`, `thetaRenewalDenominator_order_ge_one`, `thetaRenewalDenominator_infinite_type` |
| (5d) `D = D(0) e^{βz} ∏ E₁(z/ζ)`, `β = D'(0)/D(0) > 0`, `∑|ζ|^{-2} < ∞`, log-derivative | `thetaRenewalDenominator_eq_hadamard`, `exists_expAffine_mul_hadamardProduct_thetaRenewalDenominator`, `thetaRenewalDrift_pos`, `deriv_thetaRenewalDenominator_zero`, `integral_mul_thetaRenewalIncrement_pos`, `summable_inv_sq_thetaRenewalZeros`, `logDeriv_thetaRenewalDenominator` |
| infinitely many zeros; infinitely many nonreal zeros | `infinite_thetaRenewalDenominator_zeros`, `infinite_nonreal_thetaRenewalDenominator_zeros` |
| `|N(z)| ≤ N(Re z) ≤ N(-a) < c` for `Re z ≥ -a`: every zero has `Re ζ < -a` | `norm_thetaRenewalLaplace_le_real`, `re_lt_of_thetaRenewalDenominator_eq_zero` |
| resonance escape: finitely many zeros with `Re ζ ≥ -B`; `Re ζ → -∞` | `finite_thetaRenewalDenominator_zeros_re_ge`, `finite_zeroCopy_re_ge`, `tendsto_re_zeroCopyPoint_cofinite` |
| (6) `Q̂ = -log(1 - N/c)`, `Q̂' = N'/(c - N)` | `thetaRenewalLogKernelLaplace_eq` (corpus), `hasDerivAt_thetaRenewalLogKernelLaplace`, `integral_mul_cexp_thetaRenewalLogKernel_eq_logDeriv` |
| (7) `J(z) = 1/(z+a) - N'/(c-N)` on `Re z > 0` | `thetaRenewalPhaseTransform_eq`, `logDeriv_thetaRenewalDenominator_eq_laplace` |
| residue `m` of the continuation at every zero of multiplicity `m` | `tendsto_mul_thetaRenewalPhaseContinuation` (general: `tendsto_sub_mul_logDeriv_of_analyticOrderAt`) |
| (8) no completely monotone representation of `W` | `not_completelyMonotoneOn_thetaRenewalOddKernel`, `not_exists_laplaceMeasure_thetaRenewalOddKernel`, `not_forall_shifted_laplace_thetaRenewalOddKernel`, `stieltjesPairTransform_ofReal_eq`, `differentiableOn_stieltjesPairTransform` |
| no absolutely convergent signed/complex real-rate measure | `not_exists_complexLaplaceMeasure_thetaRenewalOddKernel` |
| (9) `Xi(2iλ) = (a+λ)D(λ)[1+K(λ)]`, `D(±λ) ≠ 0` on `|Re λ| < a` | `XiC_two_I_mul_eq_loop`, `XiC_two_I_mul_eq_thetaLoop`, `thetaLoopA_ne_zero`, `thetaLoopB_ne_zero` |
| (10) `B(x+iy) = conj A(-x+iy)`, `u = Re A(iy) = Xi(2y)/2`, `v = Im A(iy)` | `thetaLoopB_eq_conj`, `re_thetaLoopA_I_mul`, `thetaLoopCharge_eq` |
| (11) `v(y)/y → c` | `tendsto_thetaLoopCharge_div` |
| (11a) `A(iy) = icy + H(-2y)`, `B(iy) = -icy + H(2y)`, `v(y) = cy + o(1)` | `thetaLoopA_I_mul_eq`, `thetaLoopB_I_mul_eq`, `tendsto_thetaLoopCharge_sub` |
| (11b) `sup_{|x|≤b} |1+K(x+iy)| ≤ C e^{-κ|y|}/(1+|y|)`, every `0<κ<π/2` | `exists_norm_one_add_thetaLoopK_le` |
| `θ ∈ (0, π)`, `θ(0) = 0`, `θ → π/2`, `θ - π/2 = -arctan(u/v)` | `thetaResonancePhase_mem_Ioo`, `thetaResonancePhase_zero`, `tendsto_thetaResonancePhase`, `thetaResonancePhase_eq_arctan` |
| (11c) `θ' = (uv' - vu')/(u²+v²) = a/(a²+y²) + β + ∑ Re[1/(iy-ζ) + 1/ζ]` | `hasDerivAt_thetaResonancePhase`, `thetaResonancePhaseDeriv_eq`, `thetaResonancePhaseDeriv_eq_resonanceSum`, `summable_norm_resonanceTerm` |
| `v' → c`; `|u| + |u'| = O(e^{-κy})`, `|θ'| = O(e^{-κy}/y)` | `tendsto_thetaLoopChargeDeriv`, `exists_abs_deriv_Xi_le`, `exists_thetaResonancePhase_bounds` |
| (11d) `∫_Y^∞ |θ'| = O(e^{-κY})` | `exists_integral_abs_thetaResonancePhaseDeriv_le` |
| (11e) `d_j = 2θ'(y_j)` at every critical zero | `thetaResonancePhase_at_zero` |
| Zeno law: crossings of `θ = π/2` in both orientations above every height | `exists_thetaResonancePhase_crossing` |
| Stokes rejection: no reparametrization times a nowhere-zero scalar identifies `θ - π/2` with the Stokes crossing flow | `not_exists_reparam_stokesFlow_thetaResonancePhase` |
| (12) `∂_x g(0, y₀) = -2 v(y₀) d/dy Xi(2y)` | `hasDerivAt_thetaLoopEnergy`, `thetaLoopSlope_eq_deriv` |
| both signs arbitrarily high; `|K| > 1` and `|K| < 1` in the right collar near zeros | `exists_loop_gain_gt_one`, `exists_loop_gain_lt_one`, `one_lt_norm_thetaLoopK_of_energy_neg`, `norm_thetaLoopK_lt_one_of_energy_pos`, `infinite_zeros_boundaryValue_sign` |
| `v(y) > 0` for every `y > 0` | `thetaLoopCharge_pos` |
| (13) Pick-defect kernel, Hermitian | `thetaLoopPick`, `thetaLoopPick_swap` |
| `K(iy_j) = -1`, off-diagonal boundary values vanish | `thetaLoopK_I_mul_of_Xi_eq_zero`, `thetaLoopPick_boundary_eq_zero`, `tendsto_thetaLoopPick_offDiag` |
| (14) diagonal boundary limit `-X'(y_j)/v(y_j)` | `tendsto_thetaLoopPick_diag`, `one_sub_sq_norm_thetaLoopK` |
| infinite positive and infinite negative index of `P_K` | `exists_posDef_thetaLoopPick` (general: `posDef_of_diag_ge_of_offDiag_le`) |
| (15) `T e_j = d_j e_j` trace class | `thetaBoundaryOperator`, `thetaBoundaryOperator_coeFn`, `summable_abs_thetaBoundaryDiagonal`, `exists_abs_thetaLoopBoundaryValue_le`, `thetaBoundaryTraceNorm` |
| both spectral subspaces infinite; `d_j ≠ 0`, `d_j → 0`; infinitely many ordinates | `infinite_thetaBoundaryDiagonal_sign`, `thetaBoundaryDiagonal_ne_zero`, `tendsto_thetaBoundaryDiagonal`, `infinite_thetaSimpleOrdinates`, `finite_thetaSimpleOrdinates_le` |
| `T` injective, dense non-closed range, unbounded inverse | `thetaBoundaryOperator_injective`, `thetaBoundaryOperator_denseRange`, `not_isClosed_range_thetaBoundaryOperator`, `not_exists_lowerBound_thetaBoundaryOperator` |
| (16) `Res_{λ=iy_j} 1/(1+K) = 1/d_j` | `tendsto_residue_thetaInverseLoop` |
| `|1/d_j|` exceeds every power of `y_j`; both residue signs above every height | `exists_pow_le_abs_inv_thetaBoundaryDiagonal`, `exists_inv_thetaBoundaryDiagonal_sign_above` |
| no unweighted sum of residues converges | `not_summable_inv_thetaBoundaryDiagonal` |
