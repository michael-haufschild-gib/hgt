# Critical seam coupling in the positive theta renewal family — Lean certificate

- **Paper card:** `theta-renewal-seam-critical-coupling.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaSeamCouplingFamily` ((1)–(3), (2), inverse
  source and seam cusp, (3a), (3b), physical-coupling phase), `GaloisForLFunctions.RHTower.XiStripInverseDecay`
  ((4)), `GaloisForLFunctions.RHTower.ThetaSeamCouplingZeros` (uniform limit of `X_r`, strip
  finiteness, infinitely many nonreal zeros), `GaloisForLFunctions.RHTower.ThetaSeamCouplingContacts`
  ((5)–(10), contact cascade, real zero count, Rouché clusters); general layers
  `GaloisForLFunctions.RHTower.EntireConstantShiftZeroCount` (Rouché count for a constant shift),
  `GaloisForLFunctions.HTGeometry.RealNonnegativeZeroEvenOrder` (even order at a nonnegative real
  zero); corpus `ThetaRenewalIncrement`, `ThetaRenewalLogKernel`, `ThetaRenewalFeedbackLoop`,
  `ThetaRenewalResonancePhase`, `ThetaCuspChargeLevelSpecificity` (`XiC_level_specificity`),
  `HedenmalmThetaSourceSpectrumExact`, `CausalThetaHalfLaplace`, `GlobalParityWall`,
  `RiemannGaussian.FiniteToEntireRouche`, `HTGeometry.ZeroDivisorCount`
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** targeted `lake build`; `lake env lean` audit clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound` for all 35 audited theorems; no `sorry`, no hypotheses
  beyond the card's own quantifiers.

Dictionary: `a = 1/4`, `c = Θ 1`, `C = thetaSeamConst = 2ac`, `N = thetaRenewalLaplace`,
`D_r = thetaCouplingDenominator r`, `X_r = thetaCouplingXi r`, `Q_r = thetaCouplingLogKernel r`,
`Q̂_r = thetaCouplingLogKernelLaplace r`, `P = thetaLogProfile`, `P_r = thetaCouplingProfile r`,
`A_r = thetaCouplingA r`, `H = thetaOneSidedConnection`, `θ_r = thetaCouplingPhase r`,
`θ_1 = thetaResonancePhase`, `(α_j, β_j)` with `IsXiNegativeComponent α β`, `m_j = xiComponentMin α β`,
`r_j = contactCoupling α β`, `δ_j(r) = contactGap α β r`, zero multiplicity `zeroMult`.

| Card item | Lean theorem |
|-|-|
| (1) `D_r = c - rN`, `X_r`, `C = 2ac` | `thetaCouplingDenominator`, `thetaCouplingXi`, `thetaSeamConst_eq`, `thetaCouplingDenominator_one`, `thetaCouplingDenominator_eq` |
| `q_r = rq < 1/6`; `|rN(z)| ≤ rqc < c`; `D_r` zero-free on `Re z ≥ -a` | `integral_mul_thetaRenewalDensity`, `mul_thetaRenewalMass_lt`, `norm_coupling_mul_thetaRenewalLaplace_le`, `thetaCouplingDenominator_ne_zero` |
| (2) `Q_r = Σ r^m ν^{⋆m}/(m c^m) > 0`, logarithmic kernel of `D_r` | `thetaCouplingLogKernel`, `summable_thetaCouplingLogKernel_terms`, `thetaCouplingLogKernel_pos`, `thetaCouplingLogKernelLaplace_eq`, `thetaCouplingDenominator_eq_exp`, `thetaCouplingLogKernel_one` |
| (3) `X_r = C(1 - r) + r Ξ(2z)`; `X_0 = C`, `X_1 = Ξ(2z)` | `thetaCouplingXi_eq`, `thetaCouplingXi_zero`, `thetaCouplingXi_one`, `thetaCouplingXi_ofReal` |
| inverse source `P_r = rP + (1 - r)c e^{at}` of `D_r/(λ - a)` | `integral_cexp_mul_thetaCouplingProfile` |
| even extension of `P_r`: derivative jump `2ac(1 - r) = C(1 - r)`; `P'(0) = 0` | `hasDerivWithinAt_thetaCouplingProfile_abs_Ici`, `hasDerivWithinAt_thetaCouplingProfile_abs_Iic`, `thetaCouplingProfile_seam_jump`, `hasDerivAt_thetaLogProfile_zero` |
| (4) `sup_{|v|≤B} |Ξ(u + iv)| → 0` as `|u| → ∞`, every `B` | `exists_norm_mul_XiC_le`, `exists_norm_XiC_mul_abs_re_le`, `exists_forall_norm_XiC_lt`, `tendstoUniformlyOn_XiC_strip` |
| `X_r → C(1 - r)` uniformly on strips as `|Re z| → ∞` (any real `r`, negative limit for `r > 1`) | `exists_forall_norm_thetaCouplingXi_sub_lt` |
| `iyN(iy) → ac`; each reflected term contributes `ac(1 - r)` | `tendsto_I_mul_thetaRenewalLaplace`, `tendsto_thetaCouplingA_sub`, `tendsto_reflected_thetaCouplingA_add`, `reflected_thetaCouplingA_I_mul` |
| `Q_r(0) = ra` against `Q(0) = a` | `thetaCouplingLogKernel_zero`, `thetaRenewalLogKernel_zero` (corpus) |
| (3a) `A_r(iy) = icy + ac(1 - r) + rH(-2y)` | `thetaCouplingA_I_mul_eq`, `re_thetaCouplingA_I_mul`, `im_thetaCouplingA_I_mul` |
| `Im A_r(iy) > 0`, `θ_r ∈ (0, π)`, `θ_r - π/2 = -arctan(Re/Im)` | `im_thetaCouplingA_I_mul_pos`, `thetaCouplingPhase_mem_Ioo`, `thetaCouplingPhase_eq_arctan`, `arg_eq_pi_div_two_sub_arctan` |
| (3b) `y(θ_r(y) - π/2) → -a(1 - r)`, `0 ≤ r < 1` | `tendsto_mul_thetaCouplingPhase_sub`, `tendsto_thetaOneSidedConnection_neg_two_mul` |
| `r = 1`: `θ_1 - π/2 = O_κ(e^{-κy}/y)`, sign changes above every height | `thetaCouplingPhase_one`, `exists_abs_thetaResonancePhase_sub_le`, `exists_thetaResonancePhase_gt_lt` |
| strip finiteness for `r ≠ 1`; finitely many real zeros | `finite_thetaCouplingXi_zeros_strip`, `finite_thetaCouplingXi_real_zeros`, `thetaCouplingXi_not_eventually_zero` |
| `0 < r < 1`: infinitely many nonreal zeros; unbounded imaginary parts | `infinite_thetaCouplingXi_nonreal_zeros`, `infinite_thetaCouplingXi_zeros`, `exists_thetaCouplingXi_zero_abs_im_gt` |
| `X_0` zero-free; `X_1` has infinitely many real zeros | `thetaCouplingXi_zero_ne_zero`, `infinite_thetaCouplingXi_one_real_zeros` |
| infinitely many disjoint bounded negative components, `α_j → ∞` | `exists_isXiNegativeComponent`, `IsXiNegativeComponent.eq_of_mem`, `infinite_isXiNegativeComponent`, `exists_isXiNegativeComponent_chain` |
| (5) `m_j < 0` attained inside, `r_j = C/(C - m_j) ∈ (0, 1)` | `xiComponentMin`, `IsXiNegativeComponent.exists_minimizer`, `IsXiNegativeComponent.xiComponentMin_neg`, `contactCoupling`, `IsXiNegativeComponent.contactCoupling_pos`, `IsXiNegativeComponent.contactCoupling_lt_one` |
| (6) `r < r_j`: `X_r > 0`; `r = r_j`: `X_r ≥ 0`, zero at every minimizer; `r_j < r < 1`: two zeros | `IsXiNegativeComponent.thetaCouplingXi_pos`, `IsXiNegativeComponent.thetaCouplingXi_contact_nonneg`, `IsXiNegativeComponent.thetaCouplingXi_contact_eq_zero`, `IsXiNegativeComponent.exists_two_zeros`, `IsXiNegativeComponent.contact_identity` |
| contact zeros have even multiplicity | `IsXiNegativeComponent.even_order_contact` (general: `exists_even_order_factor_of_real_nonneg`) |
| (7) `0 < 1 - r_j = |m_j|/(C + |m_j|) ≤ C_κ e^{-κα_j}`; `m_j → 0`, `r_j → 1` | `IsXiNegativeComponent.one_sub_contactCoupling`, `exists_one_sub_contactCoupling_le`, `exists_contact_near_one` |
| real zero count of `X_r` unbounded as `r ↑ 1`, finite for `r < 1` | `exists_le_ncard_thetaCouplingXi_real_zeros`, `finite_thetaCouplingXi_real_zeros` |
| (8) `Ξ(2z) - m_j = (z - y*)^{2k} h(z)`, `k ≥ 1`, `h(y*) > 0` | `IsXiNegativeComponent.exists_contact_taylor` |
| (9) `L(r) = -C(1 - r)/r`, `δ_j = m_j - L > 0`, `X_r = r[Ξ(2z) - m_j + δ_j]`, `δ_j → 0` | `contactGap`, `contactGap_eq`, `thetaCouplingXi_eq_contactGap`, `IsXiNegativeComponent.exists_contactGap_lt` |
| Rouché: exactly `2k_j` zeros near `y*`, none real, in `|Im z| < a`, converging to `y*` | `IsXiNegativeComponent.exists_nonreal_cluster` (general: `exists_zeroCount_add_const`, `zeroMult_const_mul`) |
| conjugate pairs and even reflections | `thetaCouplingXi_conj`, `thetaCouplingXi_neg`, `thetaCouplingXi_eq_zero_conj`, `thetaCouplingXi_eq_zero_neg` |
| (10) nonreal zeros in `|Im z| < a` for `r ∈ (r_j - ε_j, r_j)`; every `(r₀, 1)` contains such couplings | `IsXiNegativeComponent.exists_nonreal_cluster`, `exists_thetaCouplingXi_nonreal_zero_in_strip` |
| seam scaled with the input: `X = rΞ`, zero set unchanged | `scaledSeam_two_ended`, `scaledSeam_two_ended_eq_zero_iff` |
