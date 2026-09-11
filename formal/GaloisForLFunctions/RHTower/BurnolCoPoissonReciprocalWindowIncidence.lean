import GaloisForLFunctions.RHTower.BurnolCoPoissonCompletedZeroJets
import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin
import GaloisForLFunctions.RHTower.DeningerBurnolConormalRadialTopBoundaryComparison

/-!
# Actual Burnol reciprocal-window conormal incidence

The Fourier image of the logarithmic co-Poisson subwindow is the actual
indicator-window co-Poisson vector. Its absolutely convergent Mellin integral
on the whole open strip gives the reciprocal endpoint germ at the unchanged
parameter. Exact multiplicity jets retain the original nonzero zeta conormal
and Gamma completion.

The two literal completed doubled-window jet quotients give inverse centered
characters. Their squared-norm difference is the fixed physical Burnol radial
defect, and hence the complete cross-prime incidence value at the original zero
copy and depth. This is a source comparison: its radial defect vanishes exactly
on the critical line, and no annihilation of that defect is asserted.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

private theorem burnolWindow_mellin_integrable_of_profile
    {f : ℝ → ℂ} {C : ℝ} (hf : Measurable f)
    (hbound : ∀ t : ℝ, ‖f t‖ ≤ C * (1 + |t|)⁻¹)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn (fun t : ℝ => f t * (t : ℂ) ^ (-w)) (Ioi (0 : ℝ)) := by
  have hC : 0 ≤ C := le_trans (norm_nonneg (f 0))
    (by simpa only [abs_zero, add_zero, inv_one, mul_one] using hbound 0)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => f t * (t : ℂ) ^ (-w)) volume :=
    (hf.mul ((Complex.measurable_ofReal.pow_const _).comp measurable_id)).aestronglyMeasurable
  have hnear : IntegrableOn (fun t : ℝ => f t * (t : ℂ) ^ (-w)) (Ioc (0 : ℝ) 1) := by
    refine Integrable.mono' (g := fun t : ℝ => C * t ^ (-w.re))
      (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -w.re)
        (by linarith)).1).const_mul C) hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (norm_le_of_decayProfile' hbound t)
      (Real.rpow_pos_of_pos ht.1 _).le
  have hfar : IntegrableOn (fun t : ℝ => f t * (t : ℂ) ^ (-w)) (Ioi (1 : ℝ)) := by
    refine Integrable.mono' (g := fun t : ℝ => C * t ^ (-w.re - 1))
      ((integrableOn_Ioi_rpow_of_lt (a := -w.re - 1) (by linarith)
        (by norm_num : (0 : ℝ) < 1)).const_mul C) hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hi : (1 + |t|)⁻¹ ≤ t⁻¹ := by
      rw [abs_of_pos ht0]
      exact (inv_le_inv₀ (by linarith : 0 < 1 + t) ht0).2 (by linarith)
    have hb : ‖f t‖ ≤ C / t :=
      (hbound t).trans (by simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hi hC)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.neg_re]
    refine (mul_le_mul_of_nonneg_right hb (Real.rpow_pos_of_pos ht0 _).le).trans_eq ?_
    rw [Real.rpow_sub ht0, Real.rpow_one]
    ring
  have hu : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hu]
  exact hnear.union hfar

/-- Every actual indicator-window co-Poisson vector has an absolutely convergent strip Mellin integral. -/
theorem integrableOn_burnolCoPoisson_windowIndicator_cpow
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn (fun t : ℝ =>
      burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t *
        (t : ℂ) ^ (-w)) (Ioi (0 : ℝ)) :=
  burnolWindow_mellin_integrable_of_profile
    (measurable_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed hc hcd)
    (norm_burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed_le_profile hc hcd) hw0 hw1

/-- Exact Mellin transform of the actual co-Poisson indicator-window vector. -/
theorem integral_Ioi_burnolCoPoisson_windowIndicator_cpow
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ t in Ioi (0 : ℝ),
      burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed c d) t *
        (t : ℂ) ^ (-w)) =
      riemannZeta w * (((d : ℂ) ^ (1 - w) - (c : ℂ) ^ (1 - w)) / (1 - w)) := by
  have hsupp : Function.support (coPoissonWindowIndicatorSeed c d) ⊆
      Icc (subWindowAperture c d) (subWindowAperture c d)⁻¹ := by
    simpa only [subWindowAperture] using
      support_coPoissonWindowIndicatorSeed_symmetric hc hcd
  rw [integral_Ioi_burnolCoPoisson_cpow (subWindowAperture_pos hc hcd)
    (integrable_coPoissonWindowIndicatorSeed c d) hsupp hw0 hw1
    (integrableOn_burnolCoPoisson_windowIndicator_cpow hc hcd hw0 hw1)]
  congr 1
  have hpt (u : ℝ) : coPoissonWindowIndicatorSeed c d u * (u : ℂ) ^ (-w) =
      Set.indicator (Icc c d) (fun v : ℝ => (v : ℂ) ^ (-w)) u := by
    by_cases hu : u ∈ Icc c d
    · rw [coPoissonWindowIndicatorSeed_of_mem hu, Set.indicator_of_mem hu, one_mul]
    · rw [coPoissonWindowIndicatorSeed_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
  have hinter : Ioi (0 : ℝ) ∩ Icc c d = Icc c d :=
    Set.inter_eq_right.mpr fun _ hx => lt_of_lt_of_le hc hx.1
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u),
    MeasureTheory.setIntegral_indicator measurableSet_Icc, hinter,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hcd,
    integral_cpow (Or.inl (by rw [Complex.neg_re]; linarith))]
  rw [show -w + 1 = 1 - w by ring]

/-- Completed Mellin evaluation of the actual Fourier image of the original
logarithmic subwindow, at the unchanged Mellin parameter. -/
def burnolCoPoissonReciprocalWindowCompletedEvaluation
    (L : ℝ) (hL : 0 ≤ L) (w : ℂ) : ℂ :=
  soninMellinEvaluation w
    ((soninCosineUnitary (coPoissonSubWindowEven (Real.exp_pos (-L))
      (Real.exp_le_one_iff.mpr (by linarith [hL]))) : evenSubspace) : SoninL2)

/-- The literal Fourier partner has the reciprocal endpoint germ on the
whole open strip; the original divisor is not reflected. -/
theorem burnolCoPoissonReciprocalWindowCompletedEvaluation_eq
    {L : ℝ} (hL : 0 < L) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolCoPoissonReciprocalWindowCompletedEvaluation L hL.le w =
      mellinCompletionFactor w * riemannZeta w *
        ((Complex.exp ((L : ℂ) * (1 - w)) - 1) / (1 - w)) := by
  have hc := Real.exp_pos (-L)
  have hcd : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hae := coeFn_soninCosineUnitary_coPoissonSubWindowEven hc hcd
  have hseed : coPoissonReciprocalSeed
      (coPoissonSubWindowSeed (Real.exp (-L)) 1) =
      coPoissonWindowIndicatorSeed 1 (Real.exp L) := by
    rw [coPoissonReciprocalSeed_subWindow_eq hc hcd, inv_one, Real.exp_neg, inv_inv]
  rw [hseed] at hae
  have hint : (∫ t in Ioi (0 : ℝ),
      (((soninCosineUnitary (coPoissonSubWindowEven hc hcd) : evenSubspace) : SoninL2) :
        ℝ → ℂ) t * soninMellinKernel w t) =
      ∫ t in Ioi (0 : ℝ),
        burnolCoPoissonRightSum (coPoissonWindowIndicatorSeed 1 (Real.exp L)) t *
          (t : ℂ) ^ (-w) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hae] with t ht
    exact congrArg (fun z : ℂ => z * (t : ℂ) ^ (-w)) ht
  have hexp : ((Real.exp L : ℝ) : ℂ) ^ (1 - w) =
      Complex.exp ((L : ℂ) * (1 - w)) := by
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos L))),
      ← Complex.ofReal_log (Real.exp_pos L).le, Real.log_exp]
  rw [burnolCoPoissonReciprocalWindowCompletedEvaluation, soninMellinEvaluation,
    hint, integral_Ioi_burnolCoPoisson_windowIndicator_cpow
      (by norm_num : (0 : ℝ) < 1) (Real.one_le_exp hL.le) hw0 hw1,
    hexp, Complex.ofReal_one, Complex.one_cpow, mul_assoc]

private theorem iteratedDeriv_zeta_mul_at_Xi
    (rho : XiDivisorSupport) {j : ℕ} (hj : j ≤ burnolCoPoissonXiConormalOrder rho)
    {g : ℂ → ℂ} (hg : ContDiffAt ℂ j g (rho : ℂ)) :
    iteratedDeriv j (riemannZeta * g) (rho : ℂ) =
      iteratedDeriv j riemannZeta (rho : ℂ) * g (rho : ℂ) := by
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact (ne_of_lt (xi_divisor_support_re_mem_open_unit rho).2) hre
  rw [iteratedDeriv_mul (analyticOn_riemannZeta (rho : ℂ) hne1).contDiffAt hg,
    Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    have hilt : i < burnolCoPoissonXiConormalOrder rho :=
      lt_of_lt_of_le (lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hij) hj
    rw [(riemannZeta_exact_jet_at_burnolCoPoissonXiConormalOrder rho).1 i hilt]
    simp
  · simp

/-- All jets through the exact Xi multiplicity of the actual completed
Fourier partner retain the same original zeta jet. -/
theorem iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) {j : ℕ}
    (hj : j ≤ burnolCoPoissonXiConormalOrder rho) :
    iteratedDeriv j (burnolCoPoissonReciprocalWindowCompletedEvaluation L hL.le)
        (rho : ℂ) =
      mellinCompletionFactor (rho : ℂ) * iteratedDeriv j riemannZeta (rho : ℂ) *
        ((Complex.exp ((L : ℂ) * (1 - (rho : ℂ))) - 1) / (1 - (rho : ℂ))) := by
  let U : Set ℂ := {w | 0 < w.re ∧ w.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  let g : ℂ → ℂ := fun w => mellinCompletionFactor w *
    ((Complex.exp ((L : ℂ) * (1 - w)) - 1) / (1 - w))
  have hEq : Set.EqOn (burnolCoPoissonReciprocalWindowCompletedEvaluation L hL.le)
      (riemannZeta * g) U := by
    intro w hw
    rw [burnolCoPoissonReciprocalWindowCompletedEvaluation_eq hL hw.1 hw.2]
    dsimp only [Pi.mul_apply, g]
    ring
  have hden : 1 - (rho : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [(xi_divisor_support_re_mem_open_unit rho).2]
  have hg : ContDiffAt ℂ j g (rho : ℂ) := by
    apply ContDiffAt.mul
    · exact (analyticAt_mellinCompletionFactor_of_re_pos
        (xi_divisor_support_re_mem_open_unit rho).1).contDiffAt
    · fun_prop
  rw [hEq.iteratedDeriv_of_isOpen hUopen j (xi_divisor_support_re_mem_open_unit rho),
    iteratedDeriv_zeta_mul_at_Xi rho hj hg]
  dsimp only [g]
  ring

/-- Exact leading completed jet of the original window, with its Gamma
factor and original zeta conormal both retained. -/
theorem iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonExpWindowCompletedEvaluation L hL.le) (rho : ℂ) =
      mellinCompletionFactor (rho : ℂ) *
        iteratedDeriv (burnolCoPoissonXiConormalOrder rho) riemannZeta (rho : ℂ) *
        ((Complex.exp ((L : ℂ) * (rho : ℂ)) - 1) / (rho : ℂ)) := by
  let U : Set ℂ := {w | 0 < w.re ∧ w.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  let g : ℂ → ℂ := fun w => mellinCompletionFactor w *
    ((Complex.exp ((L : ℂ) * w) - 1) / w)
  have hEq : Set.EqOn (burnolCoPoissonExpWindowCompletedEvaluation L hL.le)
      (riemannZeta * g) U := by
    intro w hw
    rw [burnolCoPoissonExpWindowCompletedEvaluation_eq hL hw.1 hw.2]
    dsimp only [Pi.mul_apply, g, burnolCoPoissonExpWindowZetaMellinGerm]
    ring
  have hden : (rho : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [(xi_divisor_support_re_mem_open_unit rho).1]
  have hg : ContDiffAt ℂ (burnolCoPoissonXiConormalOrder rho) g (rho : ℂ) := by
    apply ContDiffAt.mul
    · exact (analyticAt_mellinCompletionFactor_of_re_pos
        (xi_divisor_support_re_mem_open_unit rho).1).contDiffAt
    · fun_prop
  rw [hEq.iteratedDeriv_of_isOpen hUopen _ (xi_divisor_support_re_mem_open_unit rho),
    iteratedDeriv_zeta_mul_at_Xi rho le_rfl hg]
  dsimp only [g]
  ring

/-- The actual Fourier partner has no lower jet below the original exact
Xi multiplicity. -/
theorem iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation_eq_zero_of_lt
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    iteratedDeriv j (burnolCoPoissonReciprocalWindowCompletedEvaluation L hL.le)
      (rho : ℂ) = 0 := by
  rw [iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation hL rho hj.le,
    (riemannZeta_exact_jet_at_burnolCoPoissonXiConormalOrder rho).1 j hj]
  simp

private theorem burnolReciprocalWindow_lead_ne_zero (rho : XiDivisorSupport) :
    mellinCompletionFactor (rho : ℂ) *
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho) riemannZeta (rho : ℂ) /
        (1 - (rho : ℂ)) ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (mellinCompletionFactor_ne_zero
      (xi_divisor_support_re_mem_open_unit rho).1)
      (iteratedDeriv_riemannZeta_ne_zero_at_burnolCoPoissonXiConormalOrder rho)
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [(xi_divisor_support_re_mem_open_unit rho).2]

/-- Fourier transport preserves the exact nonzero conormal at the original
Xi divisor, including the archimedean completion. -/
theorem iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation_ne_zero
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
      (burnolCoPoissonReciprocalWindowCompletedEvaluation L hL.le) (rho : ℂ) ≠ 0 := by
  rw [iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation hL rho le_rfl]
  have hpos : 0 < (1 - (rho : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [(xi_divisor_support_re_mem_open_unit rho).2]
  convert burnolCoPoissonSubWindowConormalCoefficient_ne_zero hL hpos
    (burnolReciprocalWindow_lead_ne_zero rho) using 1
  dsimp only [burnolCoPoissonSubWindowConormalCoefficient]
  ring

/-- Centered quotient of literal Gamma-completed Mellin jets of the
original windows of lengths `L` and `2L`. -/
def burnolCoPoissonCompletedWindowConormalCharacter
    (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport) : ℂ :=
  Complex.exp (-(L : ℂ) / 2) *
    (iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
      (burnolCoPoissonExpWindowCompletedEvaluation (2 * L) (by positivity)) (rho : ℂ) /
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonExpWindowCompletedEvaluation L hL.le) (rho : ℂ) - 1)

/-- Centered quotient of literal completed jets of the actual Fourier
partners, evaluated at the same original divisor and multiplicity. -/
def burnolCoPoissonReciprocalWindowConormalCharacter
    (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport) : ℂ :=
  Complex.exp (-(L : ℂ) / 2) *
    (iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
      (burnolCoPoissonReciprocalWindowCompletedEvaluation (2 * L) (by positivity))
        (rho : ℂ) /
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonReciprocalWindowCompletedEvaluation L hL.le) (rho : ℂ) - 1)

/-- Completion cancels from the actual original-window quotient, without
changing its conormal character. -/
theorem burnolCoPoissonCompletedWindowConormalCharacter_eq
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    burnolCoPoissonCompletedWindowConormalCharacter L hL rho =
      burnolCoPoissonCenteredConormalCharacter L (rho : ℂ) := by
  let lead : ℂ := mellinCompletionFactor (rho : ℂ) *
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho) riemannZeta (rho : ℂ) / (rho : ℂ)
  have hlead : lead ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (mellinCompletionFactor_ne_zero
        (xi_divisor_support_re_mem_open_unit rho).1)
        (iteratedDeriv_riemannZeta_ne_zero_at_burnolCoPoissonXiConormalOrder rho)
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [(xi_divisor_support_re_mem_open_unit rho).1]
  have hjet (T : ℝ) (hT : 0 < T) :
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonExpWindowCompletedEvaluation T hT.le) (rho : ℂ) =
      burnolCoPoissonSubWindowConormalCoefficient T (rho : ℂ) lead := by
    rw [iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq hT]
    dsimp only [burnolCoPoissonSubWindowConormalCoefficient, lead]
    ring
  rw [burnolCoPoissonCompletedWindowConormalCharacter, hjet (2 * L) (by positivity),
    hjet L hL]
  exact burnolCoPoisson_centered_doubledWindowConormalRatio_eq hL
    (xi_divisor_support_re_mem_open_unit rho).1 hlead

/-- The actual Fourier-partner quotient carries the reciprocal endpoint
character at the unchanged original divisor. -/
theorem burnolCoPoissonReciprocalWindowConormalCharacter_eq
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    burnolCoPoissonReciprocalWindowConormalCharacter L hL rho =
      burnolCoPoissonCenteredConormalCharacter L (1 - (rho : ℂ)) := by
  let lead : ℂ := mellinCompletionFactor (rho : ℂ) *
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho) riemannZeta (rho : ℂ) /
      (1 - (rho : ℂ))
  have hjet (T : ℝ) (hT : 0 < T) :
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonReciprocalWindowCompletedEvaluation T hT.le) (rho : ℂ) =
      burnolCoPoissonSubWindowConormalCoefficient T (1 - (rho : ℂ)) lead := by
    rw [iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation hT rho le_rfl]
    dsimp only [burnolCoPoissonSubWindowConormalCoefficient, lead]
    ring
  have hpos : 0 < (1 - (rho : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [(xi_divisor_support_re_mem_open_unit rho).2]
  rw [burnolCoPoissonReciprocalWindowConormalCharacter, hjet (2 * L) (by positivity),
    hjet L hL]
  exact burnolCoPoisson_centered_doubledWindowConormalRatio_eq hL hpos
    (burnolReciprocalWindow_lead_ne_zero rho)

/-- Actual Fourier incidence gives inverse centered characters at the
same original divisor. -/
theorem burnolCoPoissonReciprocalWindowConormalCharacter_eq_inv
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    burnolCoPoissonReciprocalWindowConormalCharacter L hL rho =
      (burnolCoPoissonCompletedWindowConormalCharacter L hL rho)⁻¹ := by
  rw [burnolCoPoissonReciprocalWindowConormalCharacter_eq hL,
    burnolCoPoissonCompletedWindowConormalCharacter_eq hL,
    burnolCoPoissonCenteredConormalCharacter, burnolCoPoissonCenteredConormalCharacter,
    ← Complex.exp_neg]
  congr 1
  ring

/-- The squared-norm difference of the two actual completed source-jet
quotients is the fixed physical Burnol radial defect. -/
theorem burnolCoPoisson_actualFourierWindow_radialDefect_eq
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport)
    (hL : 0 < Real.log (n : ℝ)) :
    ‖burnolCoPoissonCompletedWindowConormalCharacter (Real.log (n : ℝ)) hL rho‖ ^ 2 -
      ‖burnolCoPoissonReciprocalWindowConormalCharacter (Real.log (n : ℝ)) hL rho‖ ^ 2 =
      deningerBurnolActualConormalRadialReflectionDefect n rho := by
  rw [burnolCoPoissonCompletedWindowConormalCharacter_eq hL,
    burnolCoPoissonReciprocalWindowConormalCharacter_eq hL,
    deningerBurnolActualConormalRadialReflectionDefect,
    deningerBurnolActualCenteredConormalCharacter_eq hn,
    deningerBurnolActualCenteredConormalCharacter_eq hn]
  simp only [norm_burnolCoPoissonCenteredConormalCharacter, Complex.sub_re,
    Complex.one_re, xiZeroLineConjEquiv_apply, Complex.conj_re]

/-- The actual Fourier incidence has zero physical radial defect precisely
on the critical line; reciprocal transport alone supplies no annihilation. -/
theorem burnolCoPoisson_actualFourierWindow_radialDefect_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport)
    (hL : 0 < Real.log (n : ℝ)) :
    (‖burnolCoPoissonCompletedWindowConormalCharacter (Real.log (n : ℝ)) hL rho‖ ^ 2 -
      ‖burnolCoPoissonReciprocalWindowConormalCharacter (Real.log (n : ℝ)) hL rho‖ ^ 2 = 0) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [burnolCoPoisson_actualFourierWindow_radialDefect_eq hn rho hL,
    deningerBurnolActualConormalRadialReflectionDefect_eq_zero_iff hn]

/-- The complete incidence reader, at the original prime pair, zero copy
and depth, is the radial difference of the two actual Fourier-related
completed source-jet quotients. The same nonzero incidence witness remains. -/
theorem deningerCofinalRelativeBocksteinIncidence_sourceValue_eq_actualFourierWindow
    (p q : Nat.Primes) (hpq : p ≠ q) (r : XiZeroCopy) (m : ℕ) :
    let hL : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
        p q hpq r (deningerCofinalRelativeBocksteinIncidence p q hpq r m) =
      (((‖burnolCoPoissonCompletedWindowConormalCharacter (Real.log 6) hL r.1‖ ^ 2 -
        ‖burnolCoPoissonReciprocalWindowConormalCharacter (Real.log 6) hL r.1‖ ^ 2 : ℝ) : ℂ)) •
        deningerCalderonWittCrossPrimeGammaWitness hpq := by
  dsimp only
  rw [deningerCofinalRelativeBocksteinIncidence_sourceValue_eq_burnolConormal]
  congr 2
  exact (burnolCoPoisson_actualFourierWindow_radialDefect_eq
    (by norm_num : 2 ≤ 6) r.1 (Real.log_pos (by norm_num))).symm

end

end RHTower
