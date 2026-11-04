import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheArchimedeanKernelOfNearAtoms

/-!
# The common finite part of the near and far Gamma profiles

Integrating the separated singular profile leaves exactly the logarithmic
source moment occurring in the near kernel. Their signed difference cancels
that moment. The far integral has an explicit reciprocal-cutoff error, and
actual cross entries retain their singular profile at every separated width.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis

/-- The far cross entry retains its singular profile, with an error linear in atom width. -/
theorem abs_atomCrossErrorKernel_sub_crossSingular_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {w : ℝ} (hw : 0 < w)
    {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) (hnj : n ≠ j)
    (hws : w < |Real.log j - Real.log n|) :
    |atomCrossErrorKernel (atomDilate φ w) n j -
      crossSingular φ (w / |Real.log j - Real.log n|)| ≤
      (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2)) * w := by
  let s : ℝ := |Real.log j - Real.log n|
  have hs0 : 0 < s := hw.trans hws
  have hsw : 0 < s - w := sub_pos.mpr hws
  have hg := hφ.continuous
  have hgc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  let S : ℝ → ℝ := fun t => 1 / (2 * (s + w * t)) - 1 / (2 * s)
  let R : ℝ → ℝ := fun t =>
    (_root_.RHTower.archLevyDensity (s + w * t) - 1 / (2 * (s + w * t))) -
      (_root_.RHTower.archLevyDensity s - 1 / (2 * s))
  have hpos : ∀ t ∈ Icc (-1 : ℝ) 1, s - w ≤ s + w * t := fun t ht => by
    linarith only [mul_le_mul_of_nonneg_left ht.1 hw.le]
  have hSb : ∀ t ∈ Icc (-1 : ℝ) 1, |S t| ≤ 1 / (2 * (s - w)) + 1 / (2 * s) := by
    intro t ht
    have hp := hpos t ht
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_of_pos (one_div_pos.mpr (by linarith))]
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    · rw [abs_of_pos (one_div_pos.mpr (by linarith))]
  have hRb : ∀ t ∈ Icc (-1 : ℝ) 1, |R t| ≤ 5 / 2 := by
    intro t ht
    have hp := hpos t ht
    exact (abs_sub _ _).trans ((add_le_add
      (abs_archLevyDensity_sub_inv_le (by linarith : 0 < s + w * t))
      (abs_archLevyDensity_sub_inv_le hs0)).trans_eq (by norm_num))
  have hSm : Measurable S :=
    (measurable_const.div (measurable_const.mul (measurable_const.add
      (measurable_const.mul measurable_id)))).sub measurable_const
  have hRm : Measurable R :=
    ((_root_.RHTower.measurable_archLevyDensity.comp (measurable_const.add
      (measurable_const.mul measurable_id))).sub (measurable_const.div (measurable_const.mul
        (measurable_const.add (measurable_const.mul measurable_id))))).sub measurable_const
  have hiS := integrable_bumpAutocorr_mul hg hgc hsupp hSm hSb
  have hiR := integrable_bumpAutocorr_mul hg hgc hsupp hRm hRb
  have hsplit : (∫ t, bumpAutocorr φ t * (_root_.RHTower.archLevyDensity (s + w * t) -
      _root_.RHTower.archLevyDensity s)) =
      (∫ t, bumpAutocorr φ t * S t) + ∫ t, bumpAutocorr φ t * R t := by
    rw [← integral_add hiS hiR]
    congr 1
    funext t
    dsimp only [S, R]
    ring
  have hsing : w / (∫ u, φ u ^ 2) * (∫ t, bumpAutocorr φ t * S t) =
      crossSingular φ (w / s) := by
    unfold crossSingular
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1
    funext t
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · have hp := hpos t ht
      have hp0 : s + w * t ≠ 0 := by linarith
      dsimp only [S]
      field_simp [hp0, hs0.ne', hM.ne']
    · have hzero : bumpAutocorr φ t = 0 := bumpAutocorr_profile_eq_zero hsupp (by
        by_contra h
        exact ht (abs_le.mp (not_lt.mp h)))
      rw [hzero]
      ring
  rw [atomCrossErrorKernel_atomDilate_eq hφ hsupp hM hw hn hj hnj hws]
  change |w / (∫ u, φ u ^ 2) *
    (∫ t, bumpAutocorr φ t * (_root_.RHTower.archLevyDensity (s + w * t) -
      _root_.RHTower.archLevyDensity s)) - crossSingular φ (w / s)| ≤ _
  rw [hsplit, mul_add, hsing, add_sub_cancel_left, abs_mul, abs_of_pos (div_pos hw hM)]
  exact (mul_le_mul_of_nonneg_left
    (abs_integral_bumpAutocorr_mul_le hg hgc hsupp hRm hRb) (div_pos hw hM).le).trans_eq (by ring)

private theorem crossSingular_inv_eq_interval {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) {s : ℝ} (hs : 2 ≤ s) :
    crossSingular φ (1 / s) = (1 / (2 * ∫ u, φ u ^ 2)) *
      ∫ t in (-1 : ℝ)..1, shellAutocorr φ t * ((s + t)⁻¹ - s⁻¹) := by
  have hs0 : s ≠ 0 := by linarith
  unfold crossSingular
  congr 1
  have hrestrict : (∫ t, shellAutocorr φ t * (1 / s / (1 + 1 / s * t) - 1 / s)) =
      ∫ t in (-1 : ℝ)..1, shellAutocorr φ t * (1 / s / (1 + 1 / s * t) - 1 / s) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hg : shellAutocorr φ t = 0 := shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (by
      by_contra h
      push Not at h
      exact ht ⟨by linarith [(abs_lt.mp h).1], (abs_lt.mp h).2.le⟩)
    rw [hg, zero_mul]
  change (∫ t, shellAutocorr φ t * (1 / s / (1 + 1 / s * t) - 1 / s)) = _
  rw [hrestrict]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num)] at ht
  have hst : s + t ≠ 0 := by linarith [ht.1]
  have hden : 1 + 1 / s * t = (s + t) / s := by field_simp [hs0]
  change shellAutocorr φ t * (1 / s / (1 + 1 / s * t) - 1 / s) =
    shellAutocorr φ t * ((s + t)⁻¹ - s⁻¹)
  rw [hden]
  field_simp [hs0, hst]

private theorem integral_reciprocal_difference {T t : ℝ} (hT : 2 ≤ T)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    (∫ s in (2 : ℝ)..T, ((s + t)⁻¹ - s⁻¹)) =
      (Real.log (T + t) - Real.log T) + Real.log 2 - Real.log (2 + t) := by
  have hi : IntervalIntegrable (fun s : ℝ => (s + t)⁻¹) volume 2 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact (continuous_id.add_const t).continuousOn.inv₀ fun s hs => by
      change s + t ≠ 0
      linarith [hs.1, ht.1]
  have hj : IntervalIntegrable (fun s : ℝ => s⁻¹) volume 2 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact continuousOn_id.inv₀ fun s hs => by
      change s ≠ 0
      linarith [hs.1]
  rw [intervalIntegral.integral_sub hi hj,
    intervalIntegral.integral_comp_add_right (fun s : ℝ => s⁻¹) t,
    integral_inv_of_pos (by linarith [ht.1]) (by linarith [ht.1]),
    integral_inv_of_pos (by norm_num) (by linarith),
    Real.log_div (by linarith [ht.1]) (by linarith [ht.1]),
    Real.log_div (by linarith) (by norm_num)]
  ring

private theorem integral_crossSingular_inv_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) {T : ℝ} (hT : 2 ≤ T) :
    (∫ s in (2 : ℝ)..T, crossSingular φ (1 / s)) =
      (1 / (2 * ∫ u, φ u ^ 2)) * ∫ t in (-1 : ℝ)..1,
        shellAutocorr φ t *
          ((Real.log (T + t) - Real.log T) + Real.log 2 - Real.log (2 + t)) := by
  let F : ℝ → ℝ → ℝ := fun s t => shellAutocorr φ t * ((s + t)⁻¹ - s⁻¹)
  have hc : ContinuousOn (Function.uncurry F) (Icc (2 : ℝ) T ×ˢ Icc (-1 : ℝ) 1) := by
    have hg : Continuous (fun p : ℝ × ℝ => shellAutocorr φ p.2) :=
      (continuous_shellAutocorr hφ hsupp).comp continuous_snd
    apply hg.continuousOn.mul
    apply ContinuousOn.sub
    · exact (continuous_fst.add continuous_snd).continuousOn.inv₀ fun p hp => by
        change p.1 + p.2 ≠ 0
        linarith [hp.1.1, hp.2.1]
    · exact continuous_fst.continuousOn.inv₀ fun p hp => by linarith [hp.1.1]
  have hi : IntegrableOn (Function.uncurry F) (uIoc (2 : ℝ) T ×ˢ uIoc (-1 : ℝ) 1) := by
    rw [uIoc_of_le hT, uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hc).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have heq : (∫ s in (2 : ℝ)..T, crossSingular φ (1 / s)) =
      (1 / (2 * ∫ u, φ u ^ 2)) * ∫ s in (2 : ℝ)..T, ∫ t in (-1 : ℝ)..1, F s t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    exact crossSingular_inv_eq_interval hφ hsupp hs.1
  rw [heq, intervalIntegral_intervalIntegral_swap hi]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num)] at ht
  dsimp only [F]
  rw [intervalIntegral.integral_const_mul, integral_reciprocal_difference hT ht]

private theorem abs_log_shift_difference_le {T t : ℝ} (hT : 2 ≤ T)
    (ht : t ∈ Icc (-1 : ℝ) 1) : |Real.log (T + t) - Real.log T| ≤ 2 / T := by
  have hT0 : 0 < T := by linarith
  have hTt : 0 < T + t := by linarith [ht.1]
  have hp := Real.log_le_sub_one_of_pos (div_pos hTt hT0)
  have hm := Real.log_le_sub_one_of_pos (div_pos hT0 hTt)
  rw [Real.log_div hTt.ne' hT0.ne'] at hp
  rw [Real.log_div hT0.ne' hTt.ne'] at hm
  have ep : (T + t) / T - 1 = t / T := by field_simp [hT0.ne']; ring
  have em : T / (T + t) - 1 = -t / (T + t) := by field_simp [hTt.ne']; ring
  rw [ep] at hp
  rw [em] at hm
  apply abs_le.mpr
  constructor
  · have hd : T / 2 ≤ T + t := by linarith [ht.1]
    have hfrac : -t / (T + t) ≤ 2 / T := by
      calc
        _ ≤ 1 / (T / 2) := div_le_div₀ zero_le_one (by linarith [ht.1]) (half_pos hT0) hd
        _ = _ := by ring
    linarith only [hm, hfrac]
  · exact hp.trans (div_le_div_of_nonneg_right (by linarith [ht.2]) hT0.le)

/-- The convergent far-cross integral, expressed in the source autocorrelation. -/
def farCrossFinitePart (φ : ℝ → ℝ) : ℝ :=
  ((∫ u, φ u) ^ 2 * Real.log 2 -
    ∫ t in (-1 : ℝ)..1, shellAutocorr φ t * Real.log (2 + t)) / (2 * ∫ u, φ u ^ 2)

theorem abs_integral_crossSingular_inv_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {T : ℝ} (hT : 2 ≤ T) :
    |(∫ s in (2 : ℝ)..T, crossSingular φ (1 / s)) - farCrossFinitePart φ| ≤ 2 / T := by
  have hT0 : 0 < T := by linarith
  have hG := continuous_shellAutocorr hφ hsupp
  have hlogT : ContinuousOn (fun t : ℝ => Real.log (T + t) - Real.log T) (Icc (-1 : ℝ) 1) :=
    ((continuous_const.add continuous_id).continuousOn.log fun t ht => by
      change T + t ≠ 0
      linarith [ht.1]).sub continuousOn_const
  have hlog2 : ContinuousOn (fun t : ℝ => Real.log (2 + t)) (Icc (-1 : ℝ) 1) :=
    (continuous_const.add continuous_id).continuousOn.log fun t ht => by
      change 2 + t ≠ 0
      linarith [ht.1]
  have hI1 : IntervalIntegrable (fun t => shellAutocorr φ t *
      (Real.log (T + t) - Real.log T)) volume (-1) 1 :=
    (hG.continuousOn.mul hlogT).intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1)
  have hI2 : IntervalIntegrable (fun t => shellAutocorr φ t * Real.log 2) volume (-1) 1 :=
    (hG.mul_const (Real.log 2)).intervalIntegrable (-1) 1
  have hI3 : IntervalIntegrable (fun t => shellAutocorr φ t * Real.log (2 + t)) volume (-1) 1 :=
    (hG.continuousOn.mul hlog2).intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1)
  have heq : (∫ s in (2 : ℝ)..T, crossSingular φ (1 / s)) - farCrossFinitePart φ =
      (∫ t in (-1 : ℝ)..1, shellAutocorr φ t * (Real.log (T + t) - Real.log T)) /
        (2 * ∫ u, φ u ^ 2) := by
    rw [integral_crossSingular_inv_eq hφ hsupp hT]
    have hsplit : (∫ t in (-1 : ℝ)..1, shellAutocorr φ t *
        ((Real.log (T + t) - Real.log T) + Real.log 2 - Real.log (2 + t))) =
        (∫ t in (-1 : ℝ)..1, shellAutocorr φ t * (Real.log (T + t) - Real.log T)) +
          (∫ u, φ u) ^ 2 * Real.log 2 -
          ∫ t in (-1 : ℝ)..1, shellAutocorr φ t * Real.log (2 + t) := by
      simp_rw [mul_sub, mul_add]
      rw [intervalIntegral.integral_sub (hI1.add hI2) hI3,
        intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_mul_const,
        integral_shellAutocorr_neg_one_one hφ hsupp]
      simp only [mul_sub]
    rw [hsplit]
    unfold farCrossFinitePart
    ring
  rw [heq, abs_div, abs_of_pos (mul_pos (by norm_num) hM), div_le_iff₀ (by positivity)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 1) (C := (∫ u, φ u ^ 2) * (2 / T)) (fun t ht => by
      rw [uIoc_of_le (by norm_num)] at ht
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_shellAutocorr_le' hφ hsupp t)
        (abs_log_shift_difference_le hT ⟨ht.1.le, ht.2⟩) (abs_nonneg _) hM.le)
  rw [Real.norm_eq_abs] at hb
  norm_num at hb
  nlinarith only [hb]

theorem tendsto_joint_near_far_Gamma_integral {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    Tendsto (fun T : ℝ => (2 / (∫ u, φ u ^ 2)) * (∫ s in (0 : ℝ)..2, nearKernel φ s) -
      2 * ∫ s in (2 : ℝ)..T, crossSingular φ (1 / s)) atTop
      (𝓝 (-((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant))) := by
  have hz : Tendsto (fun T : ℝ => (∫ s in (2 : ℝ)..T, crossSingular φ (1 / s)) -
      farCrossFinitePart φ) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ => 2 / T) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs] using abs_integral_crossSingular_inv_sub_le hφ hsupp hM hT
  have hf : Tendsto (fun T : ℝ => ∫ s in (2 : ℝ)..T, crossSingular φ (1 / s))
      atTop (𝓝 (farCrossFinitePart φ)) := by
    simpa only [zero_add, sub_add_cancel] using hz.add_const (farCrossFinitePart φ)
  have h := (tendsto_const_nhds (x := (2 / (∫ u, φ u ^ 2)) *
    (∫ s in (0 : ℝ)..2, nearKernel φ s))).sub (hf.const_mul 2)
  have heq : (2 / (∫ u, φ u ^ 2)) * (∫ s in (0 : ℝ)..2, nearKernel φ s) -
      2 * farCrossFinitePart φ = -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) := by
    rw [integral_nearKernel hφ hsupp, nearConstant_eq]
    have hl : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * Real.pi ≠ 0)]
      congr 1
      ring
    rw [hl]
    unfold farCrossFinitePart
    ring
  exact heq ▸ h

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_joint_near_far_Gamma_integral
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_atomCrossErrorKernel_sub_crossSingular_le
