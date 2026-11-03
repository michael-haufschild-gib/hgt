import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicLagGap

/-!
# The exterior term of the regional logarithmic energy

The logarithmic lag count is the regional energy plus an exact exterior
potential. Keeping the logarithmic boundary term preserves the spatial weight
needed when low odd moments and prime reflection are charged together.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.LatticeSectionTheory

private theorem exterior_and_reflected_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ Real.log 2 - Real.log (1 - x ^ 2) / 2 ∧
      0 ≤ Real.log (x + 1) - Real.log x := by
  have hx2 : x ^ 2 < 1 := by nlinarith only [hx.1, hx.2]
  have hl : Real.log (1 - x ^ 2) ≤ 0 := by
    have h := Real.log_le_log (show 0 < 1 - x ^ 2 by linarith only [hx2])
      (show 1 - x ^ 2 ≤ 1 by nlinarith only [sq_nonneg x])
    simpa only [Real.log_one] using h
  exact ⟨by linarith only [hl, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)],
    sub_nonneg.mpr (Real.log_le_log hx.1 (by linarith only []))⟩

private theorem logarithmic_lag_eq_regional_exterior_of_lipschitz {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hs : ∀ x, 1 ≤ |x| → F x = 0) (ho : ∀ x, F (-x) = -F x) :
    IntegrableOn (fun x => F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2))
      (Ioo (0 : ℝ) 1) ∧
    (∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t) / 2 =
      regionalLogEnergy F / 4 +
        ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2) := by
  have hFc : Continuous F := hF.continuous
  have hF0 : F 0 = 0 := by
    have h := ho 0
    simp only [neg_zero] at h
    linarith only [h]
  have hKill := oddLogKilling_integrable hF.continuous hF0 (hs 1 (by norm_num))
    (fun x _ y _ => hFL x y)
  have hExt : IntegrableOn
      (fun x => F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2)) (Ioo (0 : ℝ) 1) := by
    have hm : Measurable (fun x => F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2)) := by
      fun_prop
    refine hKill.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    obtain ⟨hE, hR⟩ := exterior_and_reflected_nonneg hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hE)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg (F x))
    unfold oddLogKilling
    linarith only [hR]
  have hRef : IntegrableOn
      (fun x => F x ^ 2 * (Real.log (x + 1) - Real.log x)) (Ioo (0 : ℝ) 1) := by
    refine hKill.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    obtain ⟨hE, hR⟩ := exterior_and_reflected_nonneg hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hR)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg (F x))
    unfold oddLogKilling
    linarith only [hE]
  have hsplit : (∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * oddLogKilling x) =
      (∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2)) +
      ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log (x + 1) - Real.log x) := by
    rw [← integral_add hExt hRef]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    unfold oddLogKilling
    ring
  have hlag := logarithmic_pair_eq_lag hF.continuous hFL hs
  have hpair := logarithmic_pair_eq_folded_count hF.continuous hFL hs ho
  have hregional := regionalLogEnergy_eq_odd_principal hF hFL ho
  rw [hsplit] at hpair
  refine ⟨hExt, ?_⟩
  linarith only [hlag, hpair, hregional]

private theorem odd_supported_vanish {F : ℝ → ℝ} {a : ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-a) a) (ho : ∀ x, F (-x) = -F x) :
    ∀ x, a ≤ |x| → F x = 0 := by
  have hz : Ioi a ⊆ {x | F x = 0} := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport fun h => not_le_of_gt hx (hs h).2
  have hzr : ∀ x, a ≤ x → F x = 0 := by
    have h := closure_minimal hz (isClosed_eq hF continuous_const)
    rw [closure_Ioi] at h
    exact fun x hx => h hx
  intro x hx
  rcases le_total 0 x with hx0 | hx0
  · exact hzr x (by rwa [abs_of_nonneg hx0] at hx)
  · have h := hzr (-x) (by rwa [abs_of_nonpos hx0] at hx)
    rw [ho] at h
    exact neg_eq_zero.mp h

/-- The normalized odd lag energy includes the full logarithmic exterior potential. -/
theorem odd_logarithmic_lag_eq_regional_exterior {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-1 : ℝ) 1) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t) / 2 =
      regionalLogEnergy F / 4 +
        ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2) := by
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)))
  obtain ⟨K, hK⟩ := _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz hF hcs
  have hFL : ∀ x y, |F x - F y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    simpa only [Real.dist_eq] using hK.dist_le_mul x y
  exact (logarithmic_lag_eq_regional_exterior_of_lipschitz (hF.of_le (by norm_num))
    hFL (odd_supported_vanish hF.continuous hs ho) ho).2

private theorem autocorr_half (F : ℝ → ℝ) (t : ℝ) :
    autocorr (fun x => F ((1 / 2) * x)) t = 2 * autocorr F ((1 / 2) * t) := by
  unfold autocorr
  have h := Measure.integral_comp_mul_left (fun x => F x * F (x + (1 / 2) * t)) (1 / 2 : ℝ)
  norm_num [smul_eq_mul] at h
  simpa only [mul_add] using h

/-- The exterior potential is integrable and retained exactly after unit-window dilation. -/
theorem unit_odd_logarithmic_lag_and_exterior {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    IntegrableOn (fun x => F ((1 / 2) * x) ^ 2 *
      (Real.log 2 - Real.log (1 - x ^ 2) / 2)) (Ioo (0 : ℝ) 1) ∧
    (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) =
      regionalLogEnergy (fun x => F ((1 / 2) * x)) / 4 +
        ∫ x in Ioo (0 : ℝ) 1,
          F ((1 / 2) * x) ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2) := by
  let U : ℝ → ℝ := fun x => F ((1 / 2) * x)
  have hU : ContDiff ℝ 1 U := (hF.of_le (by norm_num)).comp
    (contDiff_const.mul contDiff_id)
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)))
  obtain ⟨K, hK⟩ := _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz hF hcs
  have hFL : ∀ x y, |F x - F y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    simpa only [Real.dist_eq] using hK.dist_le_mul x y
  have hUL : ∀ x y, |U x - U y| ≤ ((K : ℝ) / 2) * |x - y| := by
    intro x y
    have h := hFL ((1 / 2) * x) ((1 / 2) * y)
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    dsimp [U]
    linarith only [h]
  have hUs : ∀ x, 1 ≤ |x| → U x = 0 := by
    intro x hx
    apply odd_supported_vanish hF.continuous hs ho
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith only [hx]
  have hUo : ∀ x, U (-x) = -U x := by intro x; dsimp [U]; rw [mul_neg, ho]
  have h := logarithmic_lag_eq_regional_exterior_of_lipschitz
    hU hUL hUs hUo
  have he (t : ℝ) : (autocorr U 0 - autocorr U t) / t =
      (autocorr F 0 - autocorr F ((1 / 2) * t)) / ((1 / 2) * t) := by
    dsimp [U]
    rw [autocorr_half F 0, autocorr_half F t, mul_zero]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hscale := intervalIntegral.integral_comp_mul_left
    (fun t => (autocorr F 0 - autocorr F t) / t) (a := 0) (b := 2)
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  norm_num [smul_eq_mul] at hscale
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hscale
  have hid := h.2
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t _ => he t),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hid
  rw [hscale] at hid
  refine ⟨h.1, ?_⟩
  convert hid using 1
  ring

/-- On the unit support window, dilation leaves the regional energy divided by four. -/
theorem unit_odd_logarithmic_lag_eq_regional_exterior {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) =
      regionalLogEnergy (fun x => F ((1 / 2) * x)) / 4 +
        ∫ x in Ioo (0 : ℝ) 1,
          F ((1 / 2) * x) ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2) :=
  (unit_odd_logarithmic_lag_and_exterior hF hs ho).2

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.odd_logarithmic_lag_eq_regional_exterior
#print axioms GaloisForLFunctions.LatticeSectionTheory.unit_odd_logarithmic_lag_eq_regional_exterior
