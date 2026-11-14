import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstOddMomentIsPaidAtAperture1881Over5000
import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldRetainsTwoMomentCharges
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicFirstOddMoment

/-!
# The odd Weil floor at aperture `1881/5000`

Dilation identifies the prime-two correlation with a reflected strip. The
regional logarithmic gap leaves one position charge; the exterior potential
and the Gamma reserve dominate its polynomial comparison. The resulting
capacity estimate retains a uniform floor `1/2000` for the actual Weil form.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory SpacingScaleHarmonicAnalysis SelectivePositivityAndThresholdLaws
open ArithmeticIncidencePositivity ArithmeticCriticalityTheory BiScaleUncertainty

private abbrev aperture : ℝ := 1881 / 5000

private theorem momentMassCost_upper : firstFoldMomentMassCost ≤ (173 / 100 : ℝ) := by
  have hp : (3 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d6]
  have hp2 : (9 : ℝ) ≤ Real.pi ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hp 2
    norm_num at h
    exact h
  have hi : 1 / (96 * Real.pi ^ 2) ≤ (1 / 864 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 96 * Real.pi ^ 2)).mpr
    linarith only [hp2]
  have hlu : Real.log Real.pi ≤ Real.log 3 + Real.pi / 3 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.pi / 3 by positivity)
    rw [Real.log_div Real.pi_ne_zero (by norm_num)] at h
    linarith only [h]
  have hgu := _root_.RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  unfold firstFoldMomentMassCost
  linarith only [hlu, hgu, hi, Real.log_three_lt_d9, Real.pi_lt_d4]

private theorem logarithmic_mass_reserve :
    (31 / 80 : ℝ) ≤ 11 / 6 - firstFoldMomentMassCost - Real.log (2 * aperture) := by
  have hl : Real.log (2 * aperture) ≤ Real.log 3 - 2 * Real.log 2 + 2 / 625 := by
    have he : 2 * aperture = (3 / 4 : ℝ) * (1 + 2 / 625) := by norm_num [aperture]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 2 / 625)
    have hbase : Real.log (3 / 4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [he, Real.log_mul (by norm_num) (by norm_num), hbase]
    linarith only [h]
  linarith only [hl, momentMassCost_upper, Real.log_three_lt_d9, Real.log_two_gt_d9]

private theorem first_moment_charge_upper :
    (5 / 2 : ℝ) + (39 / 32) * aperture ^ 3 ≤ 77 / 30 := by norm_num [aperture]

private theorem dilated_outside {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-aperture) aperture) {x : ℝ}
    (hx : x ∉ Icc (-1 : ℝ) 1) : F (aperture * x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hi := hs ht
  apply hx
  dsimp [aperture] at hi
  exact ⟨by linarith only [hi.1], by linarith only [hi.2]⟩

private theorem dilated_support {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-aperture) aperture) :
    tsupport (fun x => F (aperture * x)) ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  exact hx (dilated_outside hs hn)

private theorem even_integral_unit {H : ℝ → ℝ} (hH : Continuous H)
    (he : ∀ x, H (-x) = H x) :
    (∫ x in Icc (-1 : ℝ) 1, H x) = 2 * ∫ x in (0 : ℝ)..1, H x := by
  have hn := intervalIntegral.integral_comp_neg (f := H) (a := (0 : ℝ)) (b := 1)
  simp only [he, neg_zero] at hn
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hH.intervalIntegrable (-1) 0) (hH.intervalIntegrable 0 1)
  rw [← hn, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  linarith only [h]

private theorem dilated_mass {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-aperture) aperture) (ho : ∀ x, F (-x) = -F x) :
    (∫ x, F x ^ 2) = 2 * aperture * ∫ u in (0 : ℝ)..1, F (aperture * u) ^ 2 := by
  have hc : Continuous (fun u => F (aperture * u)) :=
    hF.comp (continuous_const.mul continuous_id)
  have hcut : (∫ u in Icc (-1 : ℝ) 1, F (aperture * u) ^ 2) =
      ∫ u, F (aperture * u) ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [dilated_outside hs hu, zero_pow two_ne_zero])
  have he := even_integral_unit (H := fun u => F (aperture * u) ^ 2)
    (hc.pow 2) (fun u => by rw [mul_neg, ho, neg_sq])
  have hscale := Measure.integral_comp_mul_left (fun x => F x ^ 2) aperture
  norm_num [aperture, smul_eq_mul] at hscale
  rw [hcut, hscale] at he
  dsimp [aperture]
  linarith only [he]

private theorem dilated_position {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-aperture) aperture) (ho : ∀ x, F (-x) = -F x) :
    (∫ x, x * F x) = 2 * aperture ^ 2 * ∫ u in (0 : ℝ)..1, u * F (aperture * u) := by
  have hc : Continuous (fun u => F (aperture * u)) :=
    hF.comp (continuous_const.mul continuous_id)
  have hcut : (∫ u in Icc (-1 : ℝ) 1, u * F (aperture * u)) =
      ∫ u, u * F (aperture * u) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [dilated_outside hs hu, mul_zero])
  have he := even_integral_unit (H := fun u => u * F (aperture * u))
    (continuous_id.mul hc) (fun u => by rw [mul_neg, ho, neg_mul_neg])
  have hscale := Measure.integral_comp_mul_left (fun x => x * F x) aperture
  have hfun : (fun u => (aperture * u) * F (aperture * u)) =
      fun u => aperture * (u * F (aperture * u)) := by funext u; ring
  rw [hfun, integral_const_mul] at hscale
  rw [hcut] at he
  norm_num [aperture, smul_eq_mul] at hscale
  dsimp [aperture] at he ⊢
  linarith only [he, hscale]

private theorem dilated_autocorr (F : ℝ → ℝ) (t : ℝ) :
    autocorr (fun x => F (aperture * x)) t = aperture⁻¹ * autocorr F (aperture * t) := by
  unfold autocorr
  have h := Measure.integral_comp_mul_left (fun x => F x * F (x + aperture * t)) aperture
  rw [abs_of_pos (by norm_num [aperture] : 0 < aperture⁻¹), smul_eq_mul] at h
  simpa only [mul_add] using h

private theorem logarithmic_lag_integrable {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) :
    IntegrableOn (fun t => (autocorr F 0 - autocorr F t) / t) (Ioc (0 : ℝ) 1) := by
  have hi := integrableOn_biScaleLevyIntegrand hF hcs
  have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ ht => ht.1
  apply (hi.mono_set hsub).mono'
    (((continuous_const.sub hc).measurable.div measurable_id).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hd := autocorr_sub_nonneg hcs hF.continuous t
  have hw : 1 / t ≤ archLevySinhWeight t := by
    apply le_of_mul_le_mul_left (a := t) _ ht.1
    rw [archLevySinhWeight, exp_half_div_sinh_eq ht.1]
    have hk := mul_archLevyDensity_ge_sharp ht.1 ht.2
    have ht2 : t ^ 2 ≤ t := by nlinarith only [ht.1, ht.2]
    have ht3 : t ^ 3 ≤ t := by
      have h := mul_nonneg ht.1.le (show 0 ≤ 1 - t ^ 2 by nlinarith only [ht2, ht.2])
      nlinarith only [h]
    have he : t * (1 / t) = 1 := by field_simp [ht.1.ne']
    rw [he]
    nlinarith only [hk, ht2, ht3, ht.1]
  change ‖(autocorr F 0 - autocorr F t) / t‖ ≤
    (autocorr F 0 - autocorr F t) * archLevySinhWeight t
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hd ht.1.le)]
  simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hw hd

private theorem lag_cutoff {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-aperture) aperture) :
    (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) =
      (∫ t in Ioc (0 : ℝ) (2 * aperture), (autocorr F 0 - autocorr F t) / t) -
        Real.log (2 * aperture) * autocorr F 0 := by
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport fun ht => hx (hs ht))
  have hi := logarithmic_lag_integrable hF hcs
  have hi1 : IntervalIntegrable (fun t => (autocorr F 0 - autocorr F t) / t)
      volume 0 (2 * aperture) := by
    constructor
    · exact hi.mono_set (fun t ht => ⟨ht.1, ht.2.trans (by norm_num [aperture])⟩)
    · rw [Ioc_eq_empty_of_le (by norm_num [aperture] : (0 : ℝ) ≤ 2 * aperture)]
      simp
  have hi2 : IntervalIntegrable (fun t => (autocorr F 0 - autocorr F t) / t)
      volume (2 * aperture) 1 := by
    constructor
    · exact hi.mono_set (fun t ht => ⟨lt_trans (by norm_num [aperture]) ht.1, ht.2⟩)
    · rw [Ioc_eq_empty_of_le (by norm_num [aperture] : 2 * aperture ≤ 1)]
      simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have htail : (∫ t in (2 * aperture)..1, (autocorr F 0 - autocorr F t) / t) =
      -Real.log (2 * aperture) * autocorr F 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num [aperture] : 2 * aperture ≤ 1)]
    have he : ∀ t ∈ Ioc (2 * aperture) 1,
        (autocorr F 0 - autocorr F t) / t = autocorr F 0 * t⁻¹ := by
      intro t ht
      rw [autocorr_eq_zero_of_support (x := t) hs ht.1, sub_zero, div_eq_mul_inv]
    rw [setIntegral_congr_fun measurableSet_Ioc he, integral_const_mul,
      ← intervalIntegral.integral_of_le (by norm_num [aperture] : 2 * aperture ≤ 1),
      integral_inv_of_pos (by norm_num [aperture]) (by norm_num), one_div, Real.log_inv]
    ring
  rw [htail, intervalIntegral.integral_of_le (by norm_num [aperture] : (0 : ℝ) ≤ 2 * aperture),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hadd
  linarith only [hadd]

private theorem dilated_lag (F : ℝ → ℝ) :
    (∫ t in Ioc (0 : ℝ) 2,
      (autocorr (fun x => F (aperture * x)) 0 - autocorr (fun x => F (aperture * x)) t) / t) =
      aperture⁻¹ * ∫ t in Ioc (0 : ℝ) (2 * aperture), (autocorr F 0 - autocorr F t) / t := by
  have he (t : ℝ) :
      (autocorr (fun x => F (aperture * x)) 0 - autocorr (fun x => F (aperture * x)) t) / t =
        (autocorr F 0 - autocorr F (aperture * t)) / (aperture * t) := by
    rw [dilated_autocorr F 0, dilated_autocorr F t, mul_zero]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t _ => he t),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  have h := intervalIntegral.integral_comp_mul_left
    (fun t => (autocorr F 0 - autocorr F t) / t) (a := 0) (b := 2)
    (by norm_num [aperture] : aperture ≠ 0)
  rw [smul_eq_mul, mul_zero, mul_comm aperture 2,
    intervalIntegral.integral_of_le (by norm_num [aperture] : (0 : ℝ) ≤ 2 * aperture)] at h
  exact h

private theorem exterior_integrable {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (ho : ∀ x, G (-x) = -G x) :
    IntegrableOn (fun x => G x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2))
      (Ioo (0 : ℝ) 1) := by
  let H := fun x => G (2 * x)
  have hH : ContDiff ℝ 2 H := hG.comp (contDiff_const.mul contDiff_id)
  have hHs : tsupport H ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    apply hx
    change G (2 * x) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    have hi := hs ht
    exact hn ⟨by linarith only [hi.1], by linarith only [hi.2]⟩
  have hHo (x : ℝ) : H (-x) = -H x := by dsimp [H]; rw [mul_neg, ho]
  have h := (unit_odd_logarithmic_lag_and_exterior hH hHs hHo).1
  simpa only [H, ← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul] using h

private theorem dilated_prime_reflection {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-aperture) aperture) (ho : ∀ x, F (-x) = -F x) :
    -2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) =
      2 * aperture * (Real.log 2 / Real.sqrt 2) *
        ∫ u in firstOverlapOddStripLeft..1,
          F (aperture * u) * F (aperture * (firstOverlapOddStripLeft + 1 - u)) := by
  let G : ℝ → ℝ := fun u => F (aperture * u)
  let d : ℝ := Real.log 2 / aperture
  have hGo (x : ℝ) : G (-x) = -G x := by dsimp [G]; rw [mul_neg, ho]
  have hcut : (∫ u in Icc (d - 1) 1, G u * G (d - u)) = ∫ u, G u * G (d - u) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    by_cases hright : 1 < u
    · have hz : G u = 0 := dilated_outside hs (fun h => not_lt_of_ge h.2 hright)
      rw [hz, zero_mul]
    · have hleft : u < d - 1 := lt_of_not_ge (fun h => hu ⟨h, le_of_not_gt hright⟩)
      have hz : G (d - u) = 0 := dilated_outside hs (fun h => by linarith only [h.2, hleft])
      rw [hz, mul_zero]
  have hn := integral_neg_eq_self (fun u => G u * G (u + d)) volume
  have hfun : (fun u => G (-u) * G (-u + d)) = fun u => -(G u * G (d - u)) := by
    funext u
    rw [hGo, show -u + d = d - u by ring]
    ring
  rw [hfun, integral_neg, ← hcut] at hn
  change -(∫ u in Icc (d - 1) 1, G u * G (d - u)) = autocorr G d at hn
  have hscale := dilated_autocorr F d
  change autocorr G d = aperture⁻¹ * autocorr F (aperture * d) at hscale
  rw [show aperture * d = Real.log 2 by dsimp [d, aperture]; ring] at hscale
  rw [hscale] at hn
  have hbound : firstOverlapOddStripLeft ≤ 1 := by
    unfold firstOverlapOddStripLeft
    linarith only [Real.log_two_lt_d9]
  rw [intervalIntegral.integral_of_le hbound, ← integral_Icc_eq_integral_Ioc]
  change -2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) =
    2 * aperture * (Real.log 2 / Real.sqrt 2) *
      ∫ u in Icc (d - 1) 1, G u * G (d - 1 + 1 - u)
  simp only [sub_add_cancel]
  have hw := congrArg (fun z : ℝ => (Real.log 2 / Real.sqrt 2) * z) hn
  dsimp [aperture] at hw ⊢
  nlinarith only [hw]

private theorem potential_integral_bound {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (hs : tsupport G ⊆ Icc (-1 : ℝ) 1) (ho : ∀ x, G (-x) = -G x) :
    (∫ u in (0 : ℝ)..1, firstOverlapOddPotential u * G u ^ 2) ≤
      (11 / 6 - firstFoldMomentMassCost - Real.log (2 * aperture) - Real.log 2) *
        (∫ u in (0 : ℝ)..1, G u ^ 2) +
      ∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by
  have hExt := exterior_integrable hG hs ho
  have hiM : IntegrableOn (fun u => G u ^ 2) (Ioo (0 : ℝ) 1) :=
    (hG.continuous.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiP : IntegrableOn (fun u => firstOverlapOddPotential u * G u ^ 2) (Ioo (0 : ℝ) 1) :=
    (show Continuous (fun u => firstOverlapOddPotential u * G u ^ 2) by fun_prop).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  let c := 11 / 6 - firstFoldMomentMassCost - Real.log (2 * aperture) - Real.log 2
  have hcomp : (∫ u in Ioo (0 : ℝ) 1, firstOverlapOddPotential u * G u ^ 2) ≤
      ∫ u in Ioo (0 : ℝ) 1,
        c * G u ^ 2 + G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by
    apply setIntegral_mono_on hiP ((hiM.const_mul c).add hExt) measurableSet_Ioo
    intro u hu
    have hp := firstOverlapOddPotential_le_log hu.1.le hu.2
    have hb : firstOverlapOddPotential u ≤ c + Real.log 2 - Real.log (1 - u ^ 2) / 2 := by
      dsimp [c]
      linarith only [hp, logarithmic_mass_reserve]
    have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (G u))
    change firstOverlapOddPotential u * G u ^ 2 ≤
      c * G u ^ 2 + G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2)
    nlinarith only [hm]
  rw [integral_add (hiM.const_mul c) hExt, integral_const_mul] at hcomp
  simpa only [c, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using hcomp

private theorem weil_comparison {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-aperture) aperture) (ho : ∀ x, F (-x) = -F x) :
    2 * aperture * (firstOverlapOddEnergy (fun u => F (aperture * u)) -
      (77 / 30) * (∫ u in (0 : ℝ)..1, u * F (aperture * u)) ^ 2) ≤ weilQuad F := by
  let G := fun u => F (aperture * u)
  have hG : ContDiff ℝ 2 G := hF.comp (contDiff_const.mul contDiff_id)
  have hGs : tsupport G ⊆ Icc (-1 : ℝ) 1 := dilated_support hs
  have hGo (u : ℝ) : G (-u) = -G u := by dsimp [G]; rw [mul_neg, ho]
  have hsunit : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro x hx
    have hi := hs hx
    dsimp [aperture] at hi
    exact ⟨by linarith only [hi.1], by linarith only [hi.2]⟩
  have hMass := dilated_mass hF.continuous hs ho
  have hPos := dilated_position hF.continuous hs ho
  change (∫ x, F x ^ 2) = 2 * aperture * (∫ u in (0 : ℝ)..1, G u ^ 2) at hMass
  change (∫ x, x * F x) = 2 * aperture ^ 2 * (∫ u in (0 : ℝ)..1, u * G u) at hPos
  have hM := even_integral_unit (H := fun u => G u ^ 2)
    (hG.continuous.pow 2) (fun u => by rw [hGo, neg_sq])
  have hM1 : regionalLegendreMoment G 1 = 2 * ∫ u in (0 : ℝ)..1, u * G u := by
    have h := even_integral_unit (H := fun u => u * G u) (continuous_id.mul hG.continuous)
      (fun u => by rw [hGo, neg_mul_neg])
    simpa only [regionalLegendreMoment, legP_one, mul_comm] using h
  have hGap := regionalLogEnergy_ge_third_gap_sub_first_odd_moment
    (hG.of_le (by norm_num)) hGo
  rw [hM, hM1] at hGap
  have hLag := odd_logarithmic_lag_eq_regional_exterior hG hGs hGo
  have hScale := dilated_lag F
  change (∫ t in Ioc (0 : ℝ) 2, (autocorr G 0 - autocorr G t) / t) =
    aperture⁻¹ * ∫ t in Ioc (0 : ℝ) (2 * aperture), (autocorr F 0 - autocorr F t) / t at hScale
  rw [hScale, autocorr_zero_eq, hMass] at hLag
  have hCut := lag_cutoff hF hs
  rw [autocorr_zero_eq, hMass] at hCut
  have hWeil := weilQuad_ge_logarithmic_first_moment hF hsunit ho
  have hC : Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2 + 1 / 192 +
      1 / (96 * Real.pi ^ 2) + 97 / 483840 = firstFoldMomentMassCost + Real.log 2 := by
    unfold firstFoldMomentMassCost
    ring
  rw [hC, hMass, hPos] at hWeil
  have hPrime := dilated_prime_reflection hs ho
  change -2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) =
    2 * aperture * (Real.log 2 / Real.sqrt 2) *
      ∫ u in firstOverlapOddStripLeft..1, G u * G (firstOverlapOddStripLeft + 1 - u) at hPrime
  have hPoly := potential_integral_bound hG hGs hGo
  have hCharge := mul_le_mul_of_nonneg_right first_moment_charge_upper
    (sq_nonneg (∫ u in (0 : ℝ)..1, u * G u))
  change 2 * aperture *
    ((∫ u in (0 : ℝ)..1, firstOverlapOddPotential u * G u ^ 2) +
      (Real.log 2 / Real.sqrt 2) *
        (∫ u in firstOverlapOddStripLeft..1, G u * G (firstOverlapOddStripLeft + 1 - u)) -
      (77 / 30) * (∫ u in (0 : ℝ)..1, u * G u) ^ 2) ≤ weilQuad F
  norm_num only [aperture] at hLag hCut hWeil hPrime hPoly hCharge ⊢
  nlinarith only [hGap, hLag, hCut, hWeil, hPrime, hPoly, hCharge]

/-- Odd tests at aperture `1881/5000` have a uniform positive Weil floor. -/
theorem weilQuad_ge_odd_at_aperture_1881_over_5000 {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1881 / 5000 : ℝ)) (1881 / 5000))
    (ho : ∀ x, F (-x) = -F x) : (1 / 2000 : ℝ) * (∫ x, F x ^ 2) ≤ weilQuad F := by
  have h := weil_comparison hF hs ho
  have hG : Continuous (fun u => F (aperture * u)) :=
    hF.continuous.comp (continuous_const.mul continuous_id)
  have hFloor := firstOverlapOddEnergy_sub_first_moment hG
  have hMass := dilated_mass hF.continuous hs ho
  dsimp [aperture] at h hFloor hMass
  nlinarith only [h, hFloor, hMass]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_ge_odd_at_aperture_1881_over_5000
