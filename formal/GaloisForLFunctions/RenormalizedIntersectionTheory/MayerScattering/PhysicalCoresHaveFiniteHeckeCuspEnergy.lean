import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerKreinLaxPhillipsRealization
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeWordsPreserveFiniteCuspEnergy

/-! The actual Cauchy-transformed PM cores lie in the same decaying cusp carrier as
window lifts. Field estimates at zero and infinity, together with two absolute
Cauchy moments, prove the global bound. Every finite source Hecke word therefore
has finite upper Haar square energy and finite dyadic cusp energy. -/

noncomputable section
open Complex Set MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerScatteringCore MayerCauchyMellinSymbol MayerEpsteinHeightMeasurability
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem fieldCore_decay_bound {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0, ‖fieldCore w a‖ ≤ C * (1 + a) ^ (-w.re) := by
  have ht : 0 ≤ tailCoefficient w := by
    unfold tailCoefficient
    exact div_nonneg (_root_.RHTower.tailConst_nonneg _) (by positivity)
  let B : ℝ := ‖riemannZeta w‖ + ‖scatteringCoefficient w‖ + tailCoefficient w
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨2 ^ w.re * B, by positivity, fun a ha => ?_⟩
  have hp : 0 < 1 + a := by linarith
  have hb : (1 + a) ^ w.re * ‖fieldCore w a‖ ≤ 2 ^ w.re * B := by
    by_cases ha1 : 1 ≤ a
    · have hf : ‖fieldCore w a‖ ≤ B * a ^ (-w.re) := by
        have h1 := Real.rpow_le_rpow_of_exponent_le ha1 (show (-1 : ℝ) ≤ -w.re by linarith)
        have h2 := Real.rpow_le_rpow_of_exponent_le ha1 (show -w.re / 2 - 1 ≤ -w.re by linarith)
        have hlarge := core_large_bound hw him ha1
        calc
          _ ≤ ‖riemannZeta w‖ * a ^ (-w.re) + ‖scatteringCoefficient w‖ * a ^ (-w.re) +
              tailCoefficient w * a ^ (-w.re) :=
            hlarge.trans (add_le_add (add_le_add le_rfl
              (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)))
              (mul_le_mul_of_nonneg_left h2 ht))
          _ = _ := by dsimp [B]; ring
      have hpow : (1 + a) ^ w.re ≤ 2 ^ w.re * a ^ w.re := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le]
        exact Real.rpow_le_rpow hp.le (by linarith) hw.le
      calc
        _ ≤ (2 ^ w.re * a ^ w.re) * (B * a ^ (-w.re)) :=
          mul_le_mul hpow hf (norm_nonneg _) (by positivity)
        _ = 2 ^ w.re * B := by
          rw [show (2 ^ w.re * a ^ w.re) * (B * a ^ (-w.re)) =
            (2 ^ w.re * B) * (a ^ w.re * a ^ (-w.re)) by ring,
            ← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero, mul_one]
    · have ha1' : a ≤ 1 := (not_le.mp ha1).le
      have hf : ‖fieldCore w a‖ ≤ B := by
        have h1 := Real.rpow_le_one ha.le ha1' (show 0 ≤ 1 - w.re by linarith)
        have h2 := Real.rpow_le_one ha.le ha1' (show 0 ≤ 1 - w.re / 2 by linarith)
        have hsmall := core_small_bound hw him ha ha1'
        have h1' : ‖scatteringCoefficient w‖ * a ^ (1 - w.re) ≤
            ‖scatteringCoefficient w‖ := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left h1 (norm_nonneg (scatteringCoefficient w)))
        have h2' : tailCoefficient w * a ^ (1 - w.re / 2) ≤ tailCoefficient w := by
          simpa only [mul_one] using (mul_le_mul_of_nonneg_left h2 ht)
        exact hsmall.trans (add_le_add (add_le_add le_rfl h1') h2')
      exact mul_le_mul (Real.rpow_le_rpow hp.le (by linarith) hw.le) hf
        (norm_nonneg _) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hp (-w.re)).le
  rw [← mul_assoc, ← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero, one_mul] at hmul
  simpa only [mul_comm] using hmul

private theorem rescaled_decay {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (1 + a / t) ^ (-r) ≤ (1 + t) * (1 + a) ^ (-r) := by
  have hx : 0 < 1 + a := by positivity
  have hy : 0 < 1 + a / t := by positivity
  have ht1 : 0 < 1 + t := by positivity
  have hbase : 1 + a ≤ (1 + t) * (1 + a / t) := by
    have hmul : t * (a / t) = a := by field_simp
    nlinarith [div_pos ha ht]
  have hpow : (1 + a) ^ r ≤ (1 + t) * (1 + a / t) ^ r := by
    calc
      _ ≤ ((1 + t) * (1 + a / t)) ^ r := Real.rpow_le_rpow hx.le hbase hr
      _ = (1 + t) ^ r * (1 + a / t) ^ r := Real.mul_rpow ht1.le hy.le
      _ ≤ (1 + t) * (1 + a / t) ^ r := mul_le_mul_of_nonneg_right
        (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1 + t) hr1)
        (Real.rpow_pos_of_pos hy _).le
  rw [Real.rpow_neg hy.le, Real.rpow_neg hx.le, ← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hy r) (Real.rpow_pos_of_pos hx r)).mpr
    (by simpa only [one_mul] using hpow)

private theorem cauchy_decay_mass_integrable {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => ‖cauchyKernel w t‖ * (1 + t) / t) (Ioi 0) := by
  have h0 := (cauchyKernel_hasMellin (w := w) (u := 0) hw (by norm_num) (by simp; linarith)).1
  have h1 := (cauchyKernel_hasMellin (w := w) (u := 1) hw (by norm_num) (by simp; linarith)).1
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((0 : ℂ) - 1) • cauchyKernel w t) (Ioi 0) at h0
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((1 : ℂ) - 1) • cauchyKernel w t) (Ioi 0) at h1
  simp only [sub_self, Complex.cpow_zero, one_smul] at h1
  simp only [zero_sub, Complex.cpow_neg_one, smul_eq_mul] at h0
  have hn0 : IntegrableOn (fun t : ℝ => ‖cauchyKernel w t‖ / t) (Ioi 0) := by
    refine MeasureTheory.IntegrableOn.congr_fun h0.norm (fun t ht => ?_) measurableSet_Ioi
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le]
    ring
  refine MeasureTheory.IntegrableOn.congr_fun (hn0.add h1.norm)
    (fun t ht => ?_) measurableSet_Ioi
  change ‖cauchyKernel w t‖ / t + ‖cauchyKernel w t‖ = _
  have ht0 : 0 < t := ht
  field_simp [ne_of_gt ht0]

/-- The actual Cauchy-transformed core has the same weighted decay as its field source. -/
theorem mayerPeriodCore_decay_bound {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1 / 2)
    (him : 0 < s.im) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0, ‖mayerPeriodCore s a‖ ≤ C * (1 + a) ^ (-(2 * s.re)) := by
  have hw : 0 < (2 * s).re := by simp; linarith
  have hw1 : (2 * s).re < 1 := by simp; linarith
  have hwi : 0 < (2 * s).im := by simp; linarith
  obtain ⟨C, hC, hf⟩ := fieldCore_decay_bound hw hw1 hwi
  let M : ℝ := ∫ t in Ioi (0 : ℝ), ‖cauchyKernel (2 * s) t‖ * (1 + t) / t
  have hM : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have ht0 : 0 < t := ht
    exact div_nonneg (mul_nonneg (norm_nonneg _) (by linarith : 0 ≤ 1 + t)) ht0.le
  refine ⟨C * M, mul_nonneg hC hM, fun a ha => ?_⟩
  have hi := cauchyKernel_core_integrable hw hwi ha
  have hmass := cauchy_decay_mass_integrable hw
  have hbound (t : ℝ) (ht : 0 < t) :
      ‖cauchyKernel (2 * s) t * fieldCore (2 * s) (a / t) / (t : ℂ)‖ ≤
        (C * (1 + a) ^ (-(2 * s).re)) * (‖cauchyKernel (2 * s) t‖ * (1 + t) / t) := by
    have hf' : ‖fieldCore (2 * s) (a / t)‖ ≤
        C * ((1 + t) * (1 + a) ^ (-(2 * s).re)) :=
      (hf _ (div_pos ha ht)).trans (mul_le_mul_of_nonneg_left
        (rescaled_decay hw.le hw1.le ha ht) hC)
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    calc
      _ ≤ (‖cauchyKernel (2 * s) t‖ *
          (C * ((1 + t) * (1 + a) ^ (-(2 * s).re)))) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf' (norm_nonneg _)) ht.le
      _ = _ := by ring
  have hnorm : ‖mayerPeriodCore s a‖ ≤
      (C * (1 + a) ^ (-(2 * s).re)) * M := by
    change ‖∫ t in Ioi (0 : ℝ),
      cauchyKernel (2 * s) t * fieldCore (2 * s) (a / t) / (t : ℂ)‖ ≤ _
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ),
          ‖cauchyKernel (2 * s) t * fieldCore (2 * s) (a / t) / (t : ℂ)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi (0 : ℝ), (C * (1 + a) ^ (-(2 * s).re)) *
          (‖cauchyKernel (2 * s) t‖ * (1 + t) / t) :=
        setIntegral_mono_on hi.norm (hmass.const_mul _) measurableSet_Ioi hbound
      _ = _ := by rw [integral_const_mul]
  have hre : (2 * s).re = 2 * s.re := by simp
  rw [hre] at hnorm
  convert hnorm using 1
  ring

/-- Measurability follows from the actual two-variable Cauchy integrand. -/
theorem mayerPeriodCore_measurable {s : ℂ} (him : 0 < s.im) : Measurable (mayerPeriodCore s) := by
  have hwi : 0 < (2 * s).im := by simp; linarith
  have hw0 : 2 * s ≠ 0 := by intro h; rw [h, Complex.zero_im] at hwi; exact lt_irrefl _ hwi
  have hw2 : 2 * s ≠ 2 := by intro h; rw [h] at hwi; norm_num at hwi
  have he := measurable_epsteinField hw0 hw2
  have hf : Measurable (fieldCore (2 * s)) := by unfold fieldCore scatteringPowers; fun_prop
  have hk : Measurable (cauchyKernel (2 * s)) := by unfold cauchyKernel cauchyWeight; fun_prop
  have hjoint : Measurable (fun p : ℝ × ℝ =>
      cauchyKernel (2 * s) p.2 * fieldCore (2 * s) (p.1 / p.2) / (p.2 : ℂ)) := by fun_prop
  exact hjoint.stronglyMeasurable.integral_prod_right.measurable

/-- Each physical core and every finite ordered source Hecke word retain weighted decay. -/
theorem lewisHeckeWord_mayerPeriodCore_decay {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1 / 2) (him : 0 < s.im) (w : List LewisHeckePrime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0,
      ‖lewisHeckeWord s w (mayerPeriodCore s) a‖ ≤ C * (1 + a) ^ (-(2 * s.re)) :=
  lewisHeckeWord_decay_bound hs.le (mayerPeriodCore_decay_bound hs hs1 him) w

/-- The actual physical cores have finite upper cusp energy under every finite word;
no zero or resonance assumption is needed. -/
theorem lewisHeckeWord_mayerPeriodCore_finite_cusp_energy {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1 / 2) (him : 0 < s.im) (w : List LewisHeckePrime) :
    IntegrableOn (fun a : ℝ => ‖lewisHeckeWord s w (mayerPeriodCore s) a‖ ^ 2 / a) (Ioi 1) ∧
      IntegrableOn (fun a : ℝ =>
        ‖dyadicCuspExtractor s (lewisHeckeWord s w (mayerPeriodCore s)) a‖ ^ 2 / a) (Ioi 1) :=
  lewisHeckeWord_finite_cusp_energy hs (mayerPeriodCore_measurable him)
    (mayerPeriodCore_decay_bound hs hs1 him) w

#print axioms lewisHeckeWord_mayerPeriodCore_decay
#print axioms lewisHeckeWord_mayerPeriodCore_finite_cusp_energy

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
