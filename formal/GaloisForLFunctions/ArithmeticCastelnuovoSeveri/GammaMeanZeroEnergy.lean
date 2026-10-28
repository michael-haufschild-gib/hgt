import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMeanZeroCoupling
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellLevyTransfer
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomHasConstantOne

/-!
# Logarithmic Gamma payment for mean-zero intervals

The symmetric Gamma difference integral is twice the original Lévy energy.
Each interval's far-end charge contains two kernel windows from its width to
one, paying the logarithm of its reciprocal width with coefficient one.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower _root_.RHTower.CHMDDoobGraph

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
open LogCells SpacingScaleHarmonicAnalysis

private theorem lintegral_even_eq_two_Ioi {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    (h0 : g 0 = 0) (he : ∀ t, g (-t) = g t) :
    (∫⁻ t, g t) = 2 * ∫⁻ t in Ioi (0 : ℝ), g t := by
  have hsplit (t : ℝ) : g t = (Ioi (0 : ℝ)).indicator g t + (Iio (0 : ℝ)).indicator g t := by
    rcases lt_trichotomy t 0 with ht | ht | ht
    · simp only [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) by exact not_lt.mpr ht.le),
        indicator_of_mem (show t ∈ Iio (0 : ℝ) from ht), zero_add]
    · subst t
      simp only [mem_Ioi, mem_Iio, lt_self_iff_false, not_false_eq_true,
        indicator_of_notMem, h0, add_zero]
    · simp only [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
        indicator_of_notMem (show t ∉ Iio (0 : ℝ) by exact not_lt.mpr ht.le), add_zero]
  have hreflect : (∫⁻ t in Iio (0 : ℝ), g t) = ∫⁻ t in Ioi (0 : ℝ), g t := by
    have hp : (Neg.neg : ℝ → ℝ) ⁻¹' Iio (0 : ℝ) = Ioi (0 : ℝ) := by
      ext t
      change -t < 0 ↔ 0 < t
      constructor <;> intro h <;> linarith only [h]
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
      (s := Iio (0 : ℝ)) measurableSet_Iio hg
    rw [hp] at h
    simpa only [he] using h.symm
  rw [lintegral_congr hsplit, lintegral_add_left (hg.indicator measurableSet_Ioi),
    lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Iio, hreflect,
    two_mul]

/-- The full symmetric Gamma difference integral is twice the original Lévy energy. -/
theorem gammaDifference_eq_two_levyEnergy {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∫⁻ x, ∫⁻ y, gammaDifference f x y) = 2 * ENNReal.ofReal (levyEnergy f) := by
  have hf := HTGeometry.measurable_of_boundedVariation_univ hv
  have hm := measurable_gammaDifference hf
  let J : ℝ → ℝ≥0∞ := fun t => ∫⁻ x, gammaDifference f x (x + t)
  have hJm : Measurable J :=
    (hm.comp (measurable_snd.prodMk (measurable_snd.add measurable_fst))).lintegral_prod_right'
  have hJ0 : J 0 = 0 := by simp only [J, gammaDifference, add_zero, sub_self,
    zero_pow (by norm_num : 2 ≠ 0), zero_mul, ENNReal.ofReal_zero, lintegral_zero]
  have hJe (t : ℝ) : J (-t) = J t := by
    have hs := (measurePreserving_add_right (volume : Measure ℝ) t).lintegral_comp
      (show Measurable (fun x => gammaDifference f x (x + -t)) from
        hm.comp (measurable_id.prodMk (measurable_id.add measurable_const)))
    calc
      J (-t) = ∫⁻ x, gammaDifference f (x + t) x := by
        simpa only [J, add_neg_cancel_right] using hs.symm
      _ = J t := lintegral_congr fun x => gammaDifference_comm f (x + t) x
  have hhalf : (∫⁻ t in Ioi (0 : ℝ), J t) = ENNReal.ofReal (levyEnergy f) := by
    have hi : Integrable (stationaryJump f) archBase :=
      (memLp_levyRoot hv hc).integrable_sq.congr (levyRoot_sq_ae f)
    have hn : 0 ≤ᵐ[archBase] stationaryJump f := by
      have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [ht] with e he
      exact mul_nonneg (archLevyDensity_pos he).le (sq_nonneg _)
    have hjm : Measurable (fun e : ℝ × ℝ => ENNReal.ofReal (stationaryJump f e)) :=
      ENNReal.measurable_ofReal.comp
        ((measurable_archLevyDensity.comp measurable_fst).mul
          ((measurable_difference hf).pow_const 2))
    rw [← stationaryEnergy_eq_levyEnergy hv hc, stationaryEnergy,
      ofReal_integral_eq_lintegral_ofReal hi hn, archBase,
      lintegral_prod _ hjm.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    change 0 < t at ht
    apply lintegral_congr
    intro x
    simp only [gammaDifference, add_sub_cancel_left, abs_of_pos ht,
      stationaryJump, difference, left, right, mul_comm]
  calc
    _ = ∫⁻ x, ∫⁻ t, gammaDifference f x (x + t) := by
      apply lintegral_congr
      intro x
      exact ((measurePreserving_add_left (volume : Measure ℝ) x).lintegral_comp
        (hm.comp (measurable_const.prodMk measurable_id))).symm
    _ = ∫⁻ t, J t := lintegral_lintegral_swap
      (hm.comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))).aemeasurable
    _ = 2 * ∫⁻ t in Ioi (0 : ℝ), J t := lintegral_even_eq_two_Ioi hJm hJ0 hJe
    _ = _ := by rw [hhalf]

/-- The two exterior kernel windows pay the logarithm of the reciprocal interval width. -/
theorem log_width_le_gammaFarCharge {a b : ℝ} (hab : a < b) (hw : b - a ≤ 1) :
    ENNReal.ofReal (Real.log (1 / (b - a))) ≤ ∫⁻ y, gammaFarCharge a b y := by
  let K : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (archLevyDensity t)
  have hW := measurable_gammaFarCharge a b
  have hright : (∫⁻ y in Ioc b (a + 1), gammaFarCharge a b y) = ∫⁻ t in Ioc (b - a) 1, K t := by
    have hp : (fun t : ℝ => a + t) ⁻¹' Ioc b (a + 1) = Ioc (b - a) 1 := by
      ext t
      change (b < a + t ∧ a + t ≤ a + 1) ↔ (b - a < t ∧ t ≤ 1)
      constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
    have h := (measurePreserving_add_left (volume : Measure ℝ) a).setLIntegral_comp_preimage
      (s := Ioc b (a + 1)) measurableSet_Ioc hW
    rw [hp] at h
    rw [← h]
    refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have hout : a + t ∉ Ioo a b := by intro hh; linarith only [hh.2, ht.1]
    have hmax : max (a + t - a) (b - (a + t)) = t := by
      rw [add_sub_cancel_left, max_eq_left (by linarith only [hab, ht.1])]
    simp only [gammaFarCharge, if_neg hout, hmax, K]
  have hleft : (∫⁻ y in Ico (b - 1) a, gammaFarCharge a b y) = ∫⁻ t in Ioc (b - a) 1, K t := by
    have hp : (fun t : ℝ => b - t) ⁻¹' Ico (b - 1) a = Ioc (b - a) 1 := by
      ext t
      change (b - 1 ≤ b - t ∧ b - t < a) ↔ (b - a < t ∧ t ≤ 1)
      constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
    have h := (Measure.measurePreserving_sub_left (volume : Measure ℝ) b).setLIntegral_comp_preimage
      (s := Ico (b - 1) a) measurableSet_Ico hW
    rw [hp] at h
    rw [← h]
    refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have hout : b - t ∉ Ioo a b := by intro hh; linarith only [hh.1, ht.1]
    have hmax : max (b - t - a) (b - (b - t)) = t := by
      rw [sub_sub_cancel, max_eq_right (by linarith only [hab, ht.1])]
    simp only [gammaFarCharge, if_neg hout, hmax, K]
  have hdisj : Disjoint (Ico (b - 1) a) (Ioc b (a + 1)) := by
    apply disjoint_left.mpr
    intro y hy hz
    linarith only [hy.2, hz.1, hab]
  have hw0 : 0 < b - a := sub_pos.mpr hab
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (b - a) 1)] archLevyDensity :=
    (ae_restrict_mem measurableSet_Ioc).mono fun t ht => (archLevyDensity_pos (hw0.trans ht.1)).le
  calc
    _ ≤ ENNReal.ofReal (2 * ∫ t in Ioc (b - a) 1, archLevyDensity t) :=
      ENNReal.ofReal_le_ofReal (log_div_le_two_mul_setIntegral_archLevyDensity hw0 hw le_rfl)
    _ = 2 * ∫⁻ t in Ioc (b - a) 1, K t := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ofReal_integral_eq_lintegral_ofReal (integrableOn_archLevyDensity_Ioc hw0) hnn]
      norm_num only [ENNReal.ofReal_ofNat]
      rfl
    _ = (∫⁻ y in Ico (b - 1) a, gammaFarCharge a b y) +
        ∫⁻ y in Ioc b (a + 1), gammaFarCharge a b y := by rw [hleft, hright, two_mul]
    _ = ∫⁻ y in Ico (b - 1) a ∪ Ioc b (a + 1), gammaFarCharge a b y :=
      (lintegral_union measurableSet_Ioc hdisj).symm
    _ ≤ ∫⁻ y, gammaFarCharge a b y := lintegral_mono' Measure.restrict_le_self le_rfl

#print axioms gammaDifference_eq_two_levyEnergy
#print axioms log_width_le_gammaFarCharge

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
