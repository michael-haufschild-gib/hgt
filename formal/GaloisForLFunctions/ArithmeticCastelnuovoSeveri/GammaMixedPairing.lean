import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaIntervalRemainder
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothArithmeticCellSections
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Gamma polarization and finite interval crossing measures

The symmetric Gamma measure realizes the original Lévy energy. Across an
interval boundary, subtracting its far charge leaves a finite positive measure
whose mass is proportional to interval width. Mean-zero tests kill the removed
charge exactly.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
open HTGeometry LogCells

/-- The symmetric Gamma kernel as a measure on ordered pairs. -/
def gammaKernelMeasure : Measure (ℝ × ℝ) :=
  (volume.prod volume).withDensity
    (fun p => ENNReal.ofReal (archLevyDensity |p.2 - p.1|))

/-- Measurability of the full symmetric density. -/
theorem measurable_gammaKernel :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (archLevyDensity |p.2 - p.1|)) :=
  ENNReal.measurable_ofReal.comp
    (measurable_archLevyDensity.comp (measurable_snd.sub measurable_fst).abs)

/-- The nonnegative square integral against the Gamma measure is the original energy. -/
theorem lintegral_gammaKernel_sq {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∫⁻ p, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) ∂gammaKernelMeasure) =
      2 * ENNReal.ofReal (levyEnergy f) := by
  have hm := measurable_of_boundedVariation_univ hv
  have hsq : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((f p.1 - f p.2) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((hm.comp measurable_fst).sub (hm.comp measurable_snd)).pow_const 2)
  rw [gammaKernelMeasure, lintegral_withDensity_eq_lintegral_mul _ measurable_gammaKernel
    hsq]
  simp only [Pi.mul_apply]
  have he (p : ℝ × ℝ) : ENNReal.ofReal (archLevyDensity |p.2 - p.1|) *
      ENNReal.ofReal ((f p.1 - f p.2) ^ 2) = gammaDifference f p.1 p.2 := by
    rw [gammaDifference, ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  rw [lintegral_congr he, lintegral_prod _
    (measurable_gammaDifference (measurable_of_boundedVariation_univ hv)).aemeasurable]
  exact gammaDifference_eq_two_levyEnergy hv hc

/-- Compact BV differences are square integrable for the symmetric Gamma measure. -/
theorem integrable_gammaKernel_sq {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    Integrable (fun p : ℝ × ℝ => (f p.1 - f p.2) ^ 2) gammaKernelMeasure := by
  have hm := measurable_of_boundedVariation_univ hv
  refine ⟨((hm.comp measurable_fst).sub (hm.comp measurable_snd)).pow_const 2
    |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg _),
    lintegral_gammaKernel_sq hv hc]
  exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

/-- Real conversion preserves the original normalization of Gamma energy. -/
theorem integral_gammaKernel_sq {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∫ p : ℝ × ℝ, (f p.1 - f p.2) ^ 2 ∂gammaKernelMeasure) =
      2 * levyEnergy f := by
  have hn : 0 ≤ levyEnergy f := by
    rw [← norm_levyVector_sq f hv hc]
    exact sq_nonneg _
  have he := ofReal_integral_eq_lintegral_ofReal (integrable_gammaKernel_sq hv hc)
    (ae_of_all _ fun p => sq_nonneg (f p.1 - f p.2))
  rw [lintegral_gammaKernel_sq hv hc, ← ENNReal.ofReal_ofNat (n := 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hn)] at hr
  exact hr

/-- The actual mixed Gamma form is an absolutely integrable symmetric pairing. -/
theorem integrable_gammaKernel_mixed {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2))
      gammaKernelMeasure := by
  have hfm := measurable_of_boundedVariation_univ hf
  have hgm := measurable_of_boundedVariation_univ hg
  exact integrable_mul_of_sq_integrable
    ((hfm.comp measurable_fst).sub (hfm.comp measurable_snd)).aestronglyMeasurable
    ((hgm.comp measurable_fst).sub (hgm.comp measurable_snd)).aestronglyMeasurable
    (integrable_gammaKernel_sq hf hfc) (integrable_gammaKernel_sq hg hgc)

/-- Polarization identifies the mixed pairing with the difference of actual energies. -/
theorem integral_gammaKernel_mixed {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ p : ℝ × ℝ, (f p.1 - f p.2) * (g p.1 - g p.2) ∂gammaKernelMeasure) =
      levyEnergy (fun x => f x + g x) - levyEnergy f - levyEnergy g := by
  have hiF := integrable_gammaKernel_sq hf hfc
  have hiG := integrable_gammaKernel_sq hg hgc
  have hiM := integrable_gammaKernel_mixed hf hg hfc hgc
  have hiFM : Integrable (fun p : ℝ × ℝ => (f p.1 - f p.2) ^ 2 +
      2 * ((f p.1 - f p.2) * (g p.1 - g p.2))) gammaKernelMeasure :=
    hiF.add (hiM.const_mul 2)
  have hfg : BoundedVariationOn (fun x => f x + g x) univ := by
    simpa only [neg_one_mul, sub_neg_eq_add] using
      boundedVariationOn_sub hf (bv_const_mul (-1) hg)
  have he := integral_gammaKernel_sq hfg (hfc.add hgc)
  change (∫ p : ℝ × ℝ, ((f p.1 + g p.1) - (f p.2 + g p.2)) ^ 2
    ∂gammaKernelMeasure) = 2 * levyEnergy (fun x => f x + g x) at he
  have hexp : (fun p : ℝ × ℝ => ((f p.1 + g p.1) - (f p.2 + g p.2)) ^ 2) =
      fun p => (f p.1 - f p.2) ^ 2 +
        2 * ((f p.1 - f p.2) * (g p.1 - g p.2)) + (g p.1 - g p.2) ^ 2 := by
    funext p
    ring
  rw [hexp, integral_add hiFM hiG,
    integral_add hiF (hiM.const_mul 2), integral_const_mul,
    integral_gammaKernel_sq hf hfc, integral_gammaKernel_sq hg hgc] at he
  linarith only [he]

/-- Product volume on one interval and its exterior. -/
def gammaCrossBase (a b : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo a b)).prod (volume.restrict (Ioo a b)ᶜ)

private theorem gammaCrossBase_eq_strict (a b : ℝ) :
    gammaCrossBase a b =
      (volume.restrict (Ioo a b)).prod (volume.restrict (Iio a ∪ Ioi b)) := by
  unfold gammaCrossBase
  congr 1
  apply Measure.restrict_congr_set
  filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume b] with x hxa hxb
  apply propext
  change (¬(a < x ∧ x < b)) ↔ (x < a ∨ b < x)
  constructor
  · intro hx
    rcases le_or_gt x a with h | h
    · exact Or.inl (lt_of_le_of_ne h hxa)
    · exact Or.inr (lt_of_le_of_ne (le_of_not_gt (fun hh => hx ⟨h, hh⟩)) hxb.symm)
  · rintro (h | h) hx
    · exact (not_lt_of_ge h.le) hx.1
    · exact (not_lt_of_ge h.le) hx.2

/-- The full Gamma interaction across one interval boundary. -/
def gammaCrossMeasure (a b : ℝ) : Measure (ℝ × ℝ) :=
  (gammaCrossBase a b).withDensity
    (fun p => ENNReal.ofReal (archLevyDensity |p.2 - p.1|))

/-- The positive remainder after one-sided far-charge subtraction. -/
def gammaCrossRemainderMeasure (a b : ℝ) : Measure (ℝ × ℝ) :=
  (gammaCrossBase a b).withDensity (fun p => gammaIntervalRowDefect a b p.1 p.2)

/-- The subtracted charge depends only on the exterior variable. -/
def gammaCrossFarMeasure (a b : ℝ) : Measure (ℝ × ℝ) :=
  (gammaCrossBase a b).withDensity (fun p => gammaFarCharge a b p.2)

/-- Measurability of the residual density. -/
theorem measurable_gammaIntervalRowDefect (a b : ℝ) :
    Measurable (fun p : ℝ × ℝ => gammaIntervalRowDefect a b p.1 p.2) :=
  measurable_gammaKernel.sub ((measurable_gammaFarCharge a b).comp measurable_snd)

/-- The residual crossing measure has one uniform width bound. -/
theorem gammaCrossRemainderMeasure_univ_le {a b : ℝ} (hab : a < b) (hw : b - a ≤ 1) :
    gammaCrossRemainderMeasure a b univ ≤ ENNReal.ofReal (Real.exp (1 / 2) * (b - a)) := by
  rw [gammaCrossRemainderMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    gammaCrossBase_eq_strict,
    lintegral_prod _ (measurable_gammaIntervalRowDefect a b).aemeasurable]
  exact gamma_interval_row_defect_le hab hw

/-- The unsubtracted crossing measure is finite as well. -/
theorem gammaCrossMeasure_univ_le {a b : ℝ} (hab : a < b) (hw : b - a ≤ 1) :
    gammaCrossMeasure a b univ ≤
      ENNReal.ofReal ((b - a) * (2 * gammaTailMass (b - a) + Real.exp (1 / 2))) := by
  rw [gammaCrossMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, gammaCrossBase_eq_strict,
    lintegral_prod _ measurable_gammaKernel.aemeasurable]
  exact gamma_interval_exterior_kernel_le hab hw

/-- Crossing is restriction of the original symmetric Gamma measure. -/
theorem gammaCrossMeasure_eq_restrict (a b : ℝ) :
    gammaCrossMeasure a b =
      gammaKernelMeasure.restrict (Ioo a b ×ˢ (Ioo a b)ᶜ) := by
  rw [gammaCrossMeasure, gammaCrossBase, Measure.prod_restrict, gammaKernelMeasure,
    restrict_withDensity (measurableSet_Ioo.prod measurableSet_Ioo.compl)]

/-- The crossing measure splits exactly into its positive remainder and far charge. -/
theorem gammaCrossMeasure_eq_remainder_add_far (a b : ℝ) :
    gammaCrossMeasure a b = gammaCrossRemainderMeasure a b + gammaCrossFarMeasure a b := by
  unfold gammaCrossMeasure gammaCrossRemainderMeasure gammaCrossFarMeasure
  rw [← withDensity_add_left (measurable_gammaIntervalRowDefect a b)]
  apply withDensity_congr_ae
  have hx : ∀ᵐ p ∂gammaCrossBase a b, p.1 ∈ Ioo a b :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hx] with p hp
  exact (tsub_add_cancel_of_le (gammaFarCharge_le_actual hp p.2)).symm

theorem gammaCrossRemainderMeasure_le (a b : ℝ) :
    gammaCrossRemainderMeasure a b ≤ gammaCrossMeasure a b :=
  withDensity_mono (ae_of_all _ fun _ => tsub_le_self)

theorem gammaCrossFarMeasure_le (a b : ℝ) :
    gammaCrossFarMeasure a b ≤ gammaCrossMeasure a b := by
  apply withDensity_mono
  have hx : ∀ᵐ p ∂gammaCrossBase a b, p.1 ∈ Ioo a b :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hx] with p hp
  exact gammaFarCharge_le_actual hp p.2

/-- Bounded measurable tests are integrable across a finite interval boundary. -/
theorem integrable_gammaCross_of_bound {a b : ℝ} (hab : a < b) (hw : b - a ≤ 1)
    {f : ℝ × ℝ → ℝ} (hm : Measurable f) (C : ℝ) (hb : ∀ p, ‖f p‖ ≤ C) :
    Integrable f (gammaCrossMeasure a b) := by
  letI : IsFiniteMeasure (gammaCrossMeasure a b) :=
    ⟨(gammaCrossMeasure_univ_le hab hw).trans_lt ENNReal.ofReal_lt_top⟩
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hb)

/-- A far charge cannot couple a constant interval mean to a zero-mean test. -/
theorem integral_gammaCrossFar_mixed_eq_zero (a b q : ℝ) (g h : ℝ → ℝ)
    (hg : ∀ x ∈ Ioo a b, g x = q) (hh : ∫ x in Ioo a b, h x = 0) :
    (∫ p : ℝ × ℝ, (g p.1 - g p.2) * h p.1 ∂gammaCrossFarMeasure a b) = 0 := by
  have hfinite : ∀ᵐ p ∂gammaCrossBase a b, gammaFarCharge a b p.2 < ⊤ := by
    apply ae_of_all
    intro p
    unfold gammaFarCharge
    split_ifs
    · exact ENNReal.zero_lt_top
    · exact ENNReal.ofReal_lt_top
  have hfm : Measurable (fun p : ℝ × ℝ => gammaFarCharge a b p.2) :=
    (measurable_gammaFarCharge a b).comp measurable_snd
  rw [gammaCrossFarMeasure, integral_withDensity_eq_integral_toReal_smul hfm hfinite]
  have he : (∫ p : ℝ × ℝ, (gammaFarCharge a b p.2).toReal •
      ((g p.1 - g p.2) * h p.1) ∂gammaCrossBase a b) =
      ∫ p : ℝ × ℝ, h p.1 * ((q - g p.2) * (gammaFarCharge a b p.2).toReal)
        ∂gammaCrossBase a b := by
    apply integral_congr_ae
    have hx : ∀ᵐ p ∂gammaCrossBase a b, p.1 ∈ Ioo a b :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
    filter_upwards [hx] with p hp
    rw [hg p.1 hp, smul_eq_mul]
    ring
  rw [he, gammaCrossBase, integral_prod_mul h
    (fun y => (q - g y) * (gammaFarCharge a b y).toReal), hh, zero_mul]

/-- Mean-zero cancellation leaves precisely the positive row remainder. -/
theorem integral_gammaCross_mixed_eq_remainder (a b q : ℝ) (g h : ℝ → ℝ)
    (hg : ∀ x ∈ Ioo a b, g x = q) (hh : ∫ x in Ioo a b, h x = 0)
    (hi : Integrable (fun p : ℝ × ℝ => (g p.1 - g p.2) * h p.1)
      (gammaCrossMeasure a b)) :
    (∫ p : ℝ × ℝ, (g p.1 - g p.2) * h p.1 ∂gammaCrossMeasure a b) =
      ∫ p : ℝ × ℝ, (g p.1 - g p.2) * h p.1 ∂gammaCrossRemainderMeasure a b := by
  rw [gammaCrossMeasure_eq_remainder_add_far,
    integral_add_measure (hi.mono_measure (gammaCrossRemainderMeasure_le a b))
      (hi.mono_measure (gammaCrossFarMeasure_le a b)),
    integral_gammaCrossFar_mixed_eq_zero a b q g h hg hh, add_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
