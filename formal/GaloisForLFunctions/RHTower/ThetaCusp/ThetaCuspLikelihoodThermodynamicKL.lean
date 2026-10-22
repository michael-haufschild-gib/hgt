import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodModularSeam
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodStrictCooling
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodProbabilityNondivisibility
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Thermodynamic transport across the theta likelihood modular seam

Exact exponential-family transport, strict mean crossing, Radon--Nikodym and
log-likelihood ratios, directed Kullback--Leibler identities, and Jeffreys flux.
-/

open Real MeasureTheory Set Filter
open scoped ENNReal

namespace RHTower

noncomputable section

theorem thetaCuspLikelihoodSeamCrossing_mean_bracket
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) <
        thetaCuspLikelihoodSeamCrossing x ∧
      thetaCuspLikelihoodSeamCrossing x <
        thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate (-x)) := by
  let a := thetaCuspLikelihoodCoordinate (-x)
  let b := thetaCuspLikelihoodCoordinate x
  let f := fun B : ℝ => Real.log (thetaCuspLikelihoodPartition B)
  let f' := fun B : ℝ => -thetaCuspLikelihoodMean B
  have hab : a < b := thetaCuspLikelihoodCoordinate_neg_lt hx
  have ha : 0 < a := hBnx
  have hb : 0 < b := ha.trans hab
  have hcont : ContinuousOn f (Set.Icc a b) := by
    intro B hB
    exact (hasDerivAt_log_thetaCuspLikelihoodPartition_cumulant
      (ha.trans_le hB.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ B ∈ Set.Ioo a b, HasDerivAt f (f' B) B := by
    intro B hB
    exact hasDerivAt_log_thetaCuspLikelihoodPartition_cumulant
      (ha.trans hB.1)
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f f' hab hcont hderiv
  have hcross : thetaCuspLikelihoodSeamCrossing x =
      thetaCuspLikelihoodMean c := by
    rw [thetaCuspLikelihoodSeamCrossing_eq_logPartition_secant hx hBnx]
    change (f a - f b) / (b - a) = thetaCuspLikelihoodMean c
    have hden : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    have hslope' := (eq_div_iff hden).mp hslope
    apply (div_eq_iff hden).mpr
    dsimp [f, f'] at hslope' ⊢
    linarith
  rw [hcross]
  constructor
  · exact strictAntiOn_thetaCuspLikelihoodMean (ha.trans hc.1) hb hc.2
  · exact strictAntiOn_thetaCuspLikelihoodMean ha (ha.trans hc.1) hc.1

theorem integrable_exp_neg_mul_thetaCuspLikelihoodSeamMeasure
    {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => Real.exp (-B * t))
      thetaCuspLikelihoodSeamMeasure := by
  rw [thetaCuspLikelihoodSeamMeasure]
  exact Integrable.add_measure
    (integrable_dirac (by simp))
    (integrable_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB)

theorem integral_exp_neg_mul_thetaCuspLikelihoodSeamMeasure
    {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, Real.exp (-B * t) ∂thetaCuspLikelihoodSeamMeasure) =
      thetaCuspLikelihoodPartition B := by
  have hdirac : Integrable (fun t : ℝ => Real.exp (-B * t))
      (Measure.dirac 0) := integrable_dirac (by simp)
  have hhigher :=
    integrable_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB
  rw [thetaCuspLikelihoodSeamMeasure,
    integral_add_measure hdirac hhigher, integral_dirac,
    integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB]
  simp [thetaCuspLikelihoodPartition]

theorem thetaCuspLikelihoodProbabilityMeasure_eq_tilted
    {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodProbabilityMeasure B =
      thetaCuspLikelihoodSeamMeasure.tilted (fun t : ℝ => -B * t) := by
  rw [Measure.tilted,
    integral_exp_neg_mul_thetaCuspLikelihoodSeamMeasure hB]
  let g : ℝ → ℝ≥0∞ := fun t =>
    ((thetaCuspHigherLikelihoodTiltDensity B t : NNReal) : ENNReal)
  let c : ℝ≥0∞ := (ENNReal.ofReal (thetaCuspLikelihoodPartition B))⁻¹
  have hg : Measurable g :=
    (measurable_thetaCuspHigherLikelihoodTiltDensity B).coe_nnreal_ennreal
  have hdensity :
      (fun t : ℝ => ENNReal.ofReal
        (Real.exp (-B * t) / thetaCuspLikelihoodPartition B)) = c • g := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_div_of_pos (thetaCuspLikelihoodPartition_pos hB)]
    change _ = c *
      ENNReal.ofReal (Real.exp (-B * t))
    simp only [c]
    rw [div_eq_mul_inv, mul_comm]
  rw [hdensity, withDensity_smul c hg,
    thetaCuspLikelihoodSeamMeasure, withDensity_add_measure,
    dirac_withDensity g 0]
  have hgzero : g 0 = 1 := by
    simp [g, thetaCuspHigherLikelihoodTiltDensity]
  rw [hgzero, one_smul]
  change c • (Measure.dirac 0 +
      thetaCuspHigherLikelihoodSpectralMeasure.withDensity g) = _
  rfl

theorem integrable_id_thetaCuspLikelihoodProbabilityMeasure
    {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => t)
      (thetaCuspLikelihoodProbabilityMeasure B) := by
  rw [thetaCuspLikelihoodProbabilityMeasure]
  apply Integrable.smul_measure
  · rw [thetaCuspLikelihoodSeamTiltedMeasure]
    apply Integrable.add_measure
    · exact integrable_dirac (by simp)
    · simpa only [pow_one] using
        (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB)
  · simp [thetaCuspLikelihoodPartition_pos hB]

theorem integral_id_thetaCuspLikelihoodProbabilityMeasure
    {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, t ∂thetaCuspLikelihoodProbabilityMeasure B) =
      thetaCuspLikelihoodMean B := by
  have hdirac : Integrable (fun t : ℝ => t) (Measure.dirac 0) :=
    integrable_dirac (by simp)
  have hhigher : Integrable (fun t : ℝ => t)
      (thetaCuspHigherLikelihoodTiltedMeasure B) := by
    simpa only [pow_one] using
      (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB)
  rw [thetaCuspLikelihoodProbabilityMeasure,
    integral_smul_measure, thetaCuspLikelihoodSeamTiltedMeasure,
    integral_add_measure hdirac hhigher, integral_dirac]
  simp only [zero_add, smul_eq_mul]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal
    (thetaCuspLikelihoodPartition_pos hB).le]
  rw [show (∫ x : ℝ, x ∂thetaCuspHigherLikelihoodTiltedMeasure B) =
      thetaCuspHigherLikelihoodSpectralMoment B 1 by
    simp [thetaCuspHigherLikelihoodSpectralMoment]]
  change (thetaCuspLikelihoodPartition B)⁻¹ *
      thetaCuspHigherLikelihoodSpectralMoment B 1 =
    thetaCuspLikelihoodMean B
  rw [thetaCuspLikelihoodMean]
  field_simp [thetaCuspLikelihoodPartition_pos hB |>.ne']

theorem thetaCuspLikelihoodProbabilityMeasure_tilt
    {B₀ B₁ : ℝ} (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) :
    (thetaCuspLikelihoodProbabilityMeasure B₀).tilted
        (fun t : ℝ => -(B₁ - B₀) * t) =
      thetaCuspLikelihoodProbabilityMeasure B₁ := by
  rw [thetaCuspLikelihoodProbabilityMeasure_eq_tilted hB₀,
    thetaCuspLikelihoodProbabilityMeasure_eq_tilted hB₁,
    tilted_tilted
      (integrable_exp_neg_mul_thetaCuspLikelihoodSeamMeasure hB₀)]
  apply tilted_congr
  filter_upwards with t
  dsimp
  ring

theorem integrable_exp_temperatureDifference_probabilityMeasure
    {B₀ B₁ : ℝ} (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) :
    Integrable (fun t : ℝ => Real.exp (-(B₁ - B₀) * t))
      (thetaCuspLikelihoodProbabilityMeasure B₀) := by
  rw [thetaCuspLikelihoodProbabilityMeasure_eq_tilted hB₀,
    integrable_tilted_iff
      (integrable_exp_neg_mul_thetaCuspLikelihoodSeamMeasure hB₀)]
  convert integrable_exp_neg_mul_thetaCuspLikelihoodSeamMeasure hB₁ using 1
  funext t
  simp only [smul_eq_mul]
  rw [← Real.exp_add]
  congr 1
  ring

theorem integral_exp_temperatureDifference_probabilityMeasure
    {B₀ B₁ : ℝ} (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) :
    (∫ t : ℝ, Real.exp (-(B₁ - B₀) * t)
        ∂thetaCuspLikelihoodProbabilityMeasure B₀) =
      thetaCuspLikelihoodPartition B₁ /
        thetaCuspLikelihoodPartition B₀ := by
  rw [thetaCuspLikelihoodProbabilityMeasure_eq_tilted hB₀,
    integral_exp_tilted]
  rw [integral_exp_neg_mul_thetaCuspLikelihoodSeamMeasure hB₀]
  congr 1
  convert integral_exp_neg_mul_thetaCuspLikelihoodSeamMeasure hB₁ using 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [Pi.add_apply]
  congr 1
  ring

theorem thetaCuspLikelihoodProbabilityMeasure_absolutelyContinuous
    {B₀ B₁ : ℝ} (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) :
    thetaCuspLikelihoodProbabilityMeasure B₁ ≪
      thetaCuspLikelihoodProbabilityMeasure B₀ := by
  rw [← thetaCuspLikelihoodProbabilityMeasure_tilt hB₀ hB₁]
  exact tilted_absolutelyContinuous _ _

theorem llr_thetaCuspLikelihoodProbabilityMeasure
    {B₀ B₁ : ℝ} (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) :
    llr (thetaCuspLikelihoodProbabilityMeasure B₁)
        (thetaCuspLikelihoodProbabilityMeasure B₀) =ᵐ[
          thetaCuspLikelihoodProbabilityMeasure B₀]
      fun t : ℝ => -(B₁ - B₀) * t -
        Real.log (thetaCuspLikelihoodPartition B₁ /
          thetaCuspLikelihoodPartition B₀) := by
  letI : IsProbabilityMeasure
      (thetaCuspLikelihoodProbabilityMeasure B₀) :=
    thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB₀
  have hInt :=
    integrable_exp_temperatureDifference_probabilityMeasure hB₀ hB₁
  have hlog := log_rnDeriv_tilted_left_self hInt
  rw [thetaCuspLikelihoodProbabilityMeasure_tilt hB₀ hB₁,
    integral_exp_temperatureDifference_probabilityMeasure hB₀ hB₁] at hlog
  exact hlog

theorem rnDeriv_thetaCuspLikelihoodProbabilityMeasure_reflection
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate x)).rnDeriv
        (thetaCuspLikelihoodProbabilityMeasure
          (thetaCuspLikelihoodCoordinate (-x))) =ᵐ[
          thetaCuspLikelihoodProbabilityMeasure
            (thetaCuspLikelihoodCoordinate (-x))]
      fun t : ℝ => ENNReal.ofReal (Real.exp
        ((thetaCuspLikelihoodCoordinate x -
          thetaCuspLikelihoodCoordinate (-x)) *
            (thetaCuspLikelihoodSeamCrossing x - t))) := by
  let B₀ := thetaCuspLikelihoodCoordinate (-x)
  let B₁ := thetaCuspLikelihoodCoordinate x
  let d := B₁ - B₀
  have hB₀ : 0 < B₀ := hBnx
  have hd : 0 < d := sub_pos.mpr (thetaCuspLikelihoodCoordinate_neg_lt hx)
  have hB₁ : 0 < B₁ := hB₀.trans (sub_pos.mp hd)
  letI : IsProbabilityMeasure
      (thetaCuspLikelihoodProbabilityMeasure B₀) :=
    thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB₀
  have hInt :=
    integrable_exp_temperatureDifference_probabilityMeasure hB₀ hB₁
  have hrn := rnDeriv_tilted_left_self
    (μ := thetaCuspLikelihoodProbabilityMeasure B₀)
    (f := fun t : ℝ => -(B₁ - B₀) * t) (by fun_prop)
  rw [thetaCuspLikelihoodProbabilityMeasure_tilt hB₀ hB₁,
    integral_exp_temperatureDifference_probabilityMeasure hB₀ hB₁] at hrn
  filter_upwards [hrn] with t ht
  rw [ht]
  apply congrArg ENNReal.ofReal
  have hpart₀ := thetaCuspLikelihoodPartition_pos hB₀
  have hpart₁ := thetaCuspLikelihoodPartition_pos hB₁
  rw [← Real.exp_log (div_pos hpart₁ hpart₀), ← Real.exp_sub]
  apply congrArg Real.exp
  have hcross := thetaCuspLikelihoodSeamCrossing_eq_logPartition_secant hx hBnx
  dsimp [B₀, B₁, d] at hpart₀ hpart₁ hcross ⊢
  rw [Real.log_div hpart₁.ne' hpart₀.ne', hcross]
  field_simp [(sub_pos.mpr (thetaCuspLikelihoodCoordinate_neg_lt hx)).ne']
  ring

theorem llr_thetaCuspLikelihoodProbabilityMeasure_reflection
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    llr (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate x))
        (thetaCuspLikelihoodProbabilityMeasure
          (thetaCuspLikelihoodCoordinate (-x))) =ᵐ[
          thetaCuspLikelihoodProbabilityMeasure
            (thetaCuspLikelihoodCoordinate (-x))]
      fun t : ℝ =>
        (thetaCuspLikelihoodCoordinate x -
          thetaCuspLikelihoodCoordinate (-x)) *
            (thetaCuspLikelihoodSeamCrossing x - t) := by
  have hllr := llr_thetaCuspLikelihoodProbabilityMeasure
    hBnx (hBnx.trans (thetaCuspLikelihoodCoordinate_neg_lt hx))
  filter_upwards [hllr] with t ht
  rw [ht]
  have hpart₀ := thetaCuspLikelihoodPartition_pos hBnx
  have hpart₁ := thetaCuspLikelihoodPartition_pos
    (hBnx.trans (thetaCuspLikelihoodCoordinate_neg_lt hx))
  have hcross := thetaCuspLikelihoodSeamCrossing_eq_logPartition_secant hx hBnx
  rw [Real.log_div hpart₁.ne' hpart₀.ne', hcross]
  field_simp [(sub_pos.mpr (thetaCuspLikelihoodCoordinate_neg_lt hx)).ne']
  ring

theorem toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure
    {B₀ B₁ : ℝ} (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) :
    (InformationTheory.klDiv
      (thetaCuspLikelihoodProbabilityMeasure B₁)
      (thetaCuspLikelihoodProbabilityMeasure B₀)).toReal =
        -(B₁ - B₀) * thetaCuspLikelihoodMean B₁ -
          Real.log (thetaCuspLikelihoodPartition B₁ /
            thetaCuspLikelihoodPartition B₀) := by
  letI : IsProbabilityMeasure
      (thetaCuspLikelihoodProbabilityMeasure B₀) :=
    thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB₀
  letI : IsProbabilityMeasure
      (thetaCuspLikelihoodProbabilityMeasure B₁) :=
    thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB₁
  have hac :=
    thetaCuspLikelihoodProbabilityMeasure_absolutelyContinuous hB₀ hB₁
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp)]
  rw [integral_congr_ae (hac.ae_le
    (llr_thetaCuspLikelihoodProbabilityMeasure hB₀ hB₁))]
  have hid := integrable_id_thetaCuspLikelihoodProbabilityMeasure hB₁
  rw [integral_sub
    ((hid.const_mul (-(B₁ - B₀)))) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_id_thetaCuspLikelihoodProbabilityMeasure hB₁]

theorem toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure_reflection
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    (InformationTheory.klDiv
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate x))
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate (-x)))).toReal =
      (thetaCuspLikelihoodCoordinate x -
        thetaCuspLikelihoodCoordinate (-x)) *
        (thetaCuspLikelihoodSeamCrossing x -
          thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)) := by
  rw [toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure hBnx
    (hBnx.trans (thetaCuspLikelihoodCoordinate_neg_lt hx))]
  have hpart₀ := thetaCuspLikelihoodPartition_pos hBnx
  have hpart₁ := thetaCuspLikelihoodPartition_pos
    (hBnx.trans (thetaCuspLikelihoodCoordinate_neg_lt hx))
  have hcross := thetaCuspLikelihoodSeamCrossing_eq_logPartition_secant hx hBnx
  rw [Real.log_div hpart₁.ne' hpart₀.ne', hcross]
  field_simp [(sub_pos.mpr (thetaCuspLikelihoodCoordinate_neg_lt hx)).ne']
  ring

theorem toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure_reflection_reverse
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    (InformationTheory.klDiv
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate (-x)))
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate x))).toReal =
      (thetaCuspLikelihoodCoordinate x -
        thetaCuspLikelihoodCoordinate (-x)) *
        (thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate (-x)) -
          thetaCuspLikelihoodSeamCrossing x) := by
  rw [toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure
    (hBnx.trans (thetaCuspLikelihoodCoordinate_neg_lt hx)) hBnx]
  have hpart₀ := thetaCuspLikelihoodPartition_pos hBnx
  have hpart₁ := thetaCuspLikelihoodPartition_pos
    (hBnx.trans (thetaCuspLikelihoodCoordinate_neg_lt hx))
  have hcross := thetaCuspLikelihoodSeamCrossing_eq_logPartition_secant hx hBnx
  rw [Real.log_div hpart₀.ne' hpart₁.ne', hcross]
  field_simp [(sub_pos.mpr (thetaCuspLikelihoodCoordinate_neg_lt hx)).ne']
  ring

theorem toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure_reflection_pos
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    0 < (InformationTheory.klDiv
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate x))
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate (-x)))).toReal := by
  rw [toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure_reflection hx hBnx]
  exact mul_pos (sub_pos.mpr (thetaCuspLikelihoodCoordinate_neg_lt hx))
    (sub_pos.mpr (thetaCuspLikelihoodSeamCrossing_mean_bracket hx hBnx).1)

theorem toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure_reflection_reverse_pos
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    0 < (InformationTheory.klDiv
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate (-x)))
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate x))).toReal := by
  rw [toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure_reflection_reverse hx hBnx]
  exact mul_pos (sub_pos.mpr (thetaCuspLikelihoodCoordinate_neg_lt hx))
    (sub_pos.mpr (thetaCuspLikelihoodSeamCrossing_mean_bracket hx hBnx).2)

theorem toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure_jeffreys
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    (InformationTheory.klDiv
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate x))
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate (-x)))).toReal +
    (InformationTheory.klDiv
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate (-x)))
      (thetaCuspLikelihoodProbabilityMeasure
        (thetaCuspLikelihoodCoordinate x))).toReal =
      (thetaCuspLikelihoodCoordinate x -
        thetaCuspLikelihoodCoordinate (-x)) *
        (thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate (-x)) -
          thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)) := by
  rw [toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure_reflection hx hBnx,
    toReal_klDiv_thetaCuspLikelihoodProbabilityMeasure_reflection_reverse hx hBnx]
  ring

end
end RHTower


