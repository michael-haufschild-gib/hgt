import GaloisForLFunctions.HTGeometry.GomesDilatonDensityShape
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Faithful raw measures and their amplitude orbits

The invisible-kernel experiment from arXiv:2607.24901v1 section 4 is applied to actual
Lebesgue measures with polynomial exponential density. Raw measures retain every
coefficient, including for infinite total mass. Positive scalar orbits forget exactly
the constant log-amplitude and therefore determine the full first-order connection.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The full real-line measure of an unrestricted polynomial dilaton profile. -/
def gomesDilatonMeasure (H : ℝ[X]) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (dilatonWeight H x))

/-- Exponential polynomial densities are continuous without growth restrictions. -/
theorem gomesDilatonWeight_continuous (H : ℝ[X]) : Continuous (dilatonWeight H) :=
  Real.continuous_exp.comp H.continuous

/-- Every raw dilaton measure has exactly the Lebesgue null sets. -/
theorem gomesDilatonMeasure_null_iff (H : ℝ[X]) (s : Set ℝ) :
    gomesDilatonMeasure H s = 0 ↔ volume s = 0 := by
  have ha := withDensity_absolutelyContinuous' (μ := (volume : Measure ℝ))
    (gomesDilatonWeight_continuous H).measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x =>
      ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos (H.eval x)))
  exact ⟨fun hs => ha hs, fun hs => withDensity_absolutelyContinuous _ _ hs⟩

/-- No polynomial exponential density has zero total mass, even when mass is infinite. -/
theorem gomesDilatonMeasure_mass_ne_zero (H : ℝ[X]) :
    gomesDilatonMeasure H Set.univ ≠ 0 := by
  intro hz
  have hv := (gomesDilatonMeasure_null_iff H Set.univ).mp hz
  rw [Real.volume_univ] at hv
  exact ENNReal.top_ne_zero hv

/-- A raw measure determines its entire polynomial generator. -/
theorem gomesDilatonMeasure_injective : Function.Injective gomesDilatonMeasure := by
  intro H K h
  have ha := (withDensity_eq_iff_of_sigmaFinite
    (gomesDilatonWeight_continuous H).measurable.ennreal_ofReal.aemeasurable
    (gomesDilatonWeight_continuous K).measurable.ennreal_ofReal.aemeasurable).mp h
  have hr : dilatonWeight H =ᵐ[volume] dilatonWeight K := ha.mono fun x hx => by
    have he := congrArg ENNReal.toReal hx
    simpa only [dilatonWeight, ENNReal.toReal_ofReal (Real.exp_pos (H.eval x)).le,
      ENNReal.toReal_ofReal (Real.exp_pos (K.eval x)).le] using he
  exact gomesDilatonWeight_injective
    (Measure.eq_of_ae_eq hr (gomesDilatonWeight_continuous H) (gomesDilatonWeight_continuous K))

/-- Constant log-amplitude acts by literal positive scaling of the full measure. -/
theorem gomesDilatonMeasure_constant (H : ℝ[X]) (c : ℝ) :
    gomesDilatonMeasure (H + C c) = ENNReal.ofReal (Real.exp c) • gomesDilatonMeasure H := by
  unfold gomesDilatonMeasure
  rw [← withDensity_smul _ (gomesDilatonWeight_continuous H).measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [gomesDilatonWeight_constant, ENNReal.ofReal_mul (Real.exp_pos c).le,
      Pi.smul_apply, smul_eq_mul]

/-- The observed exponential rescaling determines its exact additive profile shift. -/
theorem gomesDilatonMeasure_scale_iff (H K : ℝ[X]) (c : ℝ) :
    gomesDilatonMeasure H = ENNReal.ofReal (Real.exp c) • gomesDilatonMeasure K ↔
      H = K + C c := by
  rw [← gomesDilatonMeasure_constant]
  exact gomesDilatonMeasure_injective.eq_iff

/-- Arbitrary positive real scales have the same exact logarithmic reconstruction law. -/
theorem gomesDilatonMeasure_positive_scale_iff (H K : ℝ[X]) (s : Set.Ioi (0 : ℝ)) :
    gomesDilatonMeasure H = ENNReal.ofReal (s : ℝ) • gomesDilatonMeasure K ↔
      H = K + C (Real.log (s : ℝ)) := by
  have he := gomesDilatonMeasure_scale_iff H K (Real.log (s : ℝ))
  simpa only [Real.exp_log s.property] using he

/-- Projective measure observations retain precisely the existing first-order connection. -/
theorem gomesDilatonMeasure_projective_connection_iff (H K : ℝ[X]) :
    (∃ c : ℝ, gomesDilatonMeasure H =
      ENNReal.ofReal (Real.exp c) • gomesDilatonMeasure K) ↔
        dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  simp only [gomesDilatonMeasure_scale_iff, gomesDilatonConnection_constant_iff]

/-- Recording the origin-normalized measure loses exactly the density-shape ambiguity. -/
theorem gomesDilatonMeasure_centered_eq_iff (H K : ℝ[X]) :
    gomesDilatonMeasure (H - C (H.eval 0)) =
      gomesDilatonMeasure (K - C (K.eval 0)) ↔
        gomesDilatonDensityShape H = gomesDilatonDensityShape K := by
  rw [gomesDilatonMeasure_injective.eq_iff, gomesDilatonDensityShape_centered,
    gomesDilatonDensityShape_centered, gomesDilatonWeight_injective.eq_iff]

/-- Tensor multiplication of full measures is repeated density weighting on the same base. -/
theorem gomesDilatonMeasure_tensor (H K : ℝ[X]) :
    (gomesDilatonMeasure H).withDensity (fun x => ENNReal.ofReal (dilatonWeight K x)) =
      gomesDilatonMeasure (H + K) := by
  rw [gomesDilatonMeasure, ← withDensity_mul _
    (gomesDilatonWeight_continuous H).measurable.ennreal_ofReal
    (gomesDilatonWeight_continuous K).measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.mul_apply, dilatonWeight, eval_add, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos (H.eval x)).le]

/-- Dual densities cancel to infinite Lebesgue volume for every polynomial profile. -/
theorem gomesDilatonMeasure_dual_cancel (H : ℝ[X]) :
    (gomesDilatonMeasure H).withDensity (fun x => ENNReal.ofReal (dilatonWeight (-H) x)) =
      volume := by
  rw [gomesDilatonMeasure_tensor, add_neg_cancel]
  simp only [gomesDilatonMeasure, dilatonWeight, eval_zero, Real.exp_zero, ENNReal.ofReal_one]
  exact withDensity_one

end GaloisForLFunctions.HTGeometry
