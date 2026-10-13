import GaloisForLFunctions.HTGeometry.KLFactorizationSufficiency
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Exponential tilting by an observed potential commutes with observing, without integrability assumptions. -/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem map_tilted_comp {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) (q : Ω → Y) (hq : Measurable q) (g : Y → ℝ) (hg : Measurable g) :
    Measure.map q (μ.tilted (g ∘ q)) = (Measure.map q μ).tilted g := by
  have hZ : (∫ y, Real.exp (g y) ∂μ.map q) = ∫ x, Real.exp (g (q x)) ∂μ :=
    integral_map hq.aemeasurable
      (Real.continuous_exp.measurable.comp hg).aestronglyMeasurable
  unfold Measure.tilted
  rw [hZ]
  exact map_withDensity_comp μ hq (g := fun y =>
    ENNReal.ofReal (Real.exp (g y) / ∫ x, Real.exp (g (q x)) ∂μ)) (by fun_prop)

end GaloisForLFunctions.HTGeometry
