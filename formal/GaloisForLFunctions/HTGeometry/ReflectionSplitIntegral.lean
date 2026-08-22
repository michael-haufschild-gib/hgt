import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Splitting a real integral into the two half-lines

`∫_ℝ F = ∫_0^∞ F(u) du + ∫_0^∞ F(-u) du` for integrable `F`.  This is the reflection step that
turns a pairing against the `χ`-kernel `(-2πui)^{s-1}` — which takes different branch values on the
two half-lines — into a single Mellin integral, once the other factor is even
(Burnol, arXiv:math/0203120).

## Main results

* `integral_eq_add_reflect`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem map_neg_restrict_Ioi_zero :
    ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).map Neg.neg
      = (volume : Measure ℝ).restrict (Set.Iio (0 : ℝ)) := by
  conv_rhs => rw [← Measure.map_neg_eq_self (volume : Measure ℝ),
    measurableEmbedding_neg.restrict_map]
  congr 1
  ext x
  simp

theorem integral_Iio_zero_eq_integral_Ioi_neg (F : ℝ → E) :
    (∫ u in Set.Iio (0 : ℝ), F u) = ∫ u in Set.Ioi (0 : ℝ), F (-u) := by
  rw [← map_neg_restrict_Ioi_zero, measurableEmbedding_neg.integral_map]

/-- **Splitting a real integral into the two half-lines.** -/
theorem integral_eq_add_reflect {F : ℝ → E} (hint : Integrable F volume) :
    (∫ u : ℝ, F u) = (∫ u in Set.Ioi (0 : ℝ), F u) + ∫ u in Set.Ioi (0 : ℝ), F (-u) := by
  have hcompl := MeasureTheory.integral_add_compl (s := Set.Ioi (0:ℝ))
    (measurableSet_Ioi) hint
  have hIic : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic (0 : ℝ) := by
    ext x
    simp
  rw [hIic] at hcompl
  have hIicIio : (∫ u in Set.Iic (0 : ℝ), F u) = ∫ u in Set.Iio (0 : ℝ), F u := by
    refine MeasureTheory.setIntegral_congr_set ?_
    exact Iio_ae_eq_Iic.symm
  rw [hIicIio, integral_Iio_zero_eq_integral_Ioi_neg] at hcompl
  exact hcompl.symm

end

end GaloisForLFunctions.HTGeometry
