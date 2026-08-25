import GaloisForLFunctions.HTGeometry.MeasurableEvenWeightedSignCarrier

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem measure_strictNegative_pos_iff_not_ae_nonneg
    {f : ℝ → ℝ} :
    0 < volume {x | f x < 0} ↔ ¬ ∀ᵐ x ∂volume, 0 ≤ f x := by
  rw [pos_iff_ne_zero]
  have hiff : (∀ᵐ x ∂volume, 0 ≤ f x) ↔ volume {x | f x < 0} = 0 := by
    simpa only [not_le] using (ae_iff (μ := volume) (p := fun x => 0 ≤ f x))
  exact (not_congr hiff).symm

theorem measure_strictPositive_pos_iff_not_ae_nonpos
    {f : ℝ → ℝ} :
    0 < volume {x | 0 < f x} ↔ ¬ ∀ᵐ x ∂volume, f x ≤ 0 := by
  rw [pos_iff_ne_zero]
  have hiff : (∀ᵐ x ∂volume, f x ≤ 0) ↔ volume {x | 0 < f x} = 0 := by
    simpa only [not_le] using (ae_iff (μ := volume) (p := fun x => f x ≤ 0))
  exact (not_congr hiff).symm

end GaloisForLFunctions.HTGeometry
