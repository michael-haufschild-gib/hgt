import GaloisForLFunctions.HTGeometry.MeasurableEvenWeightedSignCarrier

/-!
# Positive-measure sign sets on the real line

For any function `f : ℝ → ℝ`, the set where `f` is strictly negative has positive Lebesgue measure
exactly when `f` fails to be almost everywhere nonnegative, and symmetrically for strictly positive
values and almost-everywhere nonpositivity.

## Main results

- `measure_strictNegative_pos_iff_not_ae_nonneg`: `0 < vol {x | f x < 0} ↔ ¬ (0 ≤ f a.e.)`.
- `measure_strictPositive_pos_iff_not_ae_nonpos`: `0 < vol {x | 0 < f x} ↔ ¬ (f ≤ 0 a.e.)`.

## Hypotheses

Both results are unconditional; no measurability of `f` is assumed.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- `{x | f x < 0}` has positive Lebesgue measure iff `f` is not almost everywhere nonnegative. -/
theorem measure_strictNegative_pos_iff_not_ae_nonneg
    {f : ℝ → ℝ} :
    0 < volume {x | f x < 0} ↔ ¬ ∀ᵐ x ∂volume, 0 ≤ f x := by
  rw [pos_iff_ne_zero]
  have hiff : (∀ᵐ x ∂volume, 0 ≤ f x) ↔ volume {x | f x < 0} = 0 := by
    simpa only [not_le] using (ae_iff (μ := volume) (p := fun x => 0 ≤ f x))
  exact (not_congr hiff).symm

/-- `{x | 0 < f x}` has positive Lebesgue measure iff `f` is not almost everywhere nonpositive. -/
theorem measure_strictPositive_pos_iff_not_ae_nonpos
    {f : ℝ → ℝ} :
    0 < volume {x | 0 < f x} ↔ ¬ ∀ᵐ x ∂volume, f x ≤ 0 := by
  rw [pos_iff_ne_zero]
  have hiff : (∀ᵐ x ∂volume, f x ≤ 0) ↔ volume {x | 0 < f x} = 0 := by
    simpa only [not_le] using (ae_iff (μ := volume) (p := fun x => f x ≤ 0))
  exact (not_congr hiff).symm

end GaloisForLFunctions.HTGeometry
