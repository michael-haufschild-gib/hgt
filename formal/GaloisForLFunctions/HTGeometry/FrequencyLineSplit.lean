import GaloisForLFunctions.HTGeometry.FiniteWindowAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Splitting the frequency line into a window and its two tails

The variation-of-constants estimate is proved on three regions with different mechanisms: a bounded
frequency window, where only the uniform propagator bound and the window length are used; and the
two outward tails, where the integrations by parts and the resolvent decay operate.  The three
bounds compose into the global one by nothing more than additivity of the integral over a set and
its complement, together with the fact that the complement of an open window is the union of two
closed rays that overlap it in a null set.

Stated in the extended norm, so the composition is unconditional: no integrability is presupposed
on any of the three regions.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {Y : Type*} [NormedAddCommGroup Y]

/-- The complement of the open window is the union of the two closed rays. -/
theorem compl_Ioo_eq_union (X : ℝ) : (Ioo (-X) X)ᶜ = Iic (-X) ∪ Ici X := by
  ext x
  simp only [mem_compl_iff, mem_Ioo, mem_union, mem_Iic, mem_Ici, not_and_or, not_lt]

/-- **The three-region composition.** -/
theorem lintegral_sq_le_of_window_and_tails {f : ℝ → Y} {X : ℝ} {A B C : ℝ≥0∞}
    (hwin : (∫⁻ x in Ioo (-X) X, ‖f x‖ₑ ^ 2) ≤ A)
    (hneg : (∫⁻ x in Iic (-X), ‖f x‖ₑ ^ 2) ≤ B)
    (hpos : (∫⁻ x in Ici X, ‖f x‖ₑ ^ 2) ≤ C) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) ≤ A + B + C := by
  have hsplit : (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2)
      = (∫⁻ x in Ioo (-X) X, ‖f x‖ₑ ^ 2) + ∫⁻ x in (Ioo (-X) X)ᶜ, ‖f x‖ₑ ^ 2 :=
    (lintegral_add_compl _ measurableSet_Ioo).symm
  have htail : (∫⁻ x in (Ioo (-X) X)ᶜ, ‖f x‖ₑ ^ 2)
      ≤ (∫⁻ x in Iic (-X), ‖f x‖ₑ ^ 2) + ∫⁻ x in Ici X, ‖f x‖ₑ ^ 2 := by
    rw [compl_Ioo_eq_union]
    exact lintegral_union_le _ _ _
  calc (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2)
      = (∫⁻ x in Ioo (-X) X, ‖f x‖ₑ ^ 2) + ∫⁻ x in (Ioo (-X) X)ᶜ, ‖f x‖ₑ ^ 2 := hsplit
    _ ≤ A + ((∫⁻ x in Iic (-X), ‖f x‖ₑ ^ 2) + ∫⁻ x in Ici X, ‖f x‖ₑ ^ 2) :=
        add_le_add hwin htail
    _ ≤ A + (B + C) := add_le_add le_rfl (add_le_add hneg hpos)
    _ = A + B + C := (add_assoc A B C).symm

/-- **The finiteness form.**  Square integrability on the window and on both tails is square
integrability on the line. -/
theorem lintegral_sq_ne_top_of_window_and_tails {f : ℝ → Y} {X : ℝ}
    (hwin : (∫⁻ x in Ioo (-X) X, ‖f x‖ₑ ^ 2) ≠ ⊤)
    (hneg : (∫⁻ x in Iic (-X), ‖f x‖ₑ ^ 2) ≠ ⊤)
    (hpos : (∫⁻ x in Ici X, ‖f x‖ₑ ^ 2) ≠ ⊤) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_
    (lintegral_sq_le_of_window_and_tails (A := ∫⁻ x in Ioo (-X) X, ‖f x‖ₑ ^ 2)
      (B := ∫⁻ x in Iic (-X), ‖f x‖ₑ ^ 2) (C := ∫⁻ x in Ici X, ‖f x‖ₑ ^ 2)
      le_rfl le_rfl le_rfl)
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hwin, hneg⟩, hpos⟩

/-- The closed and open outward rays carry the same mass. -/
theorem lintegral_sq_Ici_eq_Ioi {f : ℝ → Y} (X : ℝ) :
    (∫⁻ x in Ici X, ‖f x‖ₑ ^ 2) = ∫⁻ x in Ioi X, ‖f x‖ₑ ^ 2 :=
  setLIntegral_congr Ioi_ae_eq_Ici.symm

/-- The closed and open inward rays carry the same mass. -/
theorem lintegral_sq_Iic_eq_Iio {f : ℝ → Y} (X : ℝ) :
    (∫⁻ x in Iic X, ‖f x‖ₑ ^ 2) = ∫⁻ x in Iio X, ‖f x‖ₑ ^ 2 :=
  setLIntegral_congr Iio_ae_eq_Iic.symm

/-! ## The moving-endpoint integral inside the window -/

variable [NormedSpace ℝ Y]

/-- The extended norm of an interval integral is at most the extended mass over the interval. -/
theorem enorm_intervalIntegral_le (f : ℝ → Y) (a b : ℝ) :
    ‖∫ t in a..b, f t‖ₑ ≤ ∫⁻ t in uIoc a b, ‖f t‖ₑ := by
  rcases le_total a b with h | h
  · rw [intervalIntegral.integral_of_le h, uIoc_of_le h]
    exact enorm_integral_le_lintegral_enorm _
  · rw [intervalIntegral.integral_of_ge h, uIoc_of_ge h, enorm_neg]
    exact enorm_integral_le_lintegral_enorm _

omit [NormedSpace ℝ Y] in
/-- Open and closed windows carry the same mass. -/
theorem lintegral_Ioo_eq_Icc (g : ℝ → ℝ≥0∞) (a b : ℝ) :
    (∫⁻ x in Ioo a b, g x) = ∫⁻ x in Icc a b, g x :=
  setLIntegral_congr Ioo_ae_eq_Icc

/-- **The moving endpoint stays in the window.**  For a frequency inside the window the
variation-of-constants integral is dominated by the whole window mass, which is what lets the
window estimate see a single fixed density. -/
theorem enorm_intervalIntegral_le_window (f : ℝ → Y) {W x : ℝ} (hx : |x| ≤ W) :
    ‖∫ t in (0 : ℝ)..x, f t‖ₑ ≤ ∫⁻ t in Icc (-W) W, ‖f t‖ₑ := by
  refine (enorm_intervalIntegral_le f 0 x).trans (lintegral_mono_set ?_)
  have hxW : -W ≤ x ∧ x ≤ W := abs_le.mp hx
  have hW : (0 : ℝ) ≤ W := le_trans (abs_nonneg x) hx
  intro t ht
  rw [uIoc] at ht
  obtain ⟨h1, h2⟩ := ht
  constructor
  · have hmin : min (0 : ℝ) x ≥ -W := le_min (by linarith) hxW.1
    linarith
  · have hmax : max (0 : ℝ) x ≤ W := max_le hW hxW.2
    linarith

end GaloisForLFunctions.HTGeometry
