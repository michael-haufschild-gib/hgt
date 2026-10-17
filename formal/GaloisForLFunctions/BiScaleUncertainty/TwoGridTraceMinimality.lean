import GaloisForLFunctions.BiScaleUncertainty.TwoGridTraceData

/-!
# Exact joint interpolation defect

The unconditional energy identity retains all trace mismatch. Fixing every
integer trace removes that term and gives the unique minimum-energy velocity.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

/-- No trace restriction is imposed: the two curvature pairings remain explicit. -/
theorem twoGrid_competitor_energy (d e : ℕ) (v : TwoGridData d e) (q : Velocity) :
    ‖q‖ ^ 2 = ‖twoGridExtension d e v‖ ^ 2 + ‖q - twoGridExtension d e v‖ ^ 2 +
      2 * (∑' j, v.1.1 j * traceCurvature (q - twoGridExtension d e v) d j) +
      2 * (∑' j, v.1.2 j * traceCurvature (q - twoGridExtension d e v) e j) := by
  rw [(hasSum_extension_curvature d v.1.1 _).tsum_eq,
    (hasSum_extension_curvature e v.1.2 _).tsum_eq]
  have hi : ⟪twoGridExtension d e v, q - twoGridExtension d e v⟫ =
      ⟪coprimeExtension d v.1.1, q - twoGridExtension d e v⟫ +
      ⟪coprimeExtension e v.1.2, q - twoGridExtension d e v⟫ := by
    rw [twoGridExtension_apply, inner_add_left]
  have h := norm_add_sq_real (twoGridExtension d e v) (q - twoGridExtension d e v)
  have hsum : twoGridExtension d e v + (q - twoGridExtension d e v) = q := by abel
  rw [hsum, hi] at h
  linarith only [h]

/-- Equality of all integer traces kills every residual curvature coefficient. -/
theorem traceCurvature_sub_eq_zero_of_integer_traces (q r : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive r k) (d j : ℕ) :
    traceCurvature (q - r) d j = 0 := by
  have hz (k : ℕ) : primitive (q - r) k = 0 := by
    rw [← inner_prefixCell, inner_sub_right, inner_prefixCell, inner_prefixCell, h, sub_self]
  have hn := coprimeCenter_ge_two d j
  have hm : ((coprimeCenter d j : ℝ) - 1) = ((coprimeCenter d j - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ coprimeCenter d j)]
    simp
  have hp : ((coprimeCenter d j : ℝ) + 1) = ((coprimeCenter d j + 1 : ℕ) : ℝ) := by
    simp
  simp only [traceCurvature, hm, hp, hz]
  ring

/-- Exact excess energy when all prescribed integer traces are met. -/
theorem twoGrid_minimum_energy_defect (d e : ℕ) (v : TwoGridData d e) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (twoGridExtension d e v) k) :
    ‖q‖ ^ 2 = ‖twoGridExtension d e v‖ ^ 2 + ‖q - twoGridExtension d e v‖ ^ 2 := by
  rw [twoGrid_competitor_energy d e v q]
  simp only [traceCurvature_sub_eq_zero_of_integer_traces q _ h, mul_zero,
    tsum_zero, add_zero]

theorem twoGrid_minimum_energy (d e : ℕ) (v : TwoGridData d e) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (twoGridExtension d e v) k) :
    ‖twoGridExtension d e v‖ ^ 2 ≤ ‖q‖ ^ 2 := by
  rw [twoGrid_minimum_energy_defect d e v q h]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem twoGrid_minimum_energy_eq_iff (d e : ℕ) (v : TwoGridData d e) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (twoGridExtension d e v) k) :
    ‖q‖ ^ 2 = ‖twoGridExtension d e v‖ ^ 2 ↔ q = twoGridExtension d e v := by
  rw [twoGrid_minimum_energy_defect d e v q h]
  simp only [add_eq_left, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
