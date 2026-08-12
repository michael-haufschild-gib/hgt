import Mathlib

/-!
# Weighted `L²` interpolation into `L¹`

A square-integrable profile whose position-weighted copy is also square-integrable is integrable:

`2|P(x)| ≤ P(x)²(1 + x²) + (1 + x²)⁻¹`,

and the right side is integrable because `P, xP ∈ L²` and the Cauchy kernel is integrable.  This is
the standard passage from an energy bound plus a position-energy bound to absolute integrability,
with no support or continuity hypotheses.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- **Weighted `L²` interpolation.**  `P ∈ L²` and `xP ∈ L²` force `P ∈ L¹`. -/
theorem integrable_of_sq_integrable_of_mul_sq_integrable {P : ℝ → ℝ}
    (hPm : AEStronglyMeasurable P volume)
    (hP2 : Integrable (fun x => P x ^ 2))
    (hxP2 : Integrable (fun x => (x * P x) ^ 2)) :
    Integrable P := by
  have hcauchy : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have hmaj : Integrable (fun x => (P x ^ 2 * (1 + x ^ 2) + (1 + x ^ 2)⁻¹) / 2) := by
    have hsum : Integrable (fun x => P x ^ 2 * (1 + x ^ 2)) := by
      have h : (fun x => P x ^ 2 * (1 + x ^ 2)) = fun x => P x ^ 2 + (x * P x) ^ 2 := by
        funext x
        ring
      rw [h]
      exact hP2.add hxP2
    exact (hsum.add hcauchy).div_const 2
  refine Integrable.mono' hmaj hPm ?_
  filter_upwards with x
  have hy : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have key : 2 * |P x| * (1 + x ^ 2) ≤ P x ^ 2 * (1 + x ^ 2) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|P x| * (1 + x ^ 2) - 1), sq_abs (P x)]
  have hmain : 2 * |P x| ≤ P x ^ 2 * (1 + x ^ 2) + (1 + x ^ 2)⁻¹ := by
    nlinarith [key, hy, inv_mul_cancel₀ hy.ne', inv_nonneg.mpr hy.le]
  rw [Real.norm_eq_abs]
  linarith

end GaloisForLFunctions.HTGeometry
