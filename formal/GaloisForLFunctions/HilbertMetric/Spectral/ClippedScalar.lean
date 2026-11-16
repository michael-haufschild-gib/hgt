import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Quadratic energy with an upper spectral cutoff

The scalar functions behind the mixed-multiplicity Gram inequality of
Knausgård, arXiv:2609.33043, §2. The quadratic part below the cutoff remains
exact; the tangent line replaces the upper tail.
-/

namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section

/-- Quadratic energy continued by its tangent at `c`. -/
def quadratic (c x : ℝ) : ℝ := x ^ 2 - (max (x - c) 0) ^ 2

/-- Clipped squared distance from the eigenvalue `1`. -/
def defect (τ x : ℝ) : ℝ := quadratic τ (x - 1)

theorem quadratic_of_le {c x : ℝ} (h : x ≤ c) : quadratic c x = x ^ 2 := by
  rw [quadratic, max_eq_right (sub_nonpos.mpr h)]
  ring

theorem quadratic_of_ge {c x : ℝ} (h : c ≤ x) :
    quadratic c x = 2 * c * x - c ^ 2 := by
  rw [quadratic, max_eq_left (sub_nonneg.mpr h)]
  ring

/-- Every slope bounded by the cutoff gives a quadratic dual certificate. -/
theorem scalar_dual {c b : ℝ} (h : b ≤ c) (x : ℝ) :
    2 * b * x - b ^ 2 ≤ quadratic c x := by
  rcases le_total x c with hx | hx
  · rw [quadratic_of_le hx]
    nlinarith only [sq_nonneg (x - b)]
  · rw [quadratic_of_ge hx]
    have hp := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hx)
    nlinarith only [hp, sq_nonneg (c - b)]

/-- Clipping the slope attains the dual bound exactly. -/
theorem quadratic_eq_dual (c x : ℝ) :
    quadratic c x = 2 * min x c * x - (min x c) ^ 2 := by
  rcases le_total x c with h | h
  · rw [quadratic_of_le h, min_eq_left h]; ring
  · rw [quadratic_of_ge h, min_eq_right h]

theorem quadratic_le_square (c x : ℝ) : quadratic c x ≤ x ^ 2 :=
  sub_le_self _ (sq_nonneg _)

theorem defect_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) : 0 ≤ defect τ x := by
  have h := scalar_dual hτ (x - 1)
  simpa only [defect, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), sub_zero] using h

theorem defect_eq_square {τ x : ℝ} (h : x ≤ 1 + τ) :
    defect τ x = (x - 1) ^ 2 := quadratic_of_le (by linarith only [h])

theorem defect_ge_cutoff {τ x : ℝ} (hτ : 0 ≤ τ) (h : 1 + τ ≤ x) :
    τ ^ 2 ≤ defect τ x := by
  rw [defect, quadratic_of_ge (by linarith only [h])]
  nlinarith only [mul_nonneg hτ (show 0 ≤ x - 1 - τ by linarith only [h])]

/-- A bounded block either keeps its complete square energy or already pays the cutoff. -/
theorem block_dichotomy {ι : Type*} [Fintype ι] (x : ι → ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    (∑ i, defect τ (x i)) = (∑ i, (x i - 1) ^ 2) ∨
      τ ^ 2 ≤ ∑ i, defect τ (x i) := by
  classical
  by_cases h : ∀ i, x i ≤ 1 + τ
  · exact Or.inl (Finset.sum_congr rfl fun i _ => defect_eq_square (h i))
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr ((defect_ge_cutoff hτ hi.le).trans
      (Finset.single_le_sum (fun j _ => defect_nonneg hτ (x j)) (Finset.mem_univ i)))

/-- The block lower bound retains any square-energy gain up to the cutoff square. -/
theorem block_min_bound {ι : Type*} [Fintype ι] (x : ι → ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    min (∑ i, (x i - 1) ^ 2) (τ ^ 2) ≤ ∑ i, defect τ (x i) := by
  rcases block_dichotomy x hτ with h | h
  · rw [h]; exact min_le_left _ _
  · exact (min_le_right _ _).trans h

end
end GaloisForLFunctions.HilbertMetric.Clipped
