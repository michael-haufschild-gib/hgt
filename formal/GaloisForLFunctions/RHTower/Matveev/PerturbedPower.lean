import GaloisForLFunctions.RHTower.Matveev.PerturbedFrequency

/-!
# The cost of the perturbed normalization

The auxiliary construction consumes powers of the normalized frequency.  For a small form the
normalization is exact up to the single explicit term `m_pivot · Λ`, so every power differs from the
one the vanishing case would produce by at most `k` times that error times the `(k−1)`-st power of a
common bound.

That is the whole perturbation: the exact construction is recovered when `Λ = 0`, and the effective
theorem is the statement that the error term cannot be small for too long.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset

/-! ## An elementary power-difference bound -/

theorem abs_pow_sub_pow_le {x y M : ℝ} (hx : |x| ≤ M) (hy : |y| ≤ M) (n : ℕ) :
    |x ^ n - y ^ n| ≤ (n : ℝ) * M ^ (n - 1) * |x - y| := by
  have hM : 0 ≤ M := le_trans (abs_nonneg x) hx
  have hfac : (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n :=
    geom_sum₂_mul x y n
  have hbound : |∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)| ≤ (n : ℝ) * M ^ (n - 1) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ i ∈ Finset.range n, |x ^ i * y ^ (n - 1 - i)| ≤ M ^ (n - 1) := by
      intro i hi
      have hile : i ≤ n - 1 := by
        rw [Finset.mem_range] at hi
        omega
      rw [abs_mul, abs_pow, abs_pow]
      have h1 : |x| ^ i ≤ M ^ i := pow_le_pow_left₀ (abs_nonneg x) hx i
      have h2 : |y| ^ (n - 1 - i) ≤ M ^ (n - 1 - i) :=
        pow_le_pow_left₀ (abs_nonneg y) hy _
      calc |x| ^ i * |y| ^ (n - 1 - i) ≤ M ^ i * M ^ (n - 1 - i) := by
            exact mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = M ^ (i + (n - 1 - i)) := (pow_add M i (n - 1 - i)).symm
        _ = M ^ (n - 1) := by
            congr 1
            omega
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc |x ^ n - y ^ n| = |(∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (x - y)| := by
        rw [hfac]
    _ = |∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)| * |x - y| := abs_mul _ _
    _ ≤ ((n : ℝ) * M ^ (n - 1)) * |x - y| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

/-! ## The perturbed frequency power -/

variable {d : ℕ}

/-- The exact direction combination of the perturbed normalization. -/
def directionForm (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d) (m : Fin d → ℤ) : ℝ :=
  ∑ i ∈ Finset.univ.erase pivot, (perturbedDirection b pivot m i : ℝ) * Real.log (p i)

theorem pivot_mul_primeLogForm_eq_directionForm_add
    (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d) (m : Fin d → ℤ) :
    (b pivot : ℝ) * primeLogForm p m
      = directionForm p b pivot m + (m pivot : ℝ) * primeLogForm p b := by
  rw [directionForm]
  exact pivot_mul_primeLogForm p b pivot m

/-- **The perturbed power estimate.**  Powers of the normalized frequency differ from the powers
the exact normalization would produce by at most `k` times the explicit error. -/
theorem abs_pivotFrequency_pow_sub_directionForm_pow_le
    (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d) (m : Fin d → ℤ) {M : ℝ}
    (h₁ : |(b pivot : ℝ) * primeLogForm p m| ≤ M)
    (h₂ : |directionForm p b pivot m| ≤ M) (k : ℕ) :
    |((b pivot : ℝ) * primeLogForm p m) ^ k - (directionForm p b pivot m) ^ k|
      ≤ (k : ℝ) * M ^ (k - 1) * (|(m pivot : ℝ)| * |primeLogForm p b|) := by
  have hdiff : (b pivot : ℝ) * primeLogForm p m - directionForm p b pivot m
      = (m pivot : ℝ) * primeLogForm p b := by
    rw [pivot_mul_primeLogForm_eq_directionForm_add]
    ring
  have h := abs_pow_sub_pow_le h₁ h₂ k
  rw [hdiff, abs_mul] at h
  exact h

end GaloisForLFunctions.RHTower.Matveev
