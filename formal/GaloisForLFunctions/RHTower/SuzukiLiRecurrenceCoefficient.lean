import Mathlib

/-!
# Suzuki's Li--moment recurrence coefficient

Suzuki, arXiv:2206.03682v4, Theorem 8.2 defines the coefficients

`b_{n,k} = n!/(k!(k+3)!) * [ (n+1)!/(n-k)! *
  ((k-(4n+3)/2)^2 + 2n + 15/4)
  + sum_{j=k+1}^n j!/(j-k-1)! * ((2j-k)^2+k+2) * a_{n-j+1} ]`.

The source proves these coefficients are positive before using them in the
moment recurrence.  This file records the printed finite expression and a
generic ordered-field lemma needed by a future source-faithful proof.  It does
not yet identify `a` with the coefficients of Riemann's completed xi function,
so it is not a formalization of Suzuki's theorem.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The coefficient `b_{n,k}` printed in Suzuki's Theorem 8.2. -/
def suzukiLiRecurrenceCoefficient (a : ℕ → ℝ) (n k : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((k.factorial : ℝ) * ((k + 3).factorial : ℝ)) *
    (((n + 1).factorial : ℝ) / ((n - k).factorial : ℝ) *
        (((k : ℝ) - (4 * (n : ℝ) + 3) / 2) ^ 2 + 2 * (n : ℝ) + 15 / 4) +
      ∑ j ∈ Finset.Icc (k + 1) n,
        (j.factorial : ℝ) / ((j - k - 1).factorial : ℝ) *
          (((2 * (j : ℝ) - k) ^ 2 + k) + 2) * a (n - j + 1))

/-- Positivity of Suzuki's printed expression under positivity of its abstract
power-series coefficients.  This is infrastructure, not the source theorem. -/
theorem suzukiLiRecurrenceCoefficient_pos_of_positive_coefficients
    {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) {n k : ℕ} (hn : 0 < n) (_hkn : k ≤ n) :
    0 < suzukiLiRecurrenceCoefficient a n k := by
  unfold suzukiLiRecurrenceCoefficient
  have hscale : 0 < (n.factorial : ℝ) /
      ((k.factorial : ℝ) * ((k + 3).factorial : ℝ)) := by
    positivity
  have hcore : 0 < ((n + 1).factorial : ℝ) / ((n - k).factorial : ℝ) *
      (((k : ℝ) - (4 * (n : ℝ) + 3) / 2) ^ 2 + 2 * (n : ℝ) + 15 / 4) := by
    positivity
  have hsum : 0 ≤ ∑ j ∈ Finset.Icc (k + 1) n,
      (j.factorial : ℝ) / ((j - k - 1).factorial : ℝ) *
        (((2 * (j : ℝ) - k) ^ 2 + k) + 2) * a (n - j + 1) := by
    apply Finset.sum_nonneg
    intro j hj
    have haj : 0 ≤ a (n - j + 1) := (ha _).le
    positivity
  exact mul_pos hscale (add_pos_of_pos_of_nonneg hcore hsum)

end

end GaloisForLFunctions.RHTower
