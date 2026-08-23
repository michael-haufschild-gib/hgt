import GaloisForLFunctions.RHTower.Sieve.AbelIncreasingWeight

/-!
# Abel's inequality on a shifted range

The type-I sum coming from `log ∗ μ_V` carries the weight `log k` on an interval `[A, B)`.
Shifting the corpus's `range`-form Abel inequality to an arbitrary interval is the only step
needed to strip it.
-/

namespace RHTower.Sieve

open Finset

/-- **Abel's inequality on `[A, B)` for a nondecreasing nonnegative weight.** -/
theorem norm_sum_Ico_mul_le_of_bounded_partial_mono {A B : ℕ} (hAB : A < B) (w : ℕ → ℝ)
    (g : ℕ → ℂ) {Bd : ℝ} (hw0 : 0 ≤ w A) (hmono : ∀ i, A ≤ i → w i ≤ w (i + 1))
    (hB : ∀ k, k ≤ B - A → ‖∑ i ∈ Finset.Ico A (A + k), g i‖ ≤ Bd) :
    ‖∑ i ∈ Finset.Ico A B, ((w i : ℝ) : ℂ) * g i‖ ≤ 2 * Bd * w (B - 1) := by
  classical
  set n : ℕ := B - A with hn
  have hn0 : 0 < n := by omega
  have hmain := norm_sum_mul_le_of_bounded_partial_mono n (fun j => w (A + j))
    (fun j => g (A + j)) hw0 (fun i => by
      have := hmono (A + i) (by omega)
      simpa [Nat.add_assoc] using this)
    (fun k hk => by
      have hrange : ∑ i ∈ Finset.range k, g (A + i) = ∑ i ∈ Finset.Ico A (A + k), g i := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp
      rw [hrange]
      exact hB k hk)
  have hleft : ∑ j ∈ Finset.range n, ((w (A + j) : ℝ) : ℂ) * g (A + j)
      = ∑ i ∈ Finset.Ico A B, ((w i : ℝ) : ℂ) * g i := by
    rw [Finset.sum_Ico_eq_sum_range, hn]
  have hright : w (A + (n - 1)) = w (B - 1) := by
    congr 1
    omega
  rw [hleft, hright] at hmain
  exact hmain

end RHTower.Sieve
