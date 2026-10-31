import GaloisForLFunctions.RHTower.AtlasBlindToUnfolded

/-!
# A squared-norm perturbation bound

* `sq_norm_perturbation`: in a real inner product space, `|‖z + c‖² − ‖z‖²| ≤ 2‖z‖‖c‖ + ‖c‖²`.
* `individual_invisible`, `perturbation_grows`: arithmetic of `2√S + 1`.
* `count_bound`, `count_excludes_iff`: `N c ≤ S` gives `N ≤ S/c`, and `1 ≤ N ≤ S/c` gives `1 ≤ S/c`.

Read with `z` the vector of a quadratic zero statistic of size `S` and `c` one unit term, the first
bound says that adding the term moves the statistic by at most `O(√S)`.  This is a heuristic for why
quadratic statistics give counts; the file does not prove that correlation statistics cannot exclude
an individual zero.
-/

open Finset

noncomputable section

namespace RHTower

section Perturb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Perturbation of a squared norm.**  Adding one vector changes the square by at most
`2‖z‖‖c‖ + ‖c‖²`. -/
theorem sq_norm_perturbation (z c : E) :
    |‖z + c‖ ^ (2 : ℕ) - ‖z‖ ^ (2 : ℕ)| ≤ 2 * ‖z‖ * ‖c‖ + ‖c‖ ^ (2 : ℕ) := by
  have hexp : ‖z + c‖ ^ (2 : ℕ) = ‖z‖ ^ (2 : ℕ) + 2 * inner ℝ z c + ‖c‖ ^ (2 : ℕ) := norm_add_sq_real z c
  have hcs : |(inner ℝ z c : ℝ)| ≤ ‖z‖ * ‖c‖ := abs_real_inner_le_norm z c
  rw [hexp]
  have : ‖z‖ ^ (2 : ℕ) + 2 * inner ℝ z c + ‖c‖ ^ (2 : ℕ) - ‖z‖ ^ (2 : ℕ) = 2 * inner ℝ z c + ‖c‖ ^ (2 : ℕ) := by ring
  rw [this]
  calc |2 * (inner ℝ z c : ℝ) + ‖c‖ ^ (2 : ℕ)| ≤ |2 * (inner ℝ z c : ℝ)| + |‖c‖ ^ (2 : ℕ)| := abs_add_le _ _
    _ ≤ 2 * ‖z‖ * ‖c‖ + ‖c‖ ^ (2 : ℕ) := by
        have h1 : |2 * (inner ℝ z c : ℝ)| = 2 * |(inner ℝ z c : ℝ)| := by
          rw [abs_mul]; norm_num
        have h2 : |‖c‖ ^ (2 : ℕ)| = ‖c‖ ^ (2 : ℕ) := abs_of_nonneg (by positivity)
        rw [h1, h2]
        nlinarith [hcs]

end Perturb

/-- `1 < 2√S + 1` for `S > 1`. -/
theorem individual_invisible {S : ℝ} (hS : 1 < S) : 1 < 2 * Real.sqrt S + 1 := by
  have h : 0 < Real.sqrt S := Real.sqrt_pos.mpr (by linarith)
  linarith

/-- `S ↦ 2√S + 1` is monotone on `[0, ∞)`. -/
theorem perturbation_grows {S₁ S₂ : ℝ} (_h1 : 0 ≤ S₁) (h12 : S₁ ≤ S₂) :
    2 * Real.sqrt S₁ + 1 ≤ 2 * Real.sqrt S₂ + 1 := by
  have := Real.sqrt_le_sqrt h12
  linarith

/-- `N c ≤ S` with `c > 0` gives `N ≤ S/c`. -/
theorem count_bound {N c S : ℝ} (hc : 0 < c) (hlow : N * c ≤ S) : N ≤ S / c := by
  rw [le_div_iff₀ hc]
  exact hlow

/-- `1 ≤ N ≤ S/c` gives `1 ≤ S/c`. -/
theorem count_excludes_iff {N S c : ℝ} (_hc : 0 < c) (hN : 1 ≤ N) (hbound : N ≤ S / c) :
    1 ≤ S / c := le_trans hN hbound

end RHTower
