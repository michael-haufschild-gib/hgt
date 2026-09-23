import GaloisForLFunctions.HTGeometry.SiegelTopEntry

/-!
# The top row is bounded

Once the top diagonal entries are known to be comparable in both directions, the entry bound closes
at the top row: `dₗ γₗᵢ² ≲ d'ᵢ ≲ d'ₗ ≲ dₗ`, and `dₗ` cancels.

This is the base case of the descending induction of Siegel's finiteness, and it is the first place
where an actual entry of the conjugating matrix is bounded rather than merely constrained.

* `row_top_bounded` : **every entry of the top row is bounded.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **Every entry of the top row of `γ` is bounded.** -/
theorem row_top_bounded {J J' : JacobiData n} {t u c K : ℝ} (ht : 1 ≤ t) (hc : 0 < c) (hK : 0 ≤ K)
    (hS' : J'.IsSiegel t u) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hentry : ∀ k i : Fin n, c * (J.d k * (γ k i) ^ (2 : ℕ)) ≤ K * J'.d i)
    {l : Fin n} (hl : ∀ i : Fin n, (i : ℕ) ≤ (l : ℕ))
    (hrev : c * J'.d l ≤ K * t ^ n * J.d l) (i : Fin n) :
    c ^ (2 : ℕ) * (γ l i) ^ (2 : ℕ) ≤ K ^ (2 : ℕ) * t ^ n * t ^ n := by
  have h1 : c * (J.d l * (γ l i) ^ (2 : ℕ)) ≤ K * J'.d i := hentry l i
  have h2 : J'.d i ≤ t ^ n * J'.d l := J'.d_le_pow_n ht hS' (hl i)
  have htn : (0 : ℝ) < t ^ n := pow_pos (lt_of_lt_of_le zero_lt_one ht) n
  have hdl : (0 : ℝ) < J.d l := J.pos l
  have h3 : c * (J.d l * (γ l i) ^ (2 : ℕ)) ≤ K * t ^ n * J'.d l := by
    calc c * (J.d l * (γ l i) ^ (2 : ℕ)) ≤ K * J'.d i := h1
      _ ≤ K * (t ^ n * J'.d l) := mul_le_mul_of_nonneg_left h2 hK
      _ = K * t ^ n * J'.d l := by ring
  have h4 : c * (c * (J.d l * (γ l i) ^ (2 : ℕ))) ≤ K * t ^ n * (c * J'.d l) := by
    calc c * (c * (J.d l * (γ l i) ^ (2 : ℕ))) ≤ c * (K * t ^ n * J'.d l) :=
          mul_le_mul_of_nonneg_left h3 hc.le
      _ = K * t ^ n * (c * J'.d l) := by ring
  have h5 : c * (c * (J.d l * (γ l i) ^ (2 : ℕ))) ≤ K * t ^ n * (K * t ^ n * J.d l) := by
    refine le_trans h4 ?_
    exact mul_le_mul_of_nonneg_left hrev (by positivity)
  nlinarith [h5, hdl, sq_nonneg (γ l i)]

end GaloisForLFunctions.HTGeometry
