import GaloisForLFunctions.HTGeometry.SiegelSupportWeight

/-!
# The top diagonal entries are comparable

Every row of an invertible matrix is nonzero, so for the largest index `l` there is a column `i`
with `γ_{l i} ≠ 0`.  The entry bound then gives `c d_l ≤ K d'_i`, and since `i ≤ l` the Siegel
ordering gives `d'_i ≤ tⁿ d'_l`.  So the *top* diagonal entries of two Siegel forms in one orbit are
comparable — with no hypothesis on where the nonzero entry sits.

The corresponding statement for a general index is false in this form: for `k < l` the entry bound
runs the wrong way, which is exactly why the finiteness half needs more than the entry bound.

* `exists_row_nonzero` : every row of an invertible matrix is nonzero.
* `d_top_le` : **the top diagonal entries are comparable.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **Every row of an invertible matrix has a nonzero entry.** -/
theorem exists_row_nonzero {γ δ : Matrix (Fin n) (Fin n) ℝ} (h : γ * δ = 1) (k : Fin n) :
    ∃ i : Fin n, γ k i ≠ 0 := by
  obtain ⟨i, hγ, _⟩ := exists_nonzero_pair_of_mul_eq_one h k
  exact ⟨i, hγ⟩

/-- **The top diagonal entries of two Siegel forms in one orbit are comparable.** -/
theorem d_top_le {J J' : JacobiData n} {t u c K : ℝ} (ht : 1 ≤ t) (hK : 0 ≤ K)
    (hS' : J'.IsSiegel t u) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hrow : ∀ k : Fin n, ∃ i : Fin n, γ k i ≠ 0)
    (hentry : ∀ k i : Fin n, γ k i ≠ 0 → c * J.d k ≤ K * J'.d i)
    {l : Fin n} (hl : ∀ i : Fin n, (i : ℕ) ≤ (l : ℕ)) :
    c * J.d l ≤ K * t ^ n * J'.d l := by
  obtain ⟨i, hne⟩ := hrow l
  have h1 : c * J.d l ≤ K * J'.d i := hentry l i hne
  have h2 : J'.d i ≤ t ^ n * J'.d l := J'.d_le_pow_n ht hS' (hl i)
  calc c * J.d l ≤ K * J'.d i := h1
    _ ≤ K * (t ^ n * J'.d l) := mul_le_mul_of_nonneg_left h2 hK
    _ = K * t ^ n * J'.d l := by ring

end GaloisForLFunctions.HTGeometry
