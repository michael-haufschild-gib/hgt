import GaloisForLFunctions.HTGeometry.SiegelCovering

/-!
# Arithmetic inputs to Siegel's finiteness

The Siegel entry bound is analytic; integrality turns it into arithmetic.  A nonzero *integer* entry
has absolute value at least one, so the bound collapses to a comparison of diagonal entries.  And
because the conjugating matrix and its inverse pair to one on the diagonal, every index of the
congruate is paired with an index of the original at which the comparison holds in both directions.

* `exists_nonzero_pair_of_mul_eq_one` : the pairing supplied by `δγ = 1`.
* `d_le_of_entry_ne_zero` : **a nonzero entry forces `dₖ ≲ d'ᵢ`.**
* `exists_d_comparable` : **every index of the congruate has a two-sidedly comparable partner.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **If `M N = 1` then each diagonal index has a nontrivially pairing index.** -/
theorem exists_nonzero_pair_of_mul_eq_one {M N : Matrix (Fin n) (Fin n) ℝ} (h : M * N = 1)
    (i : Fin n) : ∃ k : Fin n, M i k ≠ 0 ∧ N k i ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hzero : (M * N) i i = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hM : M i k = 0
    · rw [hM, zero_mul]
    · rw [hcon k hM, mul_zero]
  rw [h, Matrix.one_apply_eq] at hzero
  exact one_ne_zero hzero

/-- A nonzero integer entry has square at least one. -/
theorem one_le_sq_of_int_ne_zero {x : ℝ} {z : ℤ} (hx : x = (z : ℝ)) (hne : x ≠ 0) :
    (1 : ℝ) ≤ x ^ (2 : ℕ) := by
  have hz : z ≠ 0 := by
    intro hcon
    exact hne (by rw [hx, hcon, Int.cast_zero])
  have h1 : (1 : ℤ) ≤ |z| := Int.one_le_abs (by omega)
  have h1R : (1 : ℝ) ≤ |x| := by
    rw [hx, ← Int.cast_abs]
    exact_mod_cast h1
  nlinarith [h1R, abs_nonneg x, sq_abs x]

/-- **A nonzero entry of the conjugating matrix forces a comparison of diagonal entries.** -/
theorem d_le_of_entry_ne_zero {J J' : JacobiData n} {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (hS' : J'.IsSiegel t u) (hred' : ∀ a b : Fin n, a < b → |J'.U a b| ≤ 1 / 2)
    {γ : Matrix (Fin n) (Fin n) ℝ} (hγ : J'.form = γᵀ * J.form * γ)
    (hquasi : ∀ v : Fin n → ℝ, c * (∑ m, J.d m * (v m) ^ (2 : ℕ)) ≤ v ⬝ᵥ (J.form *ᵥ v))
    {g : Matrix (Fin n) (Fin n) ℤ} (hg : ∀ a b, γ a b = (g a b : ℝ))
    {k i : Fin n} (hne : γ k i ≠ 0) :
    c * J.d k ≤ (1 + (n : ℝ) / 4 * t ^ n) * J'.d i := by
  have hsq : (1 : ℝ) ≤ (γ k i) ^ (2 : ℕ) := one_le_sq_of_int_ne_zero (hg k i) hne
  have hbound := siegel_entry_bound ht hc hS' hred' hγ hquasi k i
  have hdk : (0 : ℝ) < J.d k := J.pos k
  have h0 : (0 : ℝ) ≤ c * J.d k := (mul_pos hc hdk).le
  have hstep : c * J.d k ≤ c * (J.d k * (γ k i) ^ (2 : ℕ)) := by nlinarith [hsq, h0]
  exact le_trans hstep hbound

/-- **Every index of the congruate has a two-sidedly comparable partner.** -/
theorem exists_d_comparable {J J' : JacobiData n} {c K : ℝ}
    {γ δ : Matrix (Fin n) (Fin n) ℝ} (hδγ : δ * γ = 1)
    (hforward : ∀ k i : Fin n, γ k i ≠ 0 → c * J.d k ≤ K * J'.d i)
    (hbackward : ∀ i k : Fin n, δ i k ≠ 0 → c * J'.d i ≤ K * J.d k)
    (i : Fin n) : ∃ k : Fin n, c * J.d k ≤ K * J'.d i ∧ c * J'.d i ≤ K * J.d k := by
  obtain ⟨k, hδ, hγ⟩ := exists_nonzero_pair_of_mul_eq_one hδγ i
  exact ⟨k, hforward k i hγ, hbackward i k hδ⟩

end GaloisForLFunctions.HTGeometry
