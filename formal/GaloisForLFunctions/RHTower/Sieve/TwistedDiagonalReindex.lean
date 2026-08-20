import Mathlib

/-!
# The twisted diagonal is a single sum

For coprime `h, k` the condition `nk = mh` forces `k ∣ m`, and writing `m = kd` forces `n = hd`.
So the diagonal of a twisted mean value, a priori a double sum, is a single sum over `d`.

This is the reindexing every twisted-moment main term starts from.
-/

open Finset

noncomputable section

namespace RHTower.Sieve

/-- A diagonal pair is `(kd, hd)` with `d = m/k`. -/
theorem twisted_diagonal_decomp {p : ℕ × ℕ} {h k : ℕ} (hk0 : 0 < k)
    (hcop : Nat.Coprime h k) (heq : p.2 * k = p.1 * h) :
    p.1 = k * (p.1 / k) ∧ p.2 = h * (p.1 / k) := by
  have hk1 : k ∣ p.1 * h := ⟨p.2, by rw [← heq]; ring⟩
  obtain ⟨d, hd⟩ := Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hk1
  have hdiv : p.1 / k = d := by rw [hd, Nat.mul_div_cancel_left _ hk0]
  have hn : p.2 = h * d := by
    have hh1 : p.2 * k = k * d * h := by rw [heq, hd]
    have hk' : p.2 * k = (h * d) * k := by rw [hh1]; ring
    exact Nat.eq_of_mul_eq_mul_right hk0 hk'
  exact ⟨by rw [hdiv, ← hd], by rw [hdiv, hn]⟩

/-- The diagonal pairs `nk = mh` with `h, k` coprime are exactly `(kd, hd)`. -/
theorem twisted_diagonal_reindex {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M)
    (s : Finset ℕ) {h k : ℕ} (hk : 1 ≤ k) (hcop : Nat.Coprime h k)
    (D : Finset ℕ) (hD : ∀ d : ℕ, d ∈ D ↔ (k * d ∈ s ∧ h * d ∈ s)) :
    ∑ m ∈ s, ∑ n ∈ s.filter (fun n => n * k = m * h), f m n
      = ∑ d ∈ D, f (k * d) (h * d) := by
  classical
  have hk0 : 0 < k := hk
  have hprod : ∑ m ∈ s, ∑ n ∈ s.filter (fun n => n * k = m * h), f m n
      = ∑ p ∈ (s ×ˢ s).filter (fun p : ℕ × ℕ => p.2 * k = p.1 * h), f p.1 p.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_filter]
  rw [hprod]
  refine (Finset.sum_nbij' (i := fun d => ((k * d, h * d) : ℕ × ℕ))
    (j := fun p : ℕ × ℕ => p.1 / k) ?_ ?_ ?_ ?_ ?_).symm
  · intro d hd
    obtain ⟨h1, h2⟩ := (hD d).mp hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, ?_⟩
    simp only
    ring
  · intro p hp
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hmem
    obtain ⟨he1, he2⟩ := twisted_diagonal_decomp hk0 hcop heq
    refine (hD (p.1 / k)).mpr ⟨?_, ?_⟩
    · rw [← he1]; exact hp1
    · rw [← he2]; exact hp2
  · intro d _
    simp only
    rw [Nat.mul_div_cancel_left _ hk0]
  · intro p hp
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨he1, he2⟩ := twisted_diagonal_decomp hk0 hcop heq
    exact Prod.ext he1.symm he2.symm
  · intro d _
    rfl

end RHTower.Sieve

end
