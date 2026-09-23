import GaloisForLFunctions.RHTower.Sieve.LargeSieveFinite

/-!
# The sharp large sieve for a separated finite set

An application supplies a *set* of frequencies with pairwise separation, not an increasing sequence.
Listing the set in increasing order turns pairwise separation into consecutive separation — for an
increasing enumeration the consecutive gap is the smallest one — so the sharp bound applies:

`∑_{x ∈ s} |S(x)|² ≤ (δ^{-1} + 4πN) ∑_{n < N} |c_n|²`

for any `s` inside one period whose distinct elements are `δ` apart.
-/

namespace RHTower.Sieve

open Finset

/-- **The sharp large sieve for a separated finite set.** -/
theorem largeSieve_gallagher_finset (N : ℕ) (hN : 0 < N) (c : Fin N → ℂ) (s : Finset ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hne : s.Nonempty)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|)
    (hmem : ∀ x ∈ s, δ / 2 ≤ x ∧ x + δ / 2 ≤ 1) :
    ∑ x ∈ s, ‖expSum N c x‖ ^ (2 : ℕ)
      ≤ (1 / δ + 4 * Real.pi * (N : ℝ)) * ∑ n : Fin N, ‖c n‖ ^ (2 : ℕ) := by
  classical
  obtain ⟨R, hR⟩ : ∃ R, s.card = R + 1 := by
    have hpos := Finset.card_pos.mpr hne
    exact ⟨s.card - 1, by omega⟩
  set e := s.orderIsoOfFin hR with he
  set lam : ℕ → ℝ := fun i => if h : i < R + 1 then ((e ⟨i, h⟩ : s) : ℝ) else 0 with hlamdef
  have hlam_eq : ∀ (i : ℕ) (h : i < R + 1), lam i = ((e ⟨i, h⟩ : s) : ℝ) := by
    intro i h
    rw [hlamdef]
    simp only [dif_pos h]
  have hlam_mem : ∀ (i : ℕ) (h : i < R + 1), lam i ∈ s := by
    intro i h
    rw [hlam_eq i h]
    exact (e ⟨i, h⟩).2
  -- an increasing enumeration has consecutive gaps at least `δ`
  have hgap : ∀ i, i < R → lam i + δ ≤ lam (i + 1) := by
    intro i hi
    have h1 : i < R + 1 := by omega
    have h2 : i + 1 < R + 1 := by omega
    have hlt : lam i < lam (i + 1) := by
      rw [hlam_eq i h1, hlam_eq (i + 1) h2]
      have hfin : (⟨i, h1⟩ : Fin (R + 1)) < ⟨i + 1, h2⟩ := by
        simp [Fin.lt_def]
      exact e.lt_iff_lt.mpr hfin
    have hne' : lam i ≠ lam (i + 1) := ne_of_lt hlt
    have habs := hsep (lam i) (hlam_mem i h1) (lam (i + 1)) (hlam_mem (i + 1) h2) hne'
    rw [abs_of_nonpos (by linarith)] at habs
    linarith
  have hlow : δ / 2 ≤ lam 0 := (hmem (lam 0) (hlam_mem 0 (by omega))).1
  have hhigh : lam R + δ / 2 ≤ 1 := (hmem (lam R) (hlam_mem R (by omega))).2
  have hbase := largeSieve_gallagher_finite N hN c hδ R hgap hlow hhigh
  -- the enumeration exhausts the set
  have hsum : ∑ r ∈ Finset.range (R + 1), ‖expSum N c (lam r)‖ ^ (2 : ℕ)
      = ∑ x ∈ s, ‖expSum N c x‖ ^ (2 : ℕ) := by
    have hfin : ∑ i : Fin (R + 1), ‖expSum N c ((e i : s) : ℝ)‖ ^ (2 : ℕ)
        = ∑ x ∈ s, ‖expSum N c x‖ ^ (2 : ℕ) := by
      rw [← Finset.sum_coe_sort s (fun x => ‖expSum N c x‖ ^ (2 : ℕ))]
      exact Equiv.sum_comp e.toEquiv (fun y : s => ‖expSum N c ((y : ℝ))‖ ^ (2 : ℕ))
    rw [← hfin, ← Fin.sum_univ_eq_sum_range (fun i => ‖expSum N c (lam i)‖ ^ (2 : ℕ)) (R + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlam_eq (i : ℕ) i.isLt]
  rw [hsum] at hbase
  exact hbase

end RHTower.Sieve
