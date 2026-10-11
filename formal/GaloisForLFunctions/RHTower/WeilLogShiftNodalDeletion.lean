import GaloisForLFunctions.RHTower.WeilLogShiftMomentBarycentric

/-! Exact deletion identities for nodal weights and their partial sums. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilNodalWeight_erase {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h : ι → ℝ) (hinj : Set.InjOn h ↑s)
    {a i : ι} (ha : a ∈ s) (hi : i ∈ s) (hia : i ≠ a) :
    Lagrange.nodalWeight (s.erase a) h i =
      (h i - h a) * Lagrange.nodalWeight s h i := by
  have hgap : h i - h a ≠ 0 := sub_ne_zero.mpr (fun e => hia (hinj hi ha e))
  have hp := Finset.mul_prod_erase (s.erase i) (fun j => (h i - h j)⁻¹)
    (a := a) (by simp [ha, hia.symm])
  rw [Finset.erase_right_comm] at hp
  change (h i - h a)⁻¹ * Lagrange.nodalWeight (s.erase a) h i =
    Lagrange.nodalWeight s h i at hp
  rw [← hp, ← mul_assoc, mul_inv_cancel₀ hgap, one_mul]

theorem finiteWeilNodalWeight_erase_extended {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h : ι → ℝ) (hinj : Set.InjOn h ↑s)
    {a i : ι} (ha : a ∈ s) (hi : i ∈ s) :
    (if i = a then 0 else Lagrange.nodalWeight (s.erase a) h i) =
      (h i - h a) * Lagrange.nodalWeight s h i := by
  by_cases hia : i = a
  · subst i
    simp
  · simp only [hia, ↓reduceIte]
    exact finiteWeilNodalWeight_erase s h hinj ha hi hia

theorem finiteWeilNodalWeight_deletion_difference {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h : ι → ℝ) (hinj : Set.InjOn h ↑s)
    {a b i : ι} (ha : a ∈ s) (hb : b ∈ s) (hi : i ∈ s) :
    (if i = b then 0 else Lagrange.nodalWeight (s.erase b) h i) -
      (if i = a then 0 else Lagrange.nodalWeight (s.erase a) h i) =
        (h a - h b) * Lagrange.nodalWeight s h i := by
  rw [finiteWeilNodalWeight_erase_extended s h hinj hb hi,
    finiteWeilNodalWeight_erase_extended s h hinj ha hi]
  ring

theorem finiteWeilNodalPrefix_deletion {ι : Type*} [DecidableEq ι]
    (s p : Finset ι) (h : ι → ℝ) (hinj : Set.InjOn h ↑s)
    (hps : p ⊆ s) {a b : ι} (ha : a ∈ p) (hb : b ∈ s) (hbp : b ∉ p) :
    (∑ i ∈ p, Lagrange.nodalWeight (s.erase b) h i) -
      (∑ i ∈ p.erase a, Lagrange.nodalWeight (s.erase a) h i) =
        (h a - h b) * ∑ i ∈ p, Lagrange.nodalWeight s h i := by
  have hleft : (∑ i ∈ p, Lagrange.nodalWeight (s.erase b) h i) =
      ∑ i ∈ p, (h i - h b) * Lagrange.nodalWeight s h i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact finiteWeilNodalWeight_erase s h hinj hb (hps hi)
      (fun e => hbp (e ▸ hi))
  have hright : (∑ i ∈ p.erase a, Lagrange.nodalWeight (s.erase a) h i) =
      ∑ i ∈ p, (h i - h a) * Lagrange.nodalWeight s h i := by
    calc
      _ = ∑ i ∈ p.erase a, (h i - h a) * Lagrange.nodalWeight s h i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact finiteWeilNodalWeight_erase s h hinj (hps ha)
          (hps (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi)
      _ = _ := by
        simpa using Finset.sum_erase_add p
          (fun i => (h i - h a) * Lagrange.nodalWeight s h i) ha
  rw [hleft, hright, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteWeilNodalWeight_sum_eq_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h : ι → ℝ) (hinj : Set.InjOn h ↑s) (hs : 2 ≤ s.card) :
    ∑ i ∈ s, Lagrange.nodalWeight s h i = 0 := by
  have hdeg : (1 : Polynomial ℝ).degree < (s.card : WithBot ℕ) := by
    rw [Polynomial.degree_one]
    exact_mod_cast (show 0 < s.card by omega)
  have hc := Lagrange.coeff_eq_sum hinj (P := (1 : Polynomial ℝ)) hdeg
  have hn : s.card - 1 ≠ 0 := by omega
  simpa [Polynomial.coeff_one, hn, Lagrange.nodalWeight,
    Finset.prod_inv_distrib] using hc.symm

end RHTower
