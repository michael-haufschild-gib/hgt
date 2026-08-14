import GaloisForLFunctions.Core

/-!
# Stark's simple-zero order classification

This file formalizes the exact integer-order core of Stark's simple-zero theorem for Artin
L-functions. Artin--Takagi factorization supplies the weighted order identity, while the
Foote--Murty Heilbronn-character estimate supplies the square-norm bound. When the Dedekind zeta
zero is simple, those two facts force one degree-one component of order `1` and every other
component to have order `0`.

The theorem below is the complete finite integer classification. It does not assume Artin
holomorphy and does not encode it behind a proposition interface. The analytic derivation of the
two displayed order constraints for actual Artin L-functions is outside this module.
-/

open scoped BigOperators

namespace GaloisForLFunctions

/-- **Stark simple-zero order classification.**

Let `degree i` be positive character degrees and `order i` the integer orders of corresponding
Artin L-functions at a fixed point. If the Artin--Takagi weighted order is `1` and Foote--Murty
square norm is at most `1`, then exactly one component has degree and order both `1`; all other
orders vanish. In particular, no component has a pole.

This is dependency-closed arithmetic core of literature's simple Dedekind-zeta-zero case. -/
theorem artin_stark_simpleZero_order_classifier
    {I : Type*} [Fintype I]
    (degree : I → ℕ) (order : I → ℤ)
    (hdegree : ∀ i, 0 < degree i)
    (hweighted : ∑ i, (degree i : ℤ) * order i = 1)
    (hnorm : ∑ i, order i ^ 2 ≤ 1) :
    ∃! i₀ : I,
      degree i₀ = 1 ∧ order i₀ = 1 ∧
        ∀ i, i ≠ i₀ → order i = 0 := by
  classical
  have hsquare_nonneg (i : I) : 0 ≤ order i ^ 2 := sq_nonneg (order i)
  have horder_nonneg : ∀ i, 0 ≤ order i := by
    intro i
    by_contra hi
    have hi_neg : order i ≤ -1 := by omega
    have hi_square : 1 ≤ order i ^ 2 := by nlinarith
    have hsplit :
        (∑ j ∈ Finset.univ.erase i, order j ^ 2) + order i ^ 2 ≤ 1 := by
      simpa [Finset.sum_erase_add _ _ (Finset.mem_univ i)] using hnorm
    have herase_nonneg : 0 ≤ ∑ j ∈ Finset.univ.erase i, order j ^ 2 :=
      Finset.sum_nonneg fun j _ ↦ hsquare_nonneg j
    have herase_zero : ∑ j ∈ Finset.univ.erase i, order j ^ 2 = 0 := by
      omega
    have hi_eq : order i = -1 := by nlinarith
    have hother : ∀ j, j ≠ i → order j = 0 := by
      intro j hji
      have hjmem : j ∈ Finset.univ.erase i := by simp [hji]
      have hjle : order j ^ 2 ≤ ∑ k ∈ Finset.univ.erase i, order k ^ 2 :=
        Finset.single_le_sum (fun k _ ↦ hsquare_nonneg k) hjmem
      rw [herase_zero] at hjle
      nlinarith [hsquare_nonneg j]
    have hw := hweighted
    rw [Finset.sum_eq_single i
      (fun j _ hji ↦ by simp [hother j hji]) (by simp)] at hw
    have hdi : (0 : ℤ) < degree i := by exact_mod_cast hdegree i
    rw [hi_eq] at hw
    nlinarith
  have hterm_nonneg (i : I) : 0 ≤ (degree i : ℤ) * order i :=
    mul_nonneg (Nat.cast_nonneg _) (horder_nonneg i)
  have hexists_pos : ∃ i, 0 < (degree i : ℤ) * order i := by
    by_contra h
    push Not at h
    have hzero : ∀ i, (degree i : ℤ) * order i = 0 := by
      intro i
      exact le_antisymm (h i) (hterm_nonneg i)
    have : (∑ i, (degree i : ℤ) * order i) = 0 := by simp [hzero]
    omega
  obtain ⟨i₀, hi₀_pos⟩ := hexists_pos
  have hi₀_le : (degree i₀ : ℤ) * order i₀ ≤
      ∑ i, (degree i : ℤ) * order i :=
    Finset.single_le_sum (fun i _ ↦ hterm_nonneg i) (Finset.mem_univ i₀)
  have hi₀_prod : (degree i₀ : ℤ) * order i₀ = 1 := by omega
  have hdegree_i₀_pos : (0 : ℤ) < degree i₀ := by exact_mod_cast hdegree i₀
  have horder_i₀_pos : 0 < order i₀ := by nlinarith
  have hdegree_i₀_int : (degree i₀ : ℤ) = 1 := by nlinarith
  have hdegree_i₀ : degree i₀ = 1 := by exact_mod_cast hdegree_i₀_int
  have horder_i₀ : order i₀ = 1 := by nlinarith
  have hsplit :
      (∑ j ∈ Finset.univ.erase i₀, (degree j : ℤ) * order j) +
          (degree i₀ : ℤ) * order i₀ = 1 := by
    simpa [Finset.sum_erase_add _ _ (Finset.mem_univ i₀)] using hweighted
  have herase_zero :
      ∑ j ∈ Finset.univ.erase i₀, (degree j : ℤ) * order j = 0 := by
    omega
  have hother : ∀ j, j ≠ i₀ → order j = 0 := by
    intro j hji
    have hjmem : j ∈ Finset.univ.erase i₀ := by simp [hji]
    have hjle : (degree j : ℤ) * order j ≤
        ∑ k ∈ Finset.univ.erase i₀, (degree k : ℤ) * order k :=
      Finset.single_le_sum (fun k _ ↦ hterm_nonneg k) hjmem
    rw [herase_zero] at hjle
    have hdj : (0 : ℤ) < degree j := by exact_mod_cast hdegree j
    nlinarith [horder_nonneg j]
  refine ⟨i₀, ⟨hdegree_i₀, horder_i₀, hother⟩, ?_⟩
  intro j hj
  by_contra hji
  have hj_zero := hother j hji
  omega

end GaloisForLFunctions
