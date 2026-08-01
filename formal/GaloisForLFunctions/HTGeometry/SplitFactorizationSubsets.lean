import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Roots

/-!
# Monic factorizations of a product of distinct linear factors

A polynomial that is a product of distinct linear factors has exactly one monic divisor for each
subset of its roots, and every monic divisor arises that way.  Splitting it into two monic factors is
therefore the same as splitting its root set into two parts, and the factors of a prescribed degree
are indexed by the subsets of that size.

This is the elementary form of the count that a multiprojective intersection theory would give for
the fibre of a factorization map: for a separable split target no intersection theory is needed, the
factorizations are the subsets of the roots.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [CommRing K] [IsDomain K]

/-! ## The correspondence -/

theorem natDegree_prod_X_sub_C_finset (S : Finset K) :
    (∏ r ∈ S, (X - C r)).natDegree = S.card := by
  rw [Polynomial.natDegree_prod _ _ fun r _ => X_sub_C_ne_zero r]
  simp

omit [IsDomain K] in
theorem monic_prod_X_sub_C (S : Finset K) : (∏ r ∈ S, (X - C r)).Monic :=
  monic_prod_of_monic _ _ fun r _ => monic_X_sub_C r

/-- **Distinct subsets give distinct products.** -/
theorem prod_X_sub_C_injective :
    Function.Injective (fun S : Finset K => ∏ r ∈ S, (X - C r)) := by
  intro S T h
  have hroots := congrArg Polynomial.roots h
  rw [roots_prod_X_sub_C, roots_prod_X_sub_C] at hroots
  exact Finset.val_injective hroots

omit [IsDomain K] in
/-- **A subset of the roots divides.** -/
theorem prod_X_sub_C_dvd {R S : Finset K} (h : S ⊆ R) :
    (∏ r ∈ S, (X - C r)) ∣ ∏ r ∈ R, (X - C r) :=
  Finset.prod_dvd_prod_of_subset _ _ _ h

/-- **Every monic divisor is the product over a subset of the roots.** -/
theorem exists_subset_of_monic_dvd {R : Finset K} {A : K[X]} (hA : A.Monic)
    (hdvd : A ∣ ∏ r ∈ R, (X - C r)) :
    ∃ S ⊆ R, A = ∏ r ∈ S, (X - C r) := by
  classical
  have hP0 : (∏ r ∈ R, (X - C r)) ≠ 0 := (monic_prod_X_sub_C R).ne_zero
  have hle : A.roots ≤ (∏ r ∈ R, (X - C r)).roots := Polynomial.roots.le_of_dvd hP0 hdvd
  obtain ⟨B, hB⟩ := hdvd
  have hA0 : A ≠ 0 := hA.ne_zero
  have hB0 : B ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hB
    exact hP0 hB
  have hdeg : A.natDegree + B.natDegree = R.card := by
    rw [← Polynomial.natDegree_mul hA0 hB0, ← hB, natDegree_prod_X_sub_C_finset]
  have hrootcard : A.roots.card + B.roots.card = R.card := by
    have hmul : (A * B).roots = A.roots + B.roots :=
      Polynomial.roots_mul (by rw [← hB]; exact hP0)
    have := congrArg Multiset.card (hB ▸ hmul)
    rw [roots_prod_X_sub_C] at this
    simpa using this.symm
  have hAle : A.roots.card ≤ A.natDegree := Polynomial.card_roots' A
  have hBle : B.roots.card ≤ B.natDegree := Polynomial.card_roots' B
  have hcard : A.roots.card = A.natDegree := by omega
  have hprod : (Multiset.map (fun a => X - C a) A.roots).prod = A :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hA hcard
  rw [roots_prod_X_sub_C] at hle
  have hnodup : A.roots.Nodup := Multiset.nodup_of_le hle R.nodup
  refine ⟨⟨A.roots, hnodup⟩, ?_, hprod.symm⟩
  intro x hx
  exact Multiset.mem_of_le hle hx

/-- **Splitting into two monic factors is splitting the root set.** -/
theorem exists_subset_of_monic_mul_eq [DecidableEq K] {R : Finset K} {A B : K[X]} (hA : A.Monic)
    (h : A * B = ∏ r ∈ R, (X - C r)) :
    ∃ S ⊆ R, A = ∏ r ∈ S, (X - C r) ∧ B = ∏ r ∈ R \ S, (X - C r) := by
  obtain ⟨S, hSR, hAS⟩ := exists_subset_of_monic_dvd hA ⟨B, h.symm⟩
  refine ⟨S, hSR, hAS, ?_⟩
  have hsplit : (∏ r ∈ R \ S, (X - C r)) * (∏ r ∈ S, (X - C r)) = ∏ r ∈ R, (X - C r) :=
    Finset.prod_sdiff hSR
  refine mul_right_cancel₀ (monic_prod_X_sub_C S).ne_zero ?_
  rw [hsplit, ← h, hAS]
  ring

/-! ## The indexing -/

/-- The monic divisor attached to a subset of the roots. -/
noncomputable def subsetMonicDivisor (R : Finset K) (m : ℕ)
    (S : {S : Finset K // S ⊆ R ∧ S.card = m}) :
    {A : K[X] // A.Monic ∧ A ∣ (∏ r ∈ R, (X - C r)) ∧ A.natDegree = m} :=
  ⟨∏ r ∈ S.1, (X - C r), monic_prod_X_sub_C _, prod_X_sub_C_dvd S.2.1,
    by rw [natDegree_prod_X_sub_C_finset, S.2.2]⟩

/-- **The monic divisors of a prescribed degree are exactly the subsets of the roots of that
size.** -/
noncomputable def monicDivisorEquivSubset (R : Finset K) (m : ℕ) :
    {S : Finset K // S ⊆ R ∧ S.card = m} ≃
      {A : K[X] // A.Monic ∧ A ∣ (∏ r ∈ R, (X - C r)) ∧ A.natDegree = m} := by
  classical
  refine Equiv.ofBijective (subsetMonicDivisor R m) ⟨?_, ?_⟩
  · intro S T hST
    exact Subtype.ext (prod_X_sub_C_injective (congrArg Subtype.val hST))
  · rintro ⟨A, hA, hdvd, hdeg⟩
    obtain ⟨S, hSR, hAS⟩ := exists_subset_of_monic_dvd hA hdvd
    refine ⟨⟨S, hSR, ?_⟩, ?_⟩
    · rw [← natDegree_prod_X_sub_C_finset S, ← hAS, hdeg]
    · exact Subtype.ext hAS.symm

end GaloisForLFunctions.HTGeometry
