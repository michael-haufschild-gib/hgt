import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Factors of a product of primes

If `a * b` is a product of primes indexed by a finite set `s`, then `a` is associated to the
product over some subset `t ⊆ s`, and `b` to the product over the complement.  This is the
refinement statement that turns a factorisation of a product of irreducibles into a partition of
the index set.
-/

namespace GaloisForLFunctions.HTGeometry.PrimeSubsetFactor

open Finset

variable {M₀ : Type*} [CommMonoidWithZero M₀] [IsCancelMulZero M₀] [Nontrivial M₀]
variable {ι : Type*} [DecidableEq ι]

omit [Nontrivial M₀] in
/-- A factor of a product of primes is associated to the product over a subset. -/
theorem exists_subset_associated (s : Finset ι) (p : ι → M₀) :
    ∀ (_ : ∀ i ∈ s, Prime (p i)) (a b : M₀), a * b = ∏ i ∈ s, p i →
      ∃ t ⊆ s, Associated a (∏ i ∈ t, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _ a b h
      refine ⟨∅, Finset.Subset.refl _, ?_⟩
      rw [Finset.prod_empty] at h ⊢
      exact associated_one_iff_isUnit.mpr ⟨⟨a, b, h, (mul_comm b a).trans h⟩, rfl⟩
  | insert i s hi ih =>
      intro hp a b h
      have hprime : Prime (p i) := hp i (Finset.mem_insert_self i s)
      have hps : ∀ j ∈ s, Prime (p j) := fun j hj => hp j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi] at h
      have hdvd : p i ∣ a * b := ⟨∏ j ∈ s, p j, h⟩
      rcases hprime.2.2 a b hdvd with hA | hB
      · obtain ⟨a', rfl⟩ := hA
        have h' : a' * b = ∏ j ∈ s, p j := by
          refine mul_left_cancel₀ hprime.ne_zero ?_
          rw [← mul_assoc]
          exact h
        obtain ⟨t', ht', hassoc⟩ := ih hps a' b h'
        have hit : i ∉ t' := fun hmem => hi (ht' hmem)
        refine ⟨insert i t', Finset.insert_subset_insert i ht', ?_⟩
        rw [Finset.prod_insert hit]
        exact hassoc.mul_left (p i)
      · obtain ⟨b', rfl⟩ := hB
        have h' : a * b' = ∏ j ∈ s, p j := by
          refine mul_left_cancel₀ hprime.ne_zero ?_
          rw [mul_left_comm]
          exact h
        obtain ⟨t', ht', hassoc⟩ := ih hps a b' h'
        exact ⟨t', ht'.trans (Finset.subset_insert i s), hassoc⟩

/-- The complementary half of `exists_subset_associated`. -/
theorem associated_sdiff_of_associated {s t : Finset ι} (hts : t ⊆ s) {p : ι → M₀}
    (hp : ∀ i ∈ s, Prime (p i)) {a b : M₀} (h : a * b = ∏ i ∈ s, p i)
    (ha : Associated a (∏ i ∈ t, p i)) : Associated b (∏ i ∈ s \ t, p i) := by
  classical
  obtain ⟨u, hu⟩ := ha
  have hsplit : (∏ i ∈ s \ t, p i) * (∏ i ∈ t, p i) = ∏ i ∈ s, p i := Finset.prod_sdiff hts
  have hne : (∏ i ∈ t, p i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => (hp i (hts hi)).ne_zero
  have ha' : a = (∏ i ∈ t, p i) * (↑u⁻¹ : M₀) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨u⁻¹, ?_⟩
  refine mul_left_cancel₀ hne ?_
  calc (∏ i ∈ t, p i) * (b * (↑u⁻¹ : M₀))
      = ((∏ i ∈ t, p i) * (↑u⁻¹ : M₀)) * b := by rw [mul_comm b, ← mul_assoc]
    _ = a * b := by rw [← ha']
    _ = ∏ i ∈ s, p i := h
    _ = (∏ i ∈ s \ t, p i) * (∏ i ∈ t, p i) := hsplit.symm
    _ = (∏ i ∈ t, p i) * (∏ i ∈ s \ t, p i) := mul_comm _ _

end GaloisForLFunctions.HTGeometry.PrimeSubsetFactor
