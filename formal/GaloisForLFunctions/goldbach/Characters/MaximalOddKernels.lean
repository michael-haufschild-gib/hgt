import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.InvolutionCharacterContainers
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.SubproductStabilizerGrowth
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Odd two-primary character containers on reduced residues

A subgroup avoiding the negative unit extends to the kernel of an odd Dirichlet
character of two-power order. Applying this to the stabilizer of indexed subproducts
bounds the number of factors outside that kernel, retaining every repeated factor.
-/

open Finset
open scoped Classical Pointwise

namespace GaloisForLFunctions.Goldbach

open ArithmeticHarmonicAnalysis.FiniteGroup HTGeometry.AddComb

private theorem twoPrimary_quotient_character_power (N : ℕ)
    (χ : DirichletCharacter ℂ (N + 1))
    (hp : IsPGroup 2 ((ZMod (N + 1))ˣ ⧸ χ.toUnitHom.ker)) :
    ∃ j : ℕ, χ ^ (2 ^ j) = 1 := by
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hp
  refine ⟨j, ?_⟩
  apply MulChar.mulEquivToUnitHom.injective
  rw [map_pow, map_one]
  change χ.toUnitHom ^ (2 ^ j) = 1
  ext x
  change χ.toUnitHom x ^ (2 ^ j) = 1
  have hx : (QuotientGroup.mk' χ.toUnitHom.ker x) ^ (2 ^ j) = 1 := by
    rw [← hj]
    exact pow_card_eq_one'
  have hxker : x ^ (2 ^ j) ∈ χ.toUnitHom.ker := by
    apply (QuotientGroup.eq_one_iff (x ^ (2 ^ j))).mp
    change QuotientGroup.mk' χ.toUnitHom.ker (x ^ (2 ^ j)) = 1
    rwa [map_pow]
  change χ.toUnitHom (x ^ (2 ^ j)) = 1 at hxker
  rwa [map_pow] at hxker

/-- A subgroup contains the negative unit or lies in a maximal odd character kernel
with cyclic two-primary quotient and a two-power character exponent. -/
theorem subgroup_negative_unit_or_odd_twoPrimary_character (N : ℕ)
    (K : Subgroup (ZMod (N + 1))ˣ) :
    (-1 : (ZMod (N + 1))ˣ) ∈ K ∨ ∃ χ : DirichletCharacter ℂ (N + 1),
      χ.Odd ∧ K ≤ χ.toUnitHom.ker ∧ IsCyclic ((ZMod (N + 1))ˣ ⧸ χ.toUnitHom.ker) ∧
      IsPGroup 2 ((ZMod (N + 1))ˣ ⧸ χ.toUnitHom.ker) ∧
      (∃ j : ℕ, χ ^ (2 ^ j) = 1) ∧
        ∀ L : Subgroup (ZMod (N + 1))ˣ, χ.toUnitHom.ker ≤ L →
          (-1 : (ZMod (N + 1))ˣ) ∉ L → L = χ.toUnitHom.ker := by
  rcases subgroup_involution_or_twoPrimary_character K (-1) with
    h | h | ⟨ψ, hK, hψ, hc, hp, hmax⟩
  · exact False.elim (h (by simp))
  · exact Or.inl h
  right
  obtain ⟨χ, hχ⟩ : ∃ χ : DirichletCharacter ℂ (N + 1), χ.toUnitHom = ψ :=
    MulChar.equivToUnitHom.surjective ψ
  subst ψ
  have hodd : χ.Odd := by
    change χ (-1) = -1
    simpa only [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one] using
      congrArg (fun z : ℂˣ => (z : ℂ)) hψ
  exact ⟨χ, hodd, hK, hc, hp, twoPrimary_quotient_character_power N χ hp, hmax⟩

variable {ι : Type*} [DecidableEq ι]

/-- Missing negative-unit subproducts force an odd two-primary character container,
with both stabilizer-sensitive bounds on the exceptional indexed factors. -/
theorem negative_unit_subproduct_or_odd_container (N : ℕ)
    (q : ι → (ZMod (N + 1))ˣ) (I : Finset ι) :
    (-1 : (ZMod (N + 1))ˣ) ∈ subproducts q I ∨
      ∃ χ : DirichletCharacter ℂ (N + 1), χ.Odd ∧
        (∃ j : ℕ, χ ^ (2 ^ j) = 1) ∧
        stabSubgroup (subproducts q I) ≤ χ.toUnitHom.ker ∧
        ((I.filter fun i => χ (q i) ≠ 1).card + 1) * (mulStab (subproducts q I)).card ≤
          (subproducts q I).card ∧
        ((I.filter fun i => χ (q i) ≠ 1).card + 2) * (mulStab (subproducts q I)).card ≤
          Fintype.card (ZMod (N + 1))ˣ := by
  by_cases hg : (-1 : (ZMod (N + 1))ˣ) ∈ subproducts q I
  · exact Or.inl hg
  right
  have hgK : (-1 : (ZMod (N + 1))ˣ) ∉ stabSubgroup (subproducts q I) := by
    intro h
    exact hg (stabilizer_subset_subproducts q I (mem_mulStab.mpr h))
  obtain ⟨χ, hodd, hK, _, _, hpow, _⟩ :=
    (subgroup_negative_unit_or_odd_twoPrimary_character N
      (stabSubgroup (subproducts q I))).resolve_left hgK
  have hoff : (I.filter fun i => χ (q i) ≠ 1).card ≤
      (I.filter fun i => q i ∉ mulStab (subproducts q I)).card := by
    apply card_le_card
    intro i hi
    refine mem_filter.mpr ⟨(mem_filter.mp hi).1, ?_⟩
    intro hqi
    have he : χ.toUnitHom (q i) = 1 := hK (mem_mulStab.mp hqi)
    exact (mem_filter.mp hi).2 (congrArg (fun z : ℂˣ => (z : ℂ)) he)
  refine ⟨χ, hodd, hpow, hK, ?_, ?_⟩
  · exact (Nat.mul_le_mul_right _ (Nat.add_le_add_right hoff 1)).trans
      (subproduct_stabilizer_growth q I)
  · exact (Nat.mul_le_mul_right _ (Nat.add_le_add_right hoff 2)).trans
      ((subproduct_hit_or_coset_bound q I (-1)).resolve_left hg)

omit [DecidableEq ι] in
/-- Failure to generate the negative unit yields an odd two-primary character
that annihilates every indexed factor. -/
theorem negative_unit_generated_or_odd_common_kernel (N : ℕ)
    (q : ι → (ZMod (N + 1))ˣ) (I : Finset ι) :
    (-1 : (ZMod (N + 1))ˣ) ∈ Subgroup.closure (q '' (I : Set ι)) ∨
      ∃ χ : DirichletCharacter ℂ (N + 1), χ.Odd ∧
        (∃ j : ℕ, χ ^ (2 ^ j) = 1) ∧ ∀ i ∈ I, χ (q i) = 1 := by
  rcases subgroup_negative_unit_or_odd_twoPrimary_character N
    (Subgroup.closure (q '' (I : Set ι))) with h | ⟨χ, hodd, hK, _, _, hpow, _⟩
  · exact Or.inl h
  · refine Or.inr ⟨χ, hodd, hpow, ?_⟩
    intro i hi
    have he : χ.toUnitHom (q i) = 1 := hK (Subgroup.subset_closure ⟨i, hi, rfl⟩)
    exact congrArg (fun z : ℂˣ => (z : ℂ)) he

end GaloisForLFunctions.Goldbach

#print axioms GaloisForLFunctions.Goldbach.subgroup_negative_unit_or_odd_twoPrimary_character
#print axioms GaloisForLFunctions.Goldbach.negative_unit_subproduct_or_odd_container
#print axioms GaloisForLFunctions.Goldbach.negative_unit_generated_or_odd_common_kernel
