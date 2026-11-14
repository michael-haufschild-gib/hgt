import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.SubproductStabilizerGrowth
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.MaximalAvoidingCharacters

/-!
# Character-kernel containers for missing subproducts

A target missing from an indexed subproduct set is also missing from its stabilizer.
Extending that stabilizer to a maximal avoiding character kernel turns the coset-growth
bound into a bound on off-kernel factors, with multiplicity. If the target is generated
by the factors, at least one factor must lie outside every such kernel.
-/

open Finset
open scoped Classical Pointwise

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

open HTGeometry.AddComb

variable {G ι : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [DecidableEq ι]

/-- Either the target is represented, or a cyclic character quotient contains almost all
factors. Both upper bounds retain the cardinality of the actual subproduct stabilizer. -/
theorem subproduct_target_or_character_container (q : ι → G) (I : Finset ι) (g : G) :
    g ∈ subproducts q I ∨ ∃ χ : G →* ℂˣ,
      χ g ≠ 1 ∧ stabSubgroup (subproducts q I) ≤ χ.ker ∧ IsCyclic (G ⧸ χ.ker) ∧
      ((I.filter fun i => χ (q i) ≠ 1).card + 1) * (mulStab (subproducts q I)).card ≤
        (subproducts q I).card ∧
      ((I.filter fun i => χ (q i) ≠ 1).card + 2) * (mulStab (subproducts q I)).card ≤
        Fintype.card G ∧
      (g ∉ Subgroup.closure (q '' (I : Set ι)) ∨ 1 ≤ (I.filter fun i => χ (q i) ≠ 1).card) := by
  by_cases hg : g ∈ subproducts q I
  · exact Or.inl hg
  have hgK : g ∉ stabSubgroup (subproducts q I) := by
    intro h
    exact hg (stabilizer_subset_subproducts q I (mem_mulStab.mpr h))
  obtain ⟨χ, hK, hχ, hcyclic, _⟩ :=
    (subgroup_target_or_maximal_character (stabSubgroup (subproducts q I)) g).resolve_left hgK
  have hoff : (I.filter fun i => χ (q i) ≠ 1).card ≤
      (I.filter fun i => q i ∉ mulStab (subproducts q I)).card := by
    apply card_le_card
    intro i hi
    refine mem_filter.mpr ⟨(mem_filter.mp hi).1, ?_⟩
    intro hqi
    exact (mem_filter.mp hi).2 (hK (mem_mulStab.mp hqi))
  right
  refine ⟨χ, hχ, hK, hcyclic, ?_, ?_, ?_⟩
  · exact (Nat.mul_le_mul_right _ (Nat.add_le_add_right hoff 1)).trans
      (subproduct_stabilizer_growth q I)
  · exact (Nat.mul_le_mul_right _ (Nat.add_le_add_right hoff 2)).trans
      ((subproduct_hit_or_coset_bound q I g).resolve_left hg)
  · by_cases hgen : g ∈ Subgroup.closure (q '' (I : Set ι))
    · right
      by_contra hcount
      have hall : ∀ i ∈ I, χ (q i) = 1 := by
        intro i hi
        by_contra hne
        have hpos := card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hne⟩⟩
        omega
      have hclosure : Subgroup.closure (q '' (I : Set ι)) ≤ χ.ker := by
        apply (Subgroup.closure_le _).mpr
        rintro _ ⟨i, hi, rfl⟩
        exact hall i hi
      exact hχ (hclosure hgen)
    · exact Or.inl hgen

/-- Failure of subgroup generation admits a character that annihilates every indexed factor. -/
theorem generated_target_or_common_character_kernel (q : ι → G) (I : Finset ι) (g : G) :
    g ∈ Subgroup.closure (q '' (I : Set ι)) ∨
      ∃ χ : G →* ℂˣ, χ g ≠ 1 ∧ ∀ i ∈ I, χ (q i) = 1 := by
  rcases subgroup_target_or_maximal_character (Subgroup.closure (q '' (I : Set ι))) g with
    hg | ⟨χ, hK, hχ, _, _⟩
  · exact Or.inl hg
  · refine Or.inr ⟨χ, hχ, ?_⟩
    intro i hi
    exact hK (Subgroup.subset_closure ⟨i, hi, rfl⟩)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subproduct_target_or_character_container
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.generated_target_or_common_character_kernel
