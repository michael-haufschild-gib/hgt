import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Finset.Max

/-!
# Maximal avoiding subgroups are character kernels

In a finite abelian group, every subgroup avoiding a specified element extends to a
maximal subgroup with that property. Character separation on the quotient makes such
a maximal subgroup the kernel of a complex character; its quotient is cyclic.
The target need not be an involution, and the starting subgroup need not be trivial.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

variable {G : Type*} [CommGroup G] [Finite G]

private theorem exists_maximal_avoiding (K : Subgroup G) (g : G) (hg : g ∉ K) :
    ∃ H : Subgroup G, K ≤ H ∧ g ∉ H ∧
      ∀ L : Subgroup G, H ≤ L → g ∉ L → L = H := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  let S : Finset (Subgroup G) := univ.filter fun H => K ≤ H ∧ g ∉ H
  have hS : S.Nonempty := ⟨K, mem_filter.mpr ⟨mem_univ _, le_rfl, hg⟩⟩
  obtain ⟨H, hH, hmax⟩ := exists_max_image S (fun H => Nat.card H) hS
  have hprop := (mem_filter.mp hH).2
  refine ⟨H, hprop.1, hprop.2, ?_⟩
  intro L hHL hgL
  have hL : L ∈ S := mem_filter.mpr ⟨mem_univ _, hprop.1.trans hHL, hgL⟩
  exact (Subgroup.eq_of_le_of_card_ge hHL (hmax L hL)).symm

private theorem character_of_maximal_avoiding (H : Subgroup G) (g : G)
    (hg : g ∉ H)
    (hmax : ∀ L : Subgroup G, H ≤ L → g ∉ L → L = H) :
    ∃ χ : G →* ℂˣ, χ.ker = H ∧ χ g ≠ 1 ∧ IsCyclic (G ⧸ H) := by
  have hgq : QuotientGroup.mk' H g ≠ 1 := by
    intro h
    exact hg ((QuotientGroup.eq_one_iff g).mp h)
  obtain ⟨ψ, hψ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ H) ℂ hgq
  let χ : G →* ℂˣ := ψ.comp (QuotientGroup.mk' H)
  have hHker : H ≤ χ.ker := by
    intro x hx
    change ψ (QuotientGroup.mk' H x) = 1
    rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]
  have hgker : g ∉ χ.ker := hψ
  have hker : χ.ker = H := hmax χ.ker hHker hgker
  have hψinj : Function.Injective ψ := by
    apply (MonoidHom.ker_eq_bot_iff ψ).mp
    apply le_antisymm _ bot_le
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H z
    apply Subgroup.mem_bot.mpr
    apply (QuotientGroup.eq_one_iff x).mpr
    rw [← hker]
    exact hz
  have hcomplexinj : Function.Injective ((Units.coeHom ℂ).comp ψ) := by
    intro x y h
    exact hψinj (Units.ext h)
  exact ⟨χ, hker, hψ, isCyclic_of_injective_ringHom _ hcomplexinj⟩

/-- A target is already in the starting subgroup, or a maximal avoiding character kernel
contains that subgroup and has cyclic quotient. -/
theorem subgroup_target_or_maximal_character (K : Subgroup G) (g : G) :
    g ∈ K ∨ ∃ χ : G →* ℂˣ, K ≤ χ.ker ∧ χ g ≠ 1 ∧ IsCyclic (G ⧸ χ.ker) ∧
      ∀ L : Subgroup G, χ.ker ≤ L → g ∉ L → L = χ.ker := by
  classical
  by_cases hg : g ∈ K
  · exact Or.inl hg
  obtain ⟨H, hKH, hgH, hmax⟩ := exists_maximal_avoiding K g hg
  obtain ⟨χ, hker, hχ, hcyclic⟩ := character_of_maximal_avoiding H g hgH hmax
  right
  refine ⟨χ, ?_, hχ, ?_, ?_⟩
  · rwa [hker]
  · rwa [hker]
  · simpa only [hker] using hmax

/-- Every subgroup avoiding a target extends to an avoiding subgroup with cyclic quotient. -/
theorem subgroup_target_or_cyclic_quotient (K : Subgroup G) (g : G) :
    g ∈ K ∨ ∃ H : Subgroup G, K ≤ H ∧ g ∉ H ∧ IsCyclic (G ⧸ H) := by
  rcases subgroup_target_or_maximal_character K g with hg | ⟨χ, hK, hχ, hcyclic, _⟩
  · exact Or.inl hg
  · exact Or.inr ⟨χ.ker, hK, hχ, hcyclic⟩

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subgroup_target_or_maximal_character
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subgroup_target_or_cyclic_quotient
