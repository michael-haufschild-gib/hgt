import GaloisForLFunctions.HTGeometry.TorusCharacterCoLie
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Localization.Module

/-!
# Independent integral bases for finite character packets

A finite packet of integral character vectors generates a finitely generated torsion-free abelian
group.  A `ℤ`-basis of that group consists of actual integral character vectors and becomes
linearly independent over `ℚ` after coordinatewise scalar extension.
-/

namespace GaloisForLFunctions.HTGeometry
namespace IntegralLatticeBasis

open TorusCharacterCoLie

/-- A finite packet of integral character vectors is integrally spanned by a rationally independent
family drawn from the subgroup it generates. -/
theorem exists_integralLatticeBasis_of_finset {n : ℕ}
    (S : Finset (Fin n →₀ ℤ)) :
    ∃ (r : ℕ) (m : Fin r → (Fin n →₀ ℤ)),
      LinearIndependent ℚ (fun j => integralCast ℚ (m j)) ∧
      (∀ j, m j ∈ AddSubgroup.closure (S : Set (Fin n →₀ ℤ))) ∧
      ∀ s ∈ S, ∃ a : Fin r → ℤ, s = ∑ j, a j • m j := by
  classical
  let G := AddSubgroup.closure (S : Set (Fin n →₀ ℤ))
  haveI hFG : AddGroup.FG G := AddGroup.closure_finset_fg S
  haveI : Module.Free ℤ G := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ G
  haveI : Fintype ι := inferInstance
  let b : Module.Basis ι ℤ G := Module.Free.chooseBasis ℤ G
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let m : Fin (Fintype.card ι) → (Fin n →₀ ℤ) := fun j => (b (e j) : G)
  refine ⟨Fintype.card ι, m, ?_, ?_, ?_⟩
  · rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
    have hb : LinearIndependent ℤ (fun j => b (e j)) :=
      b.linearIndependent.comp e e.injective
    let f : G →ₗ[ℤ] (Fin n → ℚ) :=
      (integralCast ℚ).toIntLinearMap.comp (AddSubgroup.subtype G).toIntLinearMap
    have hf : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply Subtype.ext
      ext i
      have hi := congrFun hxy i
      change ((x.1 i : ℤ) : ℚ) = ((y.1 i : ℤ) : ℚ) at hi
      exact_mod_cast hi
    have hmapped := hb.map' f hf
    simpa [Function.comp_def, f, m] using hmapped
  · intro j
    exact (b (e j)).2
  · intro s hs
    have hsG : s ∈ G := AddSubgroup.subset_closure hs
    refine ⟨fun j => b.repr ⟨s, hsG⟩ (e j), ?_⟩
    dsimp only [m]
    calc
      s = ((∑ q : ι, b.repr ⟨s, hsG⟩ q • b q : G) : Fin n →₀ ℤ) := by
        exact congrArg Subtype.val (b.sum_repr ⟨s, hsG⟩).symm
      _ = ∑ q : ι, b.repr ⟨s, hsG⟩ q • ((b q : G) : Fin n →₀ ℤ) := by
        change (AddSubgroup.subtype G) (∑ q : ι, b.repr ⟨s, hsG⟩ q • b q) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro q _
        rfl
      _ = ∑ j : Fin (Fintype.card ι),
          b.repr ⟨s, hsG⟩ (e j) • ((b (e j) : G) : Fin n →₀ ℤ) :=
        (Equiv.sum_comp e _).symm

end IntegralLatticeBasis
end GaloisForLFunctions.HTGeometry
