import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rationally independent integer generators of a finitely generated subgroup of `ℝ`

A finitely generated subgroup of `ℝ` is torsion free, hence free of finite rank over `ℤ`, and any
`ℤ`-basis of it is automatically `ℚ`-linearly independent inside `ℝ`.  So every finite set of real
numbers is contained in the integer span of finitely many rationally independent reals taken from
the group it generates.

This reduces statements about arbitrary finite frequency sets — where relations are allowed — to the
rationally independent case, in which Kronecker's theorem applies.
-/

open Finset

namespace GaloisForLFunctions

/-- A finite set of reals is contained in the integer span of finitely many rationally independent
reals drawn from the group it generates. -/
theorem exists_rat_independent_intSpanning (F : Finset ℝ) :
    ∃ (k : ℕ) (b : Fin k → ℝ), LinearIndependent ℚ b ∧
      (∀ i, b i ∈ AddSubgroup.closure (F : Set ℝ)) ∧
      ∀ γ ∈ F, ∃ n : Fin k → ℤ, γ = ∑ i, (n i : ℝ) * b i := by
  classical
  haveI hFG : AddGroup.FG (AddSubgroup.closure (F : Set ℝ)) := AddGroup.closure_finset_fg F
  haveI : Module.Free ℤ (AddSubgroup.closure (F : Set ℝ)) := Module.free_of_finite_type_torsion_free'
  set ι := Module.Free.ChooseBasisIndex ℤ (AddSubgroup.closure (F : Set ℝ)) with hιdef
  haveI : Fintype ι := inferInstance
  set bG : Module.Basis ι ℤ (AddSubgroup.closure (F : Set ℝ)) :=
    Module.Free.chooseBasis ℤ (AddSubgroup.closure (F : Set ℝ)) with hbG
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hedef
  refine ⟨Fintype.card ι, fun i => ((bG (e i) : AddSubgroup.closure (F : Set ℝ)) : ℝ), ?_, ?_, ?_⟩
  · rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
    have h1 : LinearIndependent ℤ (fun i => bG (e i)) :=
      (bG.linearIndependent).comp e e.injective
    have h2 : LinearMap.ker
        ((AddSubgroup.closure (F : Set ℝ)).subtype.toIntLinearMap) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      exact Subtype.ext hxy
    exact h1.map' _ h2
  · intro i
    exact (bG (e i)).2
  · intro γ hγ
    have hγG : γ ∈ AddSubgroup.closure (F : Set ℝ) := AddSubgroup.subset_closure hγ
    refine ⟨fun i => bG.repr ⟨γ, hγG⟩ (e i), ?_⟩
    calc γ = ((∑ j : ι, bG.repr ⟨γ, hγG⟩ j • bG j :
              AddSubgroup.closure (F : Set ℝ)) : ℝ) := by rw [bG.sum_repr]
      _ = ∑ j : ι, ((bG.repr ⟨γ, hγG⟩ j : ℤ) : ℝ)
            * ((bG j : AddSubgroup.closure (F : Set ℝ)) : ℝ) := by
          push_cast
          simp [zsmul_eq_mul]
      _ = ∑ i : Fin (Fintype.card ι), ((bG.repr ⟨γ, hγG⟩ (e i) : ℤ) : ℝ)
            * ((bG (e i) : AddSubgroup.closure (F : Set ℝ)) : ℝ) :=
          (Equiv.sum_comp e _).symm

end GaloisForLFunctions
