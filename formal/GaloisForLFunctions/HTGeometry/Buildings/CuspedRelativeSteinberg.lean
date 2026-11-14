import GaloisForLFunctions.HTGeometry.Buildings.RelativeCone
import GaloisForLFunctions.HTGeometry.CuspedSteinberg

/-!
# Relative chains for the all-depth cusped building

The cone-pair comparison carries the all-depth cusped building to the
Steinberg homology of the dual vector space. Consequently the additional
cusp depths preserve the same free top classes in a relative-chain model.
This combines the contractible-pair construction of Ash--Gunnells,
arXiv:2611.03303, §3, with the cusp retraction and annihilator correspondence.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Module

universe v u

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [DecidableEq (Submodule K V)]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- Relative homology of the cusped cone is dual-building homology shifted by one. -/
noncomputable def cuspRelativeDualHomologyIso (R : C) (n : ℕ) :
    (orderConeRelativeChains (CuspedVertex K V) R).homology (n + 2) ≅
      (nerve (properPart (Submodule K (Dual K V)))).homology R (n + 1) :=
  orderConeRelativeHomologyIso (CuspedVertex K V) R n ≪≫ cuspDualHomologyIso R (n + 1)

/-- Every positive-base-degree relative cusp homology object is free, also for the zero space. -/
theorem isFreeOver_cuspRelativeHomology (R : C) (n : ℕ) :
    IsFreeOver.{v, u, u} R ((orderConeRelativeChains (CuspedVertex K V) R).homology (n + 2)) := by
  apply IsFreeOver.of_iso _ (cuspRelativeDualHomologyIso R n)
  rcases subsingleton_or_nontrivial (Dual K V) with h | h
  · haveI : SSet.HasDimensionLT (nerve (properPart (Submodule K (Dual K V)))) 0 :=
      hasDimensionLT_nerve_of_chain_bound 0 (fun _ f _ =>
        False.elim ((ne_of_gt (f 0).property.1) (Subsingleton.elim _ _)))
    exact IsFreeOver.of_isZero (isZero_homology_of_hasDimensionLT _ 0 R (n + 1) (Nat.zero_le _))
  · exact isFreeOver_homology_properPart_submodule R (n + 1)

/-- Cusp depths introduce no additional positive relative homology degrees. -/
theorem cuspRelativeHomology_support (R : C) (n : ℕ) :
    n + 1 = finrank K V - 2 ∨
      IsZero ((orderConeRelativeChains (CuspedVertex K V) R).homology (n + 2)) := by
  by_cases ht : n + 1 = finrank K V - 2
  · exact Or.inl ht
  right
  apply IsZero.of_iso _ (cuspRelativeDualHomologyIso R n)
  rcases subsingleton_or_nontrivial (Dual K V) with h | h
  · haveI : SSet.HasDimensionLT (nerve (properPart (Submodule K (Dual K V)))) 0 :=
      hasDimensionLT_nerve_of_chain_bound 0 (fun _ f _ =>
        False.elim ((ne_of_gt (f 0).property.1) (Subsingleton.elim _ _)))
    exact isZero_homology_of_hasDimensionLT _ 0 R (n + 1) (Nat.zero_le _)
  · exact isZero_homology_properPart_submodule_of_ne R (n + 1) (by omega)
      (by simpa only [Subspace.dual_finrank_eq] using ht)

/-- In dimension at least three, the cusp relative top class is the dual Steinberg module. -/
noncomputable def cuspRelativeSteinbergIso (R : C) (h : 3 ≤ finrank K V) :
    (orderConeRelativeChains (CuspedVertex K V) R).homology (finrank K V - 1) ≅
      steinbergModule K (Dual K V) R := by
  have h₁ : finrank K V - 1 = (finrank K V - 3) + 2 := by omega
  have h₂ : (finrank K V - 3) + 1 = finrank K (Dual K V) - 2 := by
    rw [Subspace.dual_finrank_eq]
    omega
  exact eqToIso (congrArg (fun n =>
      (orderConeRelativeChains (CuspedVertex K V) R).homology n) h₁)
    ≪≫ cuspRelativeDualHomologyIso R (finrank K V - 3)
    ≪≫ eqToIso (congrArg (fun n =>
      (nerve (properPart (Submodule K (Dual K V)))).homology R n) h₂)

/-- Relative cone chains retain a nonzero cusp Steinberg class for nonzero coefficients. -/
theorem not_isZero_cuspRelativeHomology_top (R : C) (hR : ¬ IsZero R)
    (h : 3 ≤ finrank K V) :
    ¬ IsZero ((orderConeRelativeChains (CuspedVertex K V) R).homology (finrank K V - 1)) := by
  intro hz
  have hdim : 3 ≤ finrank K (Dual K V) := by simpa only [Subspace.dual_finrank_eq] using h
  exact not_isZero_steinbergModule R hR hdim
    (IsZero.of_iso hz (cuspRelativeSteinbergIso R h).symm)

end GaloisForLFunctions.HTGeometry
