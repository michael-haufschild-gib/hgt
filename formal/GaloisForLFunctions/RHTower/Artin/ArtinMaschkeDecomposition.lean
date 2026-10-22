import GaloisForLFunctions.RHTower.Artin.ArtinVirtualCharacter
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Maschke decomposition for finite-group Artin representations

This file exposes the actual semisimple carrier supplied by Maschke's theorem: a finite-dimensional
complex representation of a finite group is an actual finite direct sum of simple group-algebra
submodules.  It deliberately stops before identifying these summands with irreducible characters
or proving any form of Brauer induction.
-/

open scoped MonoidAlgebra DirectSum

noncomputable section

universe u v

namespace GaloisForLFunctions

variable {G : Type u} [Group G]

section ModuleRepresentation

variable {M : Type v} [AddCommGroup M] [Module ℂ[G] M]

/-- The complex representation carried by an actual `ℂ[G]`-module, with the scalar structure
made explicit so no ambient instance is postulated. -/
noncomputable def groupAlgebraModuleRepresentation (M : Type v) [AddCommGroup M] [Module ℂ[G] M] :
    @Representation ℂ G (RestrictScalars ℂ ℂ[G] M)
      _ _ _ (RestrictScalars.module (R := ℂ) (S := ℂ[G]) (M := M)) :=
  Representation.ofModule (k := ℂ) (G := G) M

/-- An actual `ℂ[G]`-module is simple exactly when its concrete associated representation is
irreducible. -/
theorem groupAlgebraModuleRepresentation_isIrreducible_iff (M : Type v)
    [AddCommGroup M] [Module ℂ[G] M] :
    @Representation.IsIrreducible G ℂ (RestrictScalars ℂ ℂ[G] M)
      _ _ _ (RestrictScalars.module (R := ℂ) (S := ℂ[G]) (M := M))
      (groupAlgebraModuleRepresentation (G := G) M) ↔ IsSimpleModule ℂ[G] M := by
  exact (Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ) (G := G) M).symm

end ModuleRepresentation

section FiniteGroup

variable [Fintype G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Every finite-dimensional complex representation of a finite group is an actual finite direct
sum of simple `ℂ[G]`-submodules. -/
theorem finiteGroup_exists_simpleModule_decomposition
    (ρ : Representation ℂ G V) :
    ∃ (n : ℕ) (S : Fin n → Submodule ℂ[G] ρ.asModule)
      (_ : ρ.asModule ≃ₗ[ℂ[G]] Π₀ i : Fin n, S i),
      ∀ i, IsSimpleModule ℂ[G] (S i) := by
  letI : Module.Finite ℂ ρ.asModule := by infer_instance
  letI : Module.Finite ℂ[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℂ ℂ[G] ρ.asModule
  letI : Representation.IsSemisimpleRepresentation ρ := by infer_instance
  letI : IsSemisimpleModule ℂ[G] ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp inferInstance
  exact IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[G] ρ.asModule

/-- Maschke summands carry concrete irreducible complex representations via the actual group
algebra action. -/
theorem finiteGroup_exists_irreducibleModule_decomposition
    (ρ : Representation ℂ G V) :
    ∃ (n : ℕ) (S : Fin n → Submodule ℂ[G] ρ.asModule)
      (_ : ρ.asModule ≃ₗ[ℂ[G]] Π₀ i : Fin n, S i),
      ∀ i,
        @Representation.IsIrreducible G ℂ (RestrictScalars ℂ ℂ[G] (S i))
          _ _ _ (RestrictScalars.module (R := ℂ) (S := ℂ[G]) (M := S i))
          (groupAlgebraModuleRepresentation (G := G) (S i)) := by
  obtain ⟨n, S, e, hS⟩ := finiteGroup_exists_simpleModule_decomposition ρ
  exact ⟨n, S, e, fun i =>
    (groupAlgebraModuleRepresentation_isIrreducible_iff (G := G) (S i)).mpr (hS i)⟩

end FiniteGroup

end GaloisForLFunctions
