import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleSubrepresentation
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.FDRep

/-! A nonzero complex representation of a finite group contains a
finite-dimensional irreducible subrepresentation inside the span
of any nonzero orbit. -/

noncomputable section

namespace Representation

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] [Nontrivial V]

theorem exists_fd_irreducible_embedding (ρ : Representation ℂ G V) :
    ∃ τ : FDRep ℂ G, IsIrreducible τ.ρ ∧
      ∃ j : IntertwiningMap τ.ρ ρ, Function.Injective j := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let orbit := Set.range fun g : G => ρ g v
  let X : Subrepresentation ρ :=
    ⟨Submodule.span ℂ orbit, fun g {x} hx => by
      have hmap : (Submodule.span ℂ orbit).map (ρ g) ≤ Submodule.span ℂ orbit := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
        refine ⟨g * h, ?_⟩
        change ρ (g * h) v = ρ g (ρ h v)
        rw [map_mul, Module.End.mul_apply]
      exact hmap ⟨x, hx, rfl⟩⟩
  have hvX : v ∈ X.toSubmodule := Submodule.subset_span ⟨1, by
    change ρ 1 v = v
    rw [map_one, Module.End.one_apply]⟩
  letI : Nontrivial X.toSubmodule := ⟨⟨v, hvX⟩, 0, fun h => hv (congrArg Subtype.val h)⟩
  letI : FiniteDimensional ℂ X.toSubmodule :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range fun g : G => ρ g v)
  obtain ⟨S, -, hS⟩ := GlobalTheory.CuspGL.exists_irreducible_subrepresentation X.toRepresentation
  let j : S.toSubmodule →ₗ[ℂ] V := X.toSubmodule.subtype.comp S.toSubmodule.subtype
  have hj : Function.Injective j := X.toSubmodule.injective_subtype.comp S.toSubmodule.injective_subtype
  exact ⟨FDRep.of S.toRepresentation, hS, ⟨j, fun _ => rfl⟩, hj⟩

end Representation

#print axioms Representation.exists_fd_irreducible_embedding
