import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Irreducible

/-! A cuspidal finite character is realized by a simple
representation. Its invariant subspaces are therefore trivial. -/

noncomputable section

open CategoryTheory Representation

namespace GlobalTheory.GLq

variable {p n : ℕ} [Fact p.Prime]

theorem isIrreducible_of_isCusp_character (τ : FDRep ℂ (Gn p n)) (hτ : IsCusp τ.character) :
    IsIrreducible τ.ρ := by
  haveI : Simple τ := by
    obtain ⟨S, hS, hchar⟩ := hτ.2.1
    rw [FDRep.simple_iff_char_is_norm_one] at hS ⊢
    simpa only [hchar] using hS
  letI : Nontrivial τ := by
    by_contra h
    letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp h
    have he : (𝟙 τ : τ ⟶ τ) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero τ he
  letI : Nontrivial (Subrepresentation τ.ρ) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun U => ?_⟩
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  let S := FDRep.of U.toRepresentation
  let i : S ⟶ τ := ⟨FGModuleCat.ofHom U.toSubmodule.subtype, fun _ => rfl⟩
  haveI : Mono i := ⟨fun f g e => by
    ext x
    exact congrArg (fun h => h.hom.hom.hom x) e⟩
  have he : U.toSubmodule ≠ ⊥ := fun h => hU (Subrepresentation.toSubmodule_injective h)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
  have hi : i ≠ 0 := fun h => hu0 (congrArg (fun f : S ⟶ τ => f.hom.hom.hom ⟨u, hu⟩) h)
  letI : IsIso i := isIso_of_mono_of_nonzero hi
  apply Subrepresentation.toSubmodule_injective
  apply eq_top_iff.mpr
  intro x _
  let e := FDRep.isoToLinearEquiv (asIso i)
  exact (show (e (e.symm x)) ∈ U.toSubmodule from (e.symm x).2) |> fun h => e.apply_symm_apply x ▸ h

end GlobalTheory.GLq

#print axioms GlobalTheory.GLq.isIrreducible_of_isCusp_character
