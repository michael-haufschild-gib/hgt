import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! Surjective reparameterization preserves irreducibility because
it gives exactly the same invariant subspaces. -/

noncomputable section

namespace Representation

variable {G H V : Type*} [Monoid G] [Monoid H] [AddCommGroup V] [Module ℂ V]

theorem irreducible_comp_of_surjective
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (f : H →* G) (hf : Function.Surjective f) :
    IsIrreducible (ρ.comp f) := by
  letI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  letI : Nontrivial (Subrepresentation (ρ.comp f)) :=
    ⟨⊥, ⊤, fun he => bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩
  refine ⟨fun U => ?_⟩
  let W : Subrepresentation ρ :=
    ⟨U.toSubmodule, fun g {v} hv => by
      obtain ⟨h, rfl⟩ := hf g
      exact U.apply_mem_toSubmodule h hv⟩
  rcases eq_bot_or_eq_top W with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) hb
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) ht

end Representation

#print axioms Representation.irreducible_comp_of_surjective
