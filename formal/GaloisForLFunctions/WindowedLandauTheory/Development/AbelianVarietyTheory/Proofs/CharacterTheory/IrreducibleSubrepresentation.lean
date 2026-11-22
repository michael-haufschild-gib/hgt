import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantCharpolyBlocks
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible

/-! Irreducible subrepresentations and the character of the corresponding quotient. -/

namespace GlobalTheory.CuspGL

variable {F G V : Type} [Field F] [Group G] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A nonzero subrepresentation of least dimension is irreducible. -/
theorem exists_irreducible_subrepresentation [Nontrivial V] (ρ : Representation F G V) :
    ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧ S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ d : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank F S.toSubmodule = d :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hd⟩ := Nat.find_spec hex
  have hmin (T : Subrepresentation ρ) (hT : T.toSubmodule ≠ ⊥) :
      Module.finrank F S.toSubmodule ≤ Module.finrank F T.toSubmodule := by
    rw [hd]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  letI : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  letI : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have he : (⊥ : Submodule F S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top he⟩
  refine ⟨S, hS, ⟨fun T => ?_⟩⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      change T.toSubmodule.map S.toSubmodule.subtype = ⊥ at h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h
    have hrank := hmin T' hT'
    change Module.finrank F S.toSubmodule ≤
      Module.finrank F (T.toSubmodule.map S.toSubmodule.subtype) at hrank
    rw [Submodule.finrank_map_subtype_eq] at hrank
    exact Subrepresentation.toSubmodule_injective
      (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hrank))

/-- Trace additivity on an invariant subspace and its quotient gives character additivity. -/
theorem character_add_subrepresentation (ρ : Representation F G V) (S : Subrepresentation ρ) :
    ρ.character = S.toRepresentation.character +
      (ρ.quotient S.toSubmodule (fun g => by
        intro x hx
        exact S.apply_mem_toSubmodule g hx)).character := by
  funext g
  exact trace_eq_restrict_add_mapQ S.toSubmodule (ρ g) (fun _ hx => S.apply_mem_toSubmodule g hx)

end GlobalTheory.CuspGL
