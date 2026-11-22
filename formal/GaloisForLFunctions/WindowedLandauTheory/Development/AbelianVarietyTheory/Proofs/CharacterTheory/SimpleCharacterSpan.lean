import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleSubrepresentation
import GaloisForLFunctions.RHTower.Artin.ArtinVirtualCharacterPairing
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero

/-! Virtual characters are spanned over the integers by the simple characters. -/

open GaloisForLFunctions CategoryTheory

namespace GlobalTheory.CuspGL

variable (G : Type) [Group G] [Fintype G]

/-- The characters of simple complex representations of the finite group. -/
def simpleCharacterSet : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ}

private theorem simple_fdRep_of_irreducible {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) :
    Simple (FDRep.of ρ) := by
  letI : ρ.IsIrreducible := h
  have he := representationCharacterPairing_eq_finrank G ρ ρ
  rw [characterPairing, Representation.IsIrreducible.finrank_intertwiningMap_self, Nat.cast_one] at he
  have hc : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [FDRep.simple_iff_char_is_norm_one]
  change ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : ℂ)
  calc
    _ = (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = _ := by rw [he, mul_one]

private theorem character_mem_simple_span (d : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V), Module.finrank ℂ V = d →
      ρ.character ∈ AddSubgroup.closure (simpleCharacterSet G) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro V _ _ _ ρ hdim
    by_cases hd : d = 0
    · rw [hd] at hdim
      letI : Subsingleton V := Module.finrank_zero_iff.mp hdim
      have hzero : ρ.character = 0 := by
        funext g
        change LinearMap.trace ℂ V (ρ g) = 0
        rw [show ρ g = 0 from Subsingleton.elim _ _, map_zero]
      rw [hzero]
      exact zero_mem _
    · letI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by
        rw [hdim]
        exact Nat.pos_of_ne_zero hd)
      obtain ⟨S, hS, hsimple⟩ := exists_irreducible_subrepresentation ρ
      have hχ : S.toRepresentation.character ∈ AddSubgroup.closure (simpleCharacterSet G) :=
        AddSubgroup.subset_closure ⟨FDRep.of S.toRepresentation,
          simple_fdRep_of_irreducible G S.toRepresentation hsimple, rfl⟩
      let Q := ρ.quotient S.toSubmodule (fun g => by
        intro x hx
        exact S.apply_mem_toSubmodule g hx)
      letI : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
      have hSpos : 0 < Module.finrank ℂ S.toSubmodule := Module.finrank_pos
      have hqrank : Module.finrank ℂ (V ⧸ S.toSubmodule) < d := by
        have hr := Submodule.finrank_quotient_add_finrank S.toSubmodule
        omega
      have hQ := ih _ hqrank (V ⧸ S.toSubmodule) Q rfl
      rw [character_add_subrepresentation ρ S]
      exact add_mem hχ hQ

/-- Character additivity and induction on dimension give the integral span. -/
theorem virtualCharacterGroup_eq_simple_span :
    virtualCharacterGroup G = AddSubgroup.closure (simpleCharacterSet G) := by
  unfold virtualCharacterGroup
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro χ ⟨V, rfl⟩
    exact character_mem_simple_span G _ V V.ρ rfl
  · rw [AddSubgroup.closure_le]
    rintro χ ⟨V, _, rfl⟩
    exact AddSubgroup.subset_closure ⟨V, rfl⟩

end GlobalTheory.CuspGL
