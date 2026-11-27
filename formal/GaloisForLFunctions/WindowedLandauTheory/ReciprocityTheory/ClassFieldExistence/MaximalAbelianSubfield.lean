import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.GroupTheory.Abelianization.Defs

/-! The Galois group of the maximal abelian subextension is the
abelianization of the full Galois group. -/

noncomputable section

open IntermediateField

namespace GlobalTheory.Reciprocity

variable (K M : Type*) [Field K] [Field M] [Algebra K M]

/-- The fixed field of the commutator subgroup. -/
def maxAbelian : IntermediateField K M := fixedField (commutator Gal(M/K))

variable [FiniteDimensional K M] [IsGalois K M]

instance isGalois_maxAbelian : IsGalois K (maxAbelian K M) :=
  IsGalois.of_fixedField_normal_subgroup _

instance isMulCommutative_maxAbelian : IsMulCommutative Gal(maxAbelian K M/K) := by
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  let e : Gal(M/K) ⧸ commutator Gal(M/K) ≃* Gal(maxAbelian K M/K) :=
    IsGalois.normalAutEquivQuotient (commutator Gal(M/K))
  obtain ⟨a, rfl⟩ := e.surjective σ
  obtain ⟨b, rfl⟩ := e.surjective τ
  rw [← map_mul, ← map_mul]
  exact congrArg e (mul_comm (G := Abelianization Gal(M/K)) a b)

instance isAbelianGalois_maxAbelian : IsAbelianGalois K (maxAbelian K M) where

/-- The degree of the maximal abelian subextension is the order of the
abelianized Galois group. -/
theorem finrank_maxAbelian :
    Module.finrank K (maxAbelian K M) = Nat.card (Abelianization Gal(M/K)) := by
  have h1 := Module.finrank_mul_finrank K (maxAbelian K M) M
  rw [maxAbelian, finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M,
    ← (commutator Gal(M/K)).card_mul_index] at h1
  have hpos : 0 < Nat.card (commutator Gal(M/K)) := Nat.card_pos
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

end GlobalTheory.Reciprocity
