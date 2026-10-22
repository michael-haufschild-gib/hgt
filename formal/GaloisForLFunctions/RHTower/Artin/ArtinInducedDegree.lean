import GaloisForLFunctions.RHTower.Artin.ArtinCharacterMultiplicity
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Degree of an induced Artin character

This module identifies the carrier of a coinduced representation with one copy of the original
carrier for each right coset. Combining this concrete equivalence with finite-index
induction--coinduction gives the dimension formula

`dim (Ind_H^G ρ) = [G : H] * dim ρ`.

At the identity, the same formula computes the degree of an induced character. In particular,
every monomial character induced from a one-dimensional character has degree `[G : H]`.
-/

open scoped Classical

noncomputable section

universe u w

namespace GaloisForLFunctions

open Representation

variable {G : Type u} [Group G]
variable (H : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ H V)

private def rightCoset (g : G) : Quotient (QuotientGroup.rightRel H) :=
  Quotient.mk (QuotientGroup.rightRel H) g

private noncomputable def rightCosetRepresentative
    (q : Quotient (QuotientGroup.rightRel H)) : G :=
  q.out

private theorem mk_rightCosetRepresentative
    (q : Quotient (QuotientGroup.rightRel H)) :
    rightCoset H (rightCosetRepresentative H q) = q :=
  Quotient.out_eq q

private noncomputable def rightCosetMultiplier (g : G) : H :=
  ⟨g * (rightCosetRepresentative H (rightCoset H g))⁻¹,
    QuotientGroup.rightRel_apply.mp <|
      Quotient.mk_out (s := QuotientGroup.rightRel H) g⟩

private theorem mk_rightCoset_mul (s : H) (g : G) :
    rightCoset H (H.subtype s * g) = rightCoset H g := by
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr (by simp)

private theorem rightCosetMultiplier_mul (s : H) (g : G) :
    rightCosetMultiplier H (H.subtype s * g) =
      s * rightCosetMultiplier H g := by
  apply Subtype.ext
  change
    H.subtype s * g *
        (rightCosetRepresentative H (rightCoset H (H.subtype s * g)))⁻¹ =
      H.subtype s *
        (g * (rightCosetRepresentative H (rightCoset H g))⁻¹)
  rw [mk_rightCoset_mul]
  simp [mul_assoc]

private theorem rightCosetMultiplier_representative
    (q : Quotient (QuotientGroup.rightRel H)) :
    rightCosetMultiplier H (rightCosetRepresentative H q) = 1 := by
  ext
  simp [rightCosetMultiplier, mk_rightCosetRepresentative]

/-- Evaluation on right-coset representatives identifies a coinduced representation's carrier
with one copy of the original carrier for each right coset. -/
noncomputable def coinducedRightCosetEquiv :
    coindV H.subtype ρ ≃ₗ[ℂ]
      (Quotient (QuotientGroup.rightRel H) → V) where
  toFun f q := f.1 (rightCosetRepresentative H q)
  invFun a :=
    ⟨fun g => ρ (rightCosetMultiplier H g) (a (rightCoset H g)), by
      rw [mem_coindV]
      intro s g
      rw [mk_rightCoset_mul, rightCosetMultiplier_mul]
      have hmap := congrArg
        (fun T : V →ₗ[ℂ] V => T (a (rightCoset H g)))
        (ρ.map_mul s (rightCosetMultiplier H g))
      exact hmap⟩
  map_add' f₁ f₂ := by
    funext q
    rfl
  map_smul' c f := by
    funext q
    rfl
  left_inv f := by
    apply Subtype.ext
    funext g
    have hf := (mem_coindV H.subtype ρ f.1).mp f.2
      (rightCosetMultiplier H g) (rightCosetRepresentative H (rightCoset H g))
    have hprod :
        ((rightCosetMultiplier H g : H) : G) *
            rightCosetRepresentative H (rightCoset H g) = g := by
      simp [rightCosetMultiplier, mul_assoc]
    change f.1 (((rightCosetMultiplier H g : H) : G) *
        rightCosetRepresentative H (rightCoset H g)) = _ at hf
    rw [hprod] at hf
    exact hf.symm
  right_inv a := by
    funext q
    change
      ρ (rightCosetMultiplier H (rightCosetRepresentative H q))
          (a (rightCoset H (rightCosetRepresentative H q))) = a q
    rw [mk_rightCosetRepresentative, rightCosetMultiplier_representative]
    simp

/-- A finite-group coinduced representation has one copy of the original carrier per coset. -/
theorem coinduced_finrank_eq_index_mul [Fintype G] [FiniteDimensional ℂ V] :
    Module.finrank ℂ (coindV H.subtype ρ) =
      H.index * Module.finrank ℂ V := by
  letI : H.FiniteIndex := by infer_instance
  letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel H)) :=
    QuotientGroup.fintypeQuotientRightRel
  have hcard :
      Fintype.card (Quotient (QuotientGroup.rightRel H)) = H.index := by
    calc
      Fintype.card (Quotient (QuotientGroup.rightRel H)) =
          Fintype.card (G ⧸ H) := QuotientGroup.card_quotient_rightRel H
      _ = Nat.card (G ⧸ H) := Nat.card_eq_fintype_card.symm
      _ = H.index := (Subgroup.index_eq_card H).symm
  rw [(coinducedRightCosetEquiv H ρ).finrank_eq,
    Module.finrank_pi_fintype]
  simp [hcard]

private noncomputable def inducedCoinducedLinearEquiv [Fintype G] :
    IndV H.subtype ρ ≃ₗ[ℂ] coindV H.subtype ρ := by
  letI : H.FiniteIndex := by infer_instance
  letI : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  exact (Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ))).toLinearEquiv

/-- Degree formula for induction from a subgroup of a finite group. -/
theorem induced_finrank_eq_index_mul [Fintype G] [FiniteDimensional ℂ V] :
    Module.finrank ℂ (IndV H.subtype ρ) =
      H.index * Module.finrank ℂ V := by
  rw [(inducedCoinducedLinearEquiv H ρ).finrank_eq,
    coinduced_finrank_eq_index_mul]

/-- The value at the identity of an induced character is subgroup index times source degree. -/
theorem induced_character_one_eq_index_mul [Fintype G]
    [FiniteDimensional ℂ V] :
    (Representation.ind H.subtype ρ).character 1 =
      (H.index * Module.finrank ℂ V : ℕ) := by
  rw [Representation.char_one, induced_finrank_eq_index_mul]

/-- A genuine monomial character induced from a linear character has degree `[G : H]`. -/
@[simp]
theorem monomialGenuineCharacter_one_eq_index [Fintype G]
    (χ : LinearCharacter H) :
    (monomialGenuineCharacter G H χ).val 1 = H.index := by
  rw [monomialGenuineCharacter_apply,
    induced_character_one_eq_index_mul]
  simp

/-- The virtual character underlying a monomial character has degree `[G : H]`. -/
@[simp]
theorem monomialVirtualCharacter_one_eq_index [Fintype G]
    (χ : LinearCharacter H) :
    (monomialVirtualCharacter G H χ).val 1 = H.index := by
  rw [monomialVirtualCharacter_apply,
    induced_character_one_eq_index_mul]
  simp

end GaloisForLFunctions
