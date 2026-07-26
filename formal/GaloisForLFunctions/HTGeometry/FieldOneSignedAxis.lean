import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Sign.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Signed and band enhancement of the field-one core

The initial band uses the three-element carrier `{0, 1, -1}` rather than the
two-element pointed-monoid core. This file formalizes its balanced null sums,
unique additive inverses, carrier separation, multiplicative collapse, and the
different scalar extensions obtained before and after imposing the null relation.
-/

namespace GaloisForLFunctions.HTGeometry.FieldOneCore

/-- Three-element signed carrier used by the initial band. -/
abbrev SignedFieldOne := SignType

/-- Formal sums of nonzero signs, represented by positive and negative multiplicities. -/
abbrev SignedFormalSum := ℕ × ℕ

/-- Singleton formal sum associated to a sign; zero is the empty sum. -/
def signedSingleton : SignedFieldOne → SignedFormalSum
  | SignType.neg => (0, 1)
  | SignType.zero => (0, 0)
  | SignType.pos => (1, 0)

/-- Balanced signed formal sums form the null set of `F₁±`. -/
def SignedNull (s : SignedFormalSum) : Prop := s.1 = s.2

@[simp]
theorem signedNull_zero : SignedNull (0 : SignedFormalSum) :=
  rfl

/-- The sum of two balanced formal sums is balanced. -/
theorem signedNull_add {s t : SignedFormalSum} (hs : SignedNull s) (ht : SignedNull t) :
    SignedNull (s + t) := by
  exact congrArg₂ (· + ·) hs ht

/-- Multiplication of a formal sum by a sign: zero kills, one fixes, minus one swaps. -/
def signedScalar : SignedFieldOne → SignedFormalSum → SignedFormalSum
  | SignType.neg, (p, n) => (n, p)
  | SignType.zero, _ => (0, 0)
  | SignType.pos, s => s

/-- Balanced sums remain balanced under multiplication by every sign. -/
theorem signedNull_scalar {a : SignedFieldOne} {s : SignedFormalSum}
    (hs : SignedNull s) : SignedNull (signedScalar a s) := by
  rcases s with ⟨p, n⟩
  cases a with
  | neg => exact hs.symm
  | zero => rfl
  | pos => exact hs

/-- Every sign has a unique additive inverse with a null two-term sum. -/
theorem signed_additiveInverse_unique (a : SignedFieldOne) :
    ∃! b : SignedFieldOne, SignedNull (signedSingleton a + signedSingleton b) := by
  refine ⟨-a, ?_, ?_⟩
  · cases a <;> rfl
  · intro b hb
    cases a <;> cases b <;> simp [signedSingleton, SignedNull] at hb ⊢

/-- Multiplicative collapse from the signed carrier to the two-element core. -/
def signedCollapse : SignedFieldOne →*₀ WithZero PUnit where
  toFun s := if s = 0 then 0 else 1
  map_zero' := by simp
  map_one' := by simp
  map_mul' := by
    intro a b
    cases a <;> cases b <;> rfl

/-- A zero-and-one preserving injection from the signed carrier to the two-element
core cannot exist. In particular their pointed-monoid carriers are not isomorphic. -/
theorem no_signed_embedding_into_fieldOne
    (f : SignedFieldOne → WithZero PUnit) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    ¬Function.Injective f := by
  intro hf
  have hcases : f (-1) = 0 ∨ f (-1) = 1 := by
    induction f (-1) using WithZero.recZeroCoe with
    | zero => exact Or.inl rfl
    | coe x =>
        right
        congr
  rcases hcases with h | h
  · have : (-1 : SignedFieldOne) = 0 := hf (h.trans h0.symm)
    simp at this
  · have : (-1 : SignedFieldOne) = 1 := hf (h.trans h1.symm)
    simp at this

/-- No carrier can be equivalent both to the signed base and to the two-element core. -/
theorem no_signed_equiv_fieldOne : ¬Nonempty (SignedFieldOne ≃ WithZero PUnit) := by
  rintro ⟨e⟩
  letI : Fintype (WithZero PUnit) := inferInstanceAs (Fintype (Option PUnit))
  have h := Nat.card_congr e
  have hs : Nat.card SignedFieldOne = 3 :=
    (Nat.card_congr SignType.fin3Equiv.toEquiv).trans (Nat.card_fin 3)
  have hp : Nat.card PUnit = 1 := Nat.card_unique
  have hz : Nat.card (WithZero PUnit) = 2 := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Option PUnit) = 2
    rw [Fintype.card_option, Fintype.card_eq_nat_card, hp]
  omega

/-- Therefore no third carrier can be equivalent to both bases. -/
theorem no_literal_common_carrier (A : Type*)
    (core : A ≃ WithZero PUnit) (signed : A ≃ SignedFieldOne) : False := by
  apply no_signed_equiv_fieldOne
  exact ⟨signed.symm.trans core⟩

/-- Multiplicative-shadow base extension of the signed carrier. -/
abbrev SignedMultiplicativeBaseChange (R : Type*) [CommSemiring R] :=
  MonoidAlgebra R SignedFieldOneˣ

/-- Band base extension imposes the null relation by specializing the sign generator to `-1`. -/
abbrev SignedBandBaseChange (R : Type*) [CommRing R] :=
  Polynomial R ⧸ Ideal.span
    ({Polynomial.X - Polynomial.C (-1)} : Set (Polynomial R))

/-- The signed band base-extends to `R`, unlike its forgotten multiplicative shadow. -/
noncomputable def signedBandBaseChangeEquiv (R : Type*) [CommRing R] :
    SignedBandBaseChange R ≃ₐ[R] R :=
  Polynomial.quotientSpanXSubCAlgEquiv (-1)

/-- The signed generator becomes `-1` after the band null relation is imposed. -/
theorem signedBandGenerator_specializes (R : Type*) [CommRing R] :
    signedBandBaseChangeEquiv R
      (Ideal.Quotient.mk _ (Polynomial.X : Polynomial R)) = -1 := by
  change Polynomial.quotientSpanXSubCAlgEquiv (-1)
    (Ideal.Quotient.mk _ (Polynomial.X : Polynomial R)) = -1
  rw [Polynomial.quotientSpanXSubCAlgEquiv_mk]
  exact Polynomial.eval_X

end GaloisForLFunctions.HTGeometry.FieldOneCore
