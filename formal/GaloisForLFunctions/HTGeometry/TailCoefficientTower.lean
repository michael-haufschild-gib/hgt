import GaloisForLFunctions.HTGeometry.TailCoefficientDegree

/-!
# The coefficient field is exactly the fixed field

The coefficient field sits inside the fixed field of the deck transformations, and the function
field has degree the order of the deck group over that fixed field.  Since the function field has
degree at most that order over the coefficient field, the tower identity leaves no room: the
intermediate step is trivial.

So the coefficient field is the fixed field, and the degree of the parameter field over it is
exactly `n`.  This is the card's parameter change `(10)` in full.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

open scoped IntermediateField

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The fixed field seen as an extension of the coefficient field. -/
noncomputable def deckFixedOverCoeff (K : Type*) [Field K] (n : ℕ) :
    IntermediateField (tailCoeffField K n) (FractionRing (MvPolynomial (Fin n) K)) :=
  IntermediateField.extendScalars (tailCoeffField_le_deckFixedField (K := K) (n := n))

omit [CharZero K] in
theorem mem_deckFixedOverCoeff {x : FractionRing (MvPolynomial (Fin n) K)} :
    x ∈ deckFixedOverCoeff K n ↔ x ∈ deckFixedField K n :=
  IntermediateField.mem_extendScalars _

/-- **The intermediate step of the tower is trivial.** -/
theorem finrank_deckFixedOverCoeff_eq_one (hn : 0 < n) [Fintype (deckGroup K n)]
    (hcard : Fintype.card (deckGroup K n) = n) :
    Module.finrank (tailCoeffField K n) (deckFixedOverCoeff K n) = 1 := by
  haveI := finiteDimensional_tailCoeffField (K := K) (n := n) hn
  have htower : Module.finrank (tailCoeffField K n) (deckFixedOverCoeff K n) *
      Module.finrank (deckFixedOverCoeff K n) (FractionRing (MvPolynomial (Fin n) K)) =
      Module.finrank (tailCoeffField K n) (FractionRing (MvPolynomial (Fin n) K)) :=
    Module.finrank_mul_finrank _ _ _
  have htop : Module.finrank (deckFixedOverCoeff K n)
      (FractionRing (MvPolynomial (Fin n) K)) = n := by
    rw [deckFixedOverCoeff]
    rw [show Module.finrank
        (IntermediateField.extendScalars (tailCoeffField_le_deckFixedField (K := K) (n := n)))
        (FractionRing (MvPolynomial (Fin n) K)) =
        Module.finrank (deckFixedField K n) (FractionRing (MvPolynomial (Fin n) K)) from rfl,
      finrank_deckFixedField, hcard]
  have hle := finrank_tailCoeffField_le (K := K) (n := n) hn
  rw [htop] at htower
  have hpos : 0 < Module.finrank (tailCoeffField K n) (deckFixedOverCoeff K n) :=
    Module.finrank_pos
  have h1 : Module.finrank (tailCoeffField K n) (deckFixedOverCoeff K n) * n ≤ 1 * n := by
    rw [one_mul, htower]
    exact hle
  have h2 := Nat.le_of_mul_le_mul_right h1 hn
  omega

/-- **The coefficient field is the fixed field of the deck transformations.** -/
theorem tailCoeffField_eq_deckFixedField (hn : 0 < n) [Fintype (deckGroup K n)]
    (hcard : Fintype.card (deckGroup K n) = n) :
    tailCoeffField K n = deckFixedField K n := by
  refine le_antisymm (tailCoeffField_le_deckFixedField) (fun x hx => ?_)
  have hbot : deckFixedOverCoeff K n = ⊥ :=
    IntermediateField.finrank_eq_one_iff.1 (finrank_deckFixedOverCoeff_eq_one hn hcard)
  have hmem : x ∈ deckFixedOverCoeff K n := mem_deckFixedOverCoeff.2 hx
  rw [hbot, IntermediateField.mem_bot] at hmem
  obtain ⟨y, rfl⟩ := hmem
  exact y.2

/-- **The parameter field has degree exactly `n` over the coefficient field.** -/
theorem finrank_tailCoeffField (hn : 0 < n) [Fintype (deckGroup K n)]
    (hcard : Fintype.card (deckGroup K n) = n) :
    Module.finrank (tailCoeffField K n) (FractionRing (MvPolynomial (Fin n) K)) = n := by
  haveI := finiteDimensional_tailCoeffField (K := K) (n := n) hn
  have htower : Module.finrank (tailCoeffField K n) (deckFixedOverCoeff K n) *
      Module.finrank (deckFixedOverCoeff K n) (FractionRing (MvPolynomial (Fin n) K)) =
      Module.finrank (tailCoeffField K n) (FractionRing (MvPolynomial (Fin n) K)) :=
    Module.finrank_mul_finrank _ _ _
  have htop : Module.finrank (deckFixedOverCoeff K n)
      (FractionRing (MvPolynomial (Fin n) K)) = n := by
    rw [deckFixedOverCoeff]
    rw [show Module.finrank
        (IntermediateField.extendScalars (tailCoeffField_le_deckFixedField (K := K) (n := n)))
        (FractionRing (MvPolynomial (Fin n) K)) =
        Module.finrank (deckFixedField K n) (FractionRing (MvPolynomial (Fin n) K)) from rfl,
      finrank_deckFixedField, hcard]
  rw [finrank_deckFixedOverCoeff_eq_one hn hcard, htop, one_mul] at htower
  exact htower.symm

end GaloisForLFunctions.HTGeometry
