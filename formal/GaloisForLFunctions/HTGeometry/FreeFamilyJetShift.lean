import GaloisForLFunctions.HTGeometry.FreeCoordinateChainRule
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# The free differential rational field on a family of indeterminates

`FreeCoordinateRationalField C (ι × ℕ)` carries the jet-shift derivation `x_a^{(m)} ↦ x_a^{(m+1)}`.
With it the coordinate `x_a = x_a^{(0)}` has `differentialJet m x_a = x_a^{(m)}`, so the field is
the free differential rational field `C⟨x_a : a ∈ ι⟩`.

This is the family counterpart of the single-generator `FreeScalarJetField`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial
open scoped Differential

/-- The polynomial algebra on a family of complete jets. -/
abbrev FreeFamilyJetPolynomial (C ι : Type*) [Field C] := MvPolynomial (ι × ℕ) C

/-- The free differential rational field on the family `x_a`, `a ∈ ι`. -/
abbrev FreeFamilyJetField (C ι : Type*) [Field C] := FreeCoordinateRationalField C (ι × ℕ)

/-- The total-derivative shift on the polynomial family jet: `x_a^{(m)}` goes to `x_a^{(m+1)}`. -/
def freeFamilyJetShiftPolynomialDerivation (C ι : Type*) [Field C] :
    Derivation C (FreeFamilyJetPolynomial C ι) (FreeFamilyJetPolynomial C ι) :=
  MvPolynomial.mkDerivation C fun p : ι × ℕ => MvPolynomial.X (p.1, p.2 + 1)

@[simp]
theorem freeFamilyJetShiftPolynomialDerivation_X {C ι : Type*} [Field C] (p : ι × ℕ) :
    freeFamilyJetShiftPolynomialDerivation C ι (MvPolynomial.X p) =
      MvPolynomial.X (p.1, p.2 + 1) := by
  simp [freeFamilyJetShiftPolynomialDerivation]

/-- The total derivative on the free family jet field. -/
def freeFamilyJetShift (C ι : Type*) [Field C] :
    Derivation C (FreeFamilyJetField C ι) (FreeFamilyJetField C ι) :=
  extendFreeCoordinatePolynomialDerivation (freeFamilyJetShiftPolynomialDerivation C ι)

@[simp]
theorem freeFamilyJetShift_algebraMap {C ι : Type*} [Field C]
    (P : FreeFamilyJetPolynomial C ι) :
    freeFamilyJetShift C ι
        (algebraMap (FreeFamilyJetPolynomial C ι) (FreeFamilyJetField C ι) P) =
      algebraMap (FreeFamilyJetPolynomial C ι) (FreeFamilyJetField C ι)
        (freeFamilyJetShiftPolynomialDerivation C ι P) :=
  extendFreeCoordinatePolynomialDerivation_algebraMap _ P

@[simp]
theorem freeFamilyJetShift_freeCoordinate {C ι : Type*} [Field C] (p : ι × ℕ) :
    freeFamilyJetShift C ι (freeCoordinate C (ι × ℕ) p) =
      freeCoordinate C (ι × ℕ) (p.1, p.2 + 1) := by
  rw [freeCoordinate, freeFamilyJetShift_algebraMap,
    freeFamilyJetShiftPolynomialDerivation_X]
  rfl

/-- The jet-shift derivation as the differential structure of the family jet field. -/
noncomputable instance freeFamilyJetFieldDifferential (C ι : Type*) [Field C] :
    Differential (FreeFamilyJetField C ι) := by
  letI : Algebra ℤ (FreeFamilyJetField C ι) := Ring.toIntAlgebra _
  exact ⟨(freeFamilyJetShift C ι).restrictScalars ℤ⟩

@[simp]
theorem freeFamilyJetField_deriv_apply {C ι : Type*} [Field C] (f : FreeFamilyJetField C ι) :
    f′ = freeFamilyJetShift C ι f := rfl

/-- The `m`-th jet of the `a`-th free family generator. -/
def familyJet (C : Type*) {ι : Type*} [Field C] (a : ι) (m : ℕ) : FreeFamilyJetField C ι :=
  freeCoordinate C (ι × ℕ) (a, m)

@[simp]
theorem familyJet_deriv {C ι : Type*} [Field C] (a : ι) (m : ℕ) :
    (familyJet C a m)′ = familyJet C a (m + 1) := by
  rw [familyJet, freeFamilyJetField_deriv_apply, freeFamilyJetShift_freeCoordinate]
  rfl

@[simp]
theorem freeFamilyJetShift_familyJet {C ι : Type*} [Field C] (a : ι) (m : ℕ) :
    freeFamilyJetShift C ι (familyJet C a m) = familyJet C a (m + 1) := by
  rw [← freeFamilyJetField_deriv_apply, familyJet_deriv]

/-- The differential jets of a family generator are exactly its free coordinates. -/
@[simp]
theorem differentialJet_familyJet_zero {C ι : Type*} [Field C] (a : ι) (m : ℕ) :
    differentialJet m (familyJet C a 0) = familyJet C a m := by
  induction m with
  | zero => simp
  | succ m ih => rw [differentialJet_succ, ih, familyJet_deriv]

/-- Every free family coordinate is nonzero. -/
theorem familyJet_ne_zero {C ι : Type*} [Field C] (a : ι) (m : ℕ) :
    familyJet C a m ≠ 0 := by
  rw [familyJet, freeCoordinate, Ne,
    map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (ι × ℕ) C)
      (FreeCoordinateRationalField C (ι × ℕ)))]
  exact MvPolynomial.X_ne_zero (a, m)

end

end GaloisForLFunctions.HTGeometry
