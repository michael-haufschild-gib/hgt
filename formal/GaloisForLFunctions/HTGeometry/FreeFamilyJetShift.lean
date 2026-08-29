import GaloisForLFunctions.HTGeometry.FreeCoordinateChainRule
import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver
import GaloisForLFunctions.HTGeometry.DifferentialFieldLocus

/-!
# The free differential rational field on a family of indeterminates over a differential base

Let `(C, D)` be a differential field.  The rational function field
`FreeCoordinateRationalField C (ι × ℕ)` carries the total derivation of the differential
polynomial ring: coefficients are differentiated by `D` and the formal jets are shifted,
`x_a^{(m)} ↦ x_a^{(m+1)}`.  With it the coordinate `x_a = x_a^{(0)}` has
`differentialJet m x_a = x_a^{(m)}`, so the field is the free differential rational field
`C⟨x_a : a ∈ ι⟩` over the differential base.

Taking `D = 0` recovers the constant-coefficient jet shift, so this is the family counterpart of
the single-generator `FreeScalarJetField` in the generality of an arbitrary differential base.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial
open scoped Differential

/-- The polynomial algebra on a family of complete jets. -/
abbrev FreeFamilyJetPolynomial (C ι : Type*) [Field C] := MvPolynomial (ι × ℕ) C

/-- The free differential rational field on the family `x_a`, `a ∈ ι`. -/
abbrev FreeFamilyJetField (C ι : Type*) [Field C] := FreeCoordinateRationalField C (ι × ℕ)

/-- The total derivation of the differential polynomial ring, extended to the rational field by the
quotient rule, as the differential structure of the family jet field. -/
noncomputable instance freeFamilyJetFieldDifferential (C ι : Type*) [Field C] [Differential C] :
    Differential (FreeFamilyJetField C ι) := by
  letI : Algebra ℤ (FreeFamilyJetField C ι) := Ring.toIntAlgebra _
  exact ⟨GaloisForLFunctions.fractionRingDerivation
    ((Algebra.linearMap (FreeFamilyJetPolynomial C ι) (FreeFamilyJetField C ι)).compDer
      (differentialPolynomialOverDerivation ι C))⟩

variable {C ι : Type*} [Field C] [Differential C]

/-- On polynomials the ambient derivation is the total differential-polynomial derivation. -/
theorem freeFamilyJetField_deriv_algebraMap (P : FreeFamilyJetPolynomial C ι) :
    (algebraMap (FreeFamilyJetPolynomial C ι) (FreeFamilyJetField C ι) P)′ =
      algebraMap (FreeFamilyJetPolynomial C ι) (FreeFamilyJetField C ι)
        (differentialPolynomialOverDerivation ι C P) := by
  letI : Algebra ℤ (FreeFamilyJetField C ι) := Ring.toIntAlgebra _
  show GaloisForLFunctions.fractionRingDerivation
      ((Algebra.linearMap (FreeFamilyJetPolynomial C ι) (FreeFamilyJetField C ι)).compDer
        (differentialPolynomialOverDerivation ι C))
      (algebraMap (FreeFamilyJetPolynomial C ι) (FreeFamilyJetField C ι) P) = _
  rw [GaloisForLFunctions.fractionRingDerivation_algebraMap]
  rfl

/-- The ambient derivation shifts every free coordinate. -/
@[simp]
theorem freeCoordinate_deriv (p : ι × ℕ) :
    (freeCoordinate C (ι × ℕ) p)′ = freeCoordinate C (ι × ℕ) (p.1, p.2 + 1) := by
  rw [freeCoordinate, freeFamilyJetField_deriv_algebraMap]
  rcases p with ⟨a, m⟩
  rw [differentialPolynomialOverDerivation_X]
  rfl

/-- The ambient derivation restricts to the derivation of the base field. -/
theorem freeFamilyJetField_deriv_base (c : C) :
    (algebraMap C (FreeFamilyJetField C ι) c)′ =
      algebraMap C (FreeFamilyJetField C ι) (c′) := by
  rw [IsScalarTower.algebraMap_apply C (FreeFamilyJetPolynomial C ι) (FreeFamilyJetField C ι),
    IsScalarTower.algebraMap_apply C (FreeFamilyJetPolynomial C ι) (FreeFamilyJetField C ι),
    freeFamilyJetField_deriv_algebraMap]
  congr 1
  show differentialPolynomialOverDerivation ι C (MvPolynomial.C c) = MvPolynomial.C c′
  exact differentialPolynomialOverDerivation_C c

/-- The ambient derivation kills the constants of the prime field. -/
theorem freeFamilyJetField_deriv_one : (1 : FreeFamilyJetField C ι)′ = 0 := by
  have h1 : (1 : C)′ = 0 := Derivation.map_one_eq_zero _
  have h := freeFamilyJetField_deriv_base (C := C) (ι := ι) 1
  rw [h1, map_zero, map_one] at h
  exact h

/-- The `m`-th jet of the `a`-th free family generator. -/
def familyJet (C : Type*) {ι : Type*} [Field C] (a : ι) (m : ℕ) : FreeFamilyJetField C ι :=
  freeCoordinate C (ι × ℕ) (a, m)

@[simp]
theorem familyJet_deriv (a : ι) (m : ℕ) :
    (familyJet C a m)′ = familyJet C a (m + 1) := by
  rw [familyJet, freeCoordinate_deriv]
  rfl

/-- The differential jets of a family generator are exactly its free coordinates. -/
@[simp]
theorem differentialJet_familyJet_zero (a : ι) (m : ℕ) :
    differentialJet m (familyJet C a 0) = familyJet C a m := by
  induction m with
  | zero => simp
  | succ m ih => rw [differentialJet_succ, ih, familyJet_deriv]

omit [Differential C] in
/-- Every free family coordinate is nonzero. -/
theorem familyJet_ne_zero (a : ι) (m : ℕ) :
    familyJet C a m ≠ (0 : FreeFamilyJetField C ι) := by
  rw [familyJet, freeCoordinate, Ne,
    map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (ι × ℕ) C)
      (FreeCoordinateRationalField C (ι × ℕ)))]
  exact MvPolynomial.X_ne_zero (a, m)

/-- Every intermediate field of the family jet field is stable under the base derivation. -/
theorem deriv_algebraMap_mem (L : IntermediateField C (FreeFamilyJetField C ι)) (c : C) :
    (algebraMap C (FreeFamilyJetField C ι) c)′ ∈ L := by
  rw [freeFamilyJetField_deriv_base]
  exact L.algebraMap_mem _

/-- The ambient derivation carries a coordinate subfield into the subfield of the shifted
coordinates. -/
theorem deriv_mem_freeCoordinateField {S T : Set (ι × ℕ)}
    (hST : ∀ p ∈ S, ((p.1, p.2 + 1) : ι × ℕ) ∈ T) (hsub : S ⊆ T)
    {f : FreeFamilyJetField C ι} (hf : f ∈ freeCoordinateField C (ι × ℕ) S) :
    f′ ∈ freeCoordinateField C (ι × ℕ) T := by
  have hle : freeCoordinateField C (ι × ℕ) S ≤
      derivStableField (freeCoordinateField C (ι × ℕ) T)
        (deriv_algebraMap_mem (freeCoordinateField C (ι × ℕ) T)) := by
    rw [freeCoordinateField]
    refine adjoin_le_derivStableField ?_
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨IntermediateField.subset_adjoin _ _ ⟨p, hsub hp, rfl⟩, ?_⟩
    rw [freeCoordinate_deriv]
    exact IntermediateField.subset_adjoin _ _ ⟨(p.1, p.2 + 1), hST p hp, rfl⟩
  exact (hle hf).2

omit [Differential C] in
/-- **The coordinate criterion.**  An additive map obeying a twisted Leibniz rule that vanishes on
the base field and on every coordinate vanishes identically. -/
theorem eq_zero_of_twistedLeibniz [CharZero C] {E : Type*} [Field E]
    (W : FreeFamilyJetField C ι → E)
    (σ : FreeFamilyJetField C ι →+* E)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hleib : ∀ x y, W (x * y) = σ x * W y + σ y * W x)
    (hbase : ∀ c : C, W (algebraMap C (FreeFamilyJetField C ι) c) = 0)
    (hcoord : ∀ p : ι × ℕ, W (freeCoordinate C (ι × ℕ) p) = 0) (f : FreeFamilyJetField C ι) :
    W f = 0 := by
  have htop : twistedLeibnizKernel W σ hadd hleib hbase = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← freeCoordinateField_univ (C := C) (σ := ι × ℕ), freeCoordinateField,
      IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, -, rfl⟩
    exact hcoord p
  have hf : f ∈ twistedLeibnizKernel W σ hadd hleib hbase := by rw [htop]; trivial
  exact hf

end

end GaloisForLFunctions.HTGeometry
