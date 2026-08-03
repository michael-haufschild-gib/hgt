import GaloisForLFunctions.HTGeometry.InvariantFractions
import Mathlib.RingTheory.Invariant.Basic

/-!
# Finite invariant-field generation

For a finite group acting compatibly on a domain and its fraction field, the fixed field is the
fraction field of the invariant subring.  Thus invariant rational functions are generated as a
field by invariant regular functions.  This is the algebraic fixed-field step used by finite
quotient schemes and finite holonomy descent.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

variable (G : Type u) [Group G] [Fintype G]
variable (R : Type v) [CommRing R] [IsDomain R] [MulSemiringAction G R]
variable (L : Type w) [Field L] [Algebra R L] [IsFractionRing R L]
  [MulSemiringAction G L] [SMulDistribClass G R L]

/-- Inclusion of invariant regular functions into invariant rational functions. -/
def fixedSubringToFixedSubfield : FixedPoints.subring R G →+* FixedPoints.subfield G L where
  toFun r := ⟨algebraMap R L r.1, fun g => by rw [smul_algebraMap_eq, r.2 g]⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

instance fixedSubringAlgebraFixedSubfield :
    Algebra (FixedPoints.subring R G) (FixedPoints.subfield G L) :=
  (fixedSubringToFixedSubfield G R L).toAlgebra

omit [Fintype G] [IsDomain R] in
/-- Inclusion of fixed regular functions into the fixed field is injective. -/
theorem fixedSubringToFixedSubfield_injective :
    Function.Injective (fixedSubringToFixedSubfield G R L) := by
  intro x y h
  apply Subtype.ext
  apply IsFractionRing.injective R L
  exact congrArg Subtype.val h

/-- Every fixed rational function is a quotient of two fixed regular functions, with nonzero
denominator. -/
theorem fixedSubfield_exists_invariant_div (x : FixedPoints.subfield G L) :
    ∃ a b : FixedPoints.subring R G, b ≠ 0 ∧
      x = algebraMap _ _ a / algebraMap _ _ b := by
  obtain ⟨a, b, ha, hb, hb0, hx⟩ :=
    exists_invariant_ratio (G := G) (R := R) (L := L) x.1 x.2
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_⟩
  · exact fun h => hb0 (congrArg Subtype.val h)
  · apply Subtype.ext
    exact hx

/-- **Invariant-field generation.** The fixed field is a fraction field of the invariant ring. -/
instance fixedSubfieldIsFractionRing :
    IsFractionRing (FixedPoints.subring R G) (FixedPoints.subfield G L) := by
  letI : FaithfulSMul (FixedPoints.subring R G) (FixedPoints.subfield G L) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (fixedSubringToFixedSubfield_injective G R L)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, -, hz⟩ := fixedSubfield_exists_invariant_div G R L z
  exact ⟨a, b, hz⟩

/-- Canonical equivalence from the abstract fraction field of invariant regular functions to the
fixed rational function field. -/
noncomputable def invariantFractionFieldEquiv :
    FractionRing (FixedPoints.subring R G) ≃ₐ[FixedPoints.subring R G]
      FixedPoints.subfield G L :=
  FractionRing.algEquiv (FixedPoints.subring R G) (FixedPoints.subfield G L)

end GaloisForLFunctions.HTGeometry
