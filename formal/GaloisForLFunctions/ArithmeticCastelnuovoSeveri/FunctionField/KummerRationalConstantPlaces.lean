import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPlaceClassification

/-!
# Rationality of intrinsic Kummer places

Rationality means that constants surject onto the valuation residue field.
The finite-place quotient criterion and the rational infinity place give
the corresponding refinement of the intrinsic place classification.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis

/-- A rational place is a constant-field valuation ring whose residue field consists of constants. -/
def RationalConstantFieldPlaces (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  {W : ConstantFieldPlaces K L // Function.Surjective (valuationConstantResidue W.val W.property.2)}

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- The intrinsic place at infinity has residue field equal to the stated constants. -/
theorem squareKummerInfinityConstantPlace_rational :
    Function.Surjective (valuationConstantResidue (squareKummerInfinityConstantPlace p s c d r).val
      (squareKummerInfinityConstantPlace p s c d r).property.2) := by
  let K := SquareConstantField p s
  let L' := KummerInfinityField c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))
  let w := squareKummerInfinityPlace p s c d r
  let e := kummerInfinityFieldEquiv c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))
  have h := (heightOne_constant_residue_surjective_iff (K := K) (L := L') w).mpr
    (squareKummerInfinity_residue_surjective p s c d r)
  exact (valuationConstantResidue_comap_surjective_iff e (w.valuation L').valuationSubring
    (heightOne_constants_mem (K := K) w)).mpr h

/-- The actual rational place at infinity. -/
def squareKummerRationalInfinityPlace :
    RationalConstantFieldPlaces (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :=
  ⟨squareKummerInfinityConstantPlace p s c d r, squareKummerInfinityConstantPlace_rational p s c d r⟩

/-- A rational finite normalization place gives a rational valuation-ring place. -/
def squareKummerRationalFinitePlace
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r)))
    (hw : Function.Surjective (algebraMap (SquareConstantField p s)
      (SquareKummerNormalization p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) ⧸ w.asIdeal))) :
    RationalConstantFieldPlaces (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :=
  ⟨squareKummerFiniteConstantPlace p s c d r w,
    (heightOne_constant_residue_surjective_iff w).mpr hw⟩

/-- Every intrinsic rational place is finite with constant prime residue, or is the unique infinity place. -/
theorem squareKummer_rationalPlace_cases
    (W : RationalConstantFieldPlaces (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) :
    (∃ w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) r)),
      ∃ hw : Function.Surjective (algebraMap (SquareConstantField p s)
        (SquareKummerNormalization p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) ⧸ w.asIdeal)),
        squareKummerRationalFinitePlace p s c d r w hw = W) ∨
      squareKummerRationalInfinityPlace p s c d r = W := by
  rcases squareKummer_constantPlace_cases p s c d r W.val with ⟨w, hw⟩ | hW
  · left
    have hres : Function.Surjective (valuationConstantResidue
        (squareKummerFiniteConstantPlace p s c d r w).val
        (squareKummerFiniteConstantPlace p s c d r w).property.2) := hw.symm ▸ W.property
    have hquot := (heightOne_constant_residue_surjective_iff w).mp hres
    exact ⟨w, hquot, Subtype.ext hw⟩
  · exact Or.inr (Subtype.ext hW)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
