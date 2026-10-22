import GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesCalkinPolarHandoff
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCrossPrimeSingularCorona

/-!
# Route R cross-prime Stokes/Calkin pre-quotient no-factorization

The actual Calderon--Witt cross-prime source contains a distinguished `(2,3)` atom.  Its
coefficient-faithful pre-quotient realization is the fixed Stokes--Sonin commutator constructed in
`RouteRCrossPrimeStokesCalkinPolarHandoff`.  The singular-corona projection kills that atom.

Consequently, away from neutral horizontal grade, no linear map out of the singular corona can
recover the pre-quotient comparison, even modulo compact operators.  This formally closes the
proposal that existing singular-corona exactness supplies the missing compactness producer.  It
does not prove compactness of the fixed commutator from a new source law.
-/

open Complex

namespace RHTower

noncomputable section

noncomputable local instance decEqCrossPrimePacketIndexPrequotient :
    DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

/-- The literal `(2,3)` atom in the actual finite Calderon--Witt arithmetic source span. -/
def routeRTwoThreeActualCrossPrimeSourceAtom :
    deningerCalderonWittCrossPrimeAlgebraicSourceSpan :=
  deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan
    (Finsupp.single deningerCalderonWittTwoThreePacketIndex 1)

@[simp]
theorem routeRTwoThreeActualCrossPrimeSourceAtom_coefficient :
    deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan.symm
        routeRTwoThreeActualCrossPrimeSourceAtom
        deningerCalderonWittTwoThreePacketIndex = 1 := by
  simp [routeRTwoThreeActualCrossPrimeSourceAtom]

/-- Coefficient-faithful pre-quotient comparison on the selected arithmetic source coordinate. -/
def routeRTwoThreeStokesCalkinPrequotientComparison (A a : ℝ) :
    deningerCalderonWittCrossPrimeAlgebraicSourceSpan →ₗ[ℂ]
      (ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) where
  toFun x :=
    deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan.symm x
        deningerCalderonWittTwoThreePacketIndex •
      routeRTwoThreeStokesSoninCommutator A a
  map_add' x y := by
    simp [add_smul]
  map_smul' c x := by
    simp [mul_smul]

/-- The pre-quotient comparison sends the literal arithmetic atom to the fixed physical
Stokes--Sonin commutator with coefficient one. -/
@[simp]
theorem routeRTwoThreeStokesCalkinPrequotientComparison_sourceAtom
    (A a : ℝ) :
    routeRTwoThreeStokesCalkinPrequotientComparison A a
        routeRTwoThreeActualCrossPrimeSourceAtom =
      routeRTwoThreeStokesSoninCommutator A a := by
  simp [routeRTwoThreeStokesCalkinPrequotientComparison]

/-- The same literal source atom is zero after singular-corona projection. -/
@[simp]
theorem routeRTwoThreeActualCrossPrimeSourceAtom_singularCoronaClass :
    deningerCalderonWittCrossPrimeSingularCoronaClass
        (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert
          routeRTwoThreeActualCrossPrimeSourceAtom) = 0 := by
  exact
    deningerCalderonWittCrossPrimeSingularCoronaClass_sourceSpan
      routeRTwoThreeActualCrossPrimeSourceAtom

/-- Off neutral grade, the actual source atom has a noncompact pre-quotient image. -/
theorem routeRTwoThreeStokesCalkinPrequotientComparison_sourceAtom_not_compact
    {A : ℝ} (hA : 0 < A) {a : ℝ} (ha : a ≠ 0) :
    ¬IsCompactOperator
      (routeRTwoThreeStokesCalkinPrequotientComparison A a
        routeRTwoThreeActualCrossPrimeSourceAtom) := by
  rw [routeRTwoThreeStokesCalkinPrequotientComparison_sourceAtom,
    routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA]
  exact ha

/-- **Calkin no-factorization.**  Away from neutral grade, no linear reporter on the singular
corona can agree with the actual pre-quotient comparison even modulo compact operators. -/
theorem no_routeRTwoThreeStokesCalkinPrequotientComparison_factorization_mod_compact
    {A : ℝ} (hA : 0 < A) {a : ℝ} (ha : a ≠ 0) :
    ¬∃ F : DeningerCalderonWittCrossPrimeSingularCorona →ₗ[ℂ]
        (ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2),
      ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
        IsCompactOperator
          (F (deningerCalderonWittCrossPrimeSingularCoronaClass
              (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x)) -
            routeRTwoThreeStokesCalkinPrequotientComparison A a x) := by
  rintro ⟨F, hfactor⟩
  have hcompact := hfactor routeRTwoThreeActualCrossPrimeSourceAtom
  rw [routeRTwoThreeActualCrossPrimeSourceAtom_singularCoronaClass,
    map_zero, routeRTwoThreeStokesCalkinPrequotientComparison_sourceAtom,
    zero_sub] at hcompact
  change IsCompactOperator
    (-(routeRTwoThreeStokesSoninCommutator A a :
      ArchimedeanWeightedL2 → ArchimedeanWeightedL2)) at hcompact
  have hphysical :
      IsCompactOperator (routeRTwoThreeStokesSoninCommutator A a) := by
    simpa using hcompact.neg
  exact ha
    ((routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA a).1 hphysical)

/-- Exact equality factorization is impossible as a corollary of the stronger Calkin statement. -/
theorem no_routeRTwoThreeStokesCalkinPrequotientComparison_factorization
    {A : ℝ} (hA : 0 < A) {a : ℝ} (ha : a ≠ 0) :
    ¬∃ F : DeningerCalderonWittCrossPrimeSingularCorona →ₗ[ℂ]
        (ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2),
      ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
        F (deningerCalderonWittCrossPrimeSingularCoronaClass
            (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x)) =
          routeRTwoThreeStokesCalkinPrequotientComparison A a x := by
  intro hfactor
  apply no_routeRTwoThreeStokesCalkinPrequotientComparison_factorization_mod_compact
    hA ha
  rcases hfactor with ⟨F, hF⟩
  refine ⟨F, ?_⟩
  intro x
  rw [hF x, sub_self]
  exact isCompactOperator_zero

end

end RHTower
