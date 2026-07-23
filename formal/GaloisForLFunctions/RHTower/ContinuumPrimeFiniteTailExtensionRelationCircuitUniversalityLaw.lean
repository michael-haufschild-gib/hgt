import GaloisForLFunctions.HTGeometry.FiniteRangePrimeDirichletRelationIdeal
import GaloisForLFunctions.HTGeometry.ContinuumPrimeCoherenceSaturation
import GaloisForLFunctions.RHTower.PrimeSourceFiniteDifferentialCircuit
import GaloisForLFunctions.RHTower.PrimeSourcePolynomialActivationBoundary

/-!
# Continuum prime finite-tail extension relation-circuit universality

Every finite subfamily of one sparse coherent continuum is a tail-pivot basis.  Hence adjoining
arbitrary coefficient columns that lie in its span modulo finitely many primes produces exactly
the displayed prolonged affine relations, with no hidden nonlinear differential relations.  The
pivots remain an exact differential basis of rectangular rank.  Simultaneously, every continuum
orientation retains both finite-circuit and polynomial first-order hypertranscendental source
boundaries.
-/

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- A finite labelled subfamily of a sparse coherent continuum, together with arbitrary columns
in its tail span, is a prime-coefficient tail-pivot presentation. -/
def coherentPrimeTailPivotPresentation
    {B R : Type*} [Fintype B]
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes)
    (code : B → ℕ → Bool) (hcode : Function.Injective code)
    (dependent : R → Nat.Primes → ℂ) (coefficient : R → B → ℂ)
    (hresidual : ∀ r,
      {p | dependent r p -
        ∑ b, coefficient r b *
          primeDirichletSign
            (continuumSparsePrimeOrientation base e (code b) p) ≠ 0}.Finite) :
    PrimeCoefficientTailPivotPresentation B R where
  pivot := fun b p =>
    primeDirichletSign (continuumSparsePrimeOrientation base e (code b) p)
  dependent := dependent
  coefficient := coefficient
  pivotTailIndependent := by
    exact basedSparsePrefixOrientation_tailIndependent base e code hcode
  pivotPatternRangeFinite := by
    exact primeOrientationCoefficientPattern_range_finite
      (fun b => continuumSparsePrimeOrientation base e (code b))
  residualFinite := hresidual

/-- A sign-valued coefficient carrier is definitionally the signed-prime carrier after unfolding
the common prime-supported analytic jet. -/
theorem primeCoefficientShiftCarrier_primeDirichletSign
    (epsilon : Nat.Primes → Bool) (a : ℂ) :
    primeCoefficientShiftCarrier (fun p => primeDirichletSign (epsilon p)) a =
      signedPrimeShiftCarrier epsilon a := by
  unfold primeCoefficientShiftCarrier signedPrimeShiftCarrier
  congr 2
  exact (signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn epsilon a 0).symm

/-- The pivot palette of the coherent presentation is exactly the selected signed-prime shift
palette, not merely an isomorphic copy. -/
theorem coherentPrimeTailPivotPresentation_pivotPalette
    {B R A : Type*} [Fintype B]
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes)
    (code : B → ℕ → Bool) (hcode : Function.Injective code)
    (dependent : R → Nat.Primes → ℂ) (coefficient : R → B → ℂ)
    (hresidual : ∀ r,
      {p | dependent r p -
        ∑ b, coefficient r b *
          primeDirichletSign
            (continuumSparsePrimeOrientation base e (code b) p) ≠ 0}.Finite)
    (alpha : A → ℂ) (ba : B × A) :
    (coherentPrimeTailPivotPresentation base e code hcode
      dependent coefficient hresidual).pivotPalette alpha ba =
      signedPrimeShiftCarrier
        (continuumSparsePrimeOrientation base e (code ba.1)) (alpha ba.2) := by
  exact primeCoefficientShiftCarrier_primeDirichletSign _ _

/-- Every finite tail-linear extension of a coherent subpalette has an exact complete relation
ideal, an exact pivot differential basis, and rectangular differential rank. -/
theorem coherentPrimeTailPivot_completeFiniteExtension
    {B R A : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes)
    (code : B → ℕ → Bool) (hcode : Function.Injective code)
    (dependent : R → Nat.Primes → ℂ) (coefficient : R → B → ℂ)
    (hresidual : ∀ r,
      {p | dependent r p -
        ∑ b, coefficient r b *
          primeDirichletSign
            (continuumSparsePrimeOrientation base e (code b) p) ≠ 0}.Finite)
    (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    let P := coherentPrimeTailPivotPresentation base e code hcode
      dependent coefficient hresidual
    (∀ ba, P.pivotPalette alpha ba =
      signedPrimeShiftCarrier
        (continuumSparsePrimeOrientation base e (code ba.1)) (alpha ba.2)) ∧
    differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha)) =
      differentialPivotRelationIdeal P.paletteMatrix (P.baseCorrection alpha) ∧
    DifferentialIndependent finitePrimeRationalCoefficientField
      (P.pivotPalette alpha) ∧
    differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha))) =
      differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (P.pivotPalette alpha)) ∧
    Fintype.card (B × A) = Fintype.card A * Fintype.card B := by
  dsimp only
  exact ⟨
    coherentPrimeTailPivotPresentation_pivotPalette base e code hcode
      dependent coefficient hresidual alpha,
    (coherentPrimeTailPivotPresentation base e code hcode
      dependent coefficient hresidual).complete_relationIdeal alpha hdistinct,
    (coherentPrimeTailPivotPresentation base e code hcode
      dependent coefficient hresidual).pivotPalette_differentialIndependent alpha hdistinct,
    (coherentPrimeTailPivotPresentation base e code hcode
      dependent coefficient hresidual).differentialBasis alpha hdistinct |>.2,
    (coherentPrimeTailPivotPresentation base e code hcode
      dependent coefficient hresidual).differentialBasis_card⟩

/-- **Continuum prime finite-tail extension relation-circuit universality law.**  One sparse
continuum simultaneously has trivial global relation ideal; complete affine relation
classification for every finite tail-linear extension at every finite shift alphabet; and both
finite-circuit and polynomial first-order hypertranscendental source rigidity for every member. -/
theorem continuumPrime_completeFiniteTailExtension_sourceRigidity
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) :
    differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (fun xa : (ℕ → Bool) × ℕ =>
          signedPrimeNaturalShiftPalette
            (continuumSparsePrimeOrientation base e xa.1) xa.2) = ⊥ ∧
    (∀ {B R A : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype A] [DecidableEq A] [Nonempty A]
      (code : B → ℕ → Bool) (hcode : Function.Injective code)
      (dependent : R → Nat.Primes → ℂ) (coefficient : R → B → ℂ)
      (hresidual : ∀ r,
        {p | dependent r p -
          ∑ b, coefficient r b *
            primeDirichletSign
              (continuumSparsePrimeOrientation base e (code b) p) ≠ 0}.Finite)
      (alpha : A → ℂ)
      (_hdistinct : Function.Injective (fun a => (alpha a).re)),
      let P := coherentPrimeTailPivotPresentation base e code hcode
        dependent coefficient hresidual
      (∀ ba, P.pivotPalette alpha ba =
        signedPrimeShiftCarrier
          (continuumSparsePrimeOrientation base e (code ba.1)) (alpha ba.2)) ∧
      differentialRelationIdeal
          (C := finitePrimeRationalCoefficientField)
          (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha)) =
        differentialPivotRelationIdeal P.paletteMatrix (P.baseCorrection alpha) ∧
      DifferentialIndependent finitePrimeRationalCoefficientField
        (P.pivotPalette alpha) ∧
      differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha))) =
        differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (P.pivotPalette alpha)) ∧
      Fintype.card (B × A) = Fintype.card A * Fintype.card B) ∧
    (∀ z (Atom : arithmeticFunctionRationalCoordinateField → Prop),
      FiniteDifferentialCircuit Atom
        (signedPrimeNaturalShiftPalette
          (continuumSparsePrimeOrientation base e z) 0) →
      ∃ a : arithmeticFunctionRationalCoordinateField,
        Atom a ∧ HypertranscendentalOver ℂ a) ∧
    ∀ z (h : arithmeticFunctionRationalCoordinateField)
      (P : Polynomial (differentialAdjoin ℂ
        ({h} : Set arithmeticFunctionRationalCoordinateField))),
      (signedPrimeNaturalShiftPalette
          (continuumSparsePrimeOrientation base e z) 0)′ =
        Polynomial.eval₂
          (algebraMap
            (differentialAdjoin ℂ
              ({h} : Set arithmeticFunctionRationalCoordinateField))
            arithmeticFunctionRationalCoordinateField)
          (signedPrimeNaturalShiftPalette
            (continuumSparsePrimeOrientation base e z) 0) P →
      HypertranscendentalOver ℂ h := by
  have hdiff :=
    continuumSparsePrimeNaturalShiftPalette_differentialIndependent base e
  refine ⟨
    (differentialIndependent_iff_relationIdeal_eq_bot
      (fun xa : (ℕ → Bool) × ℕ =>
        signedPrimeNaturalShiftPalette
          (continuumSparsePrimeOrientation base e xa.1) xa.2)).mp hdiff,
    ?_, ?_, ?_⟩
  · intro B R A _ _ _ _ _ _ code hcode dependent coefficient hresidual
      alpha hdistinct
    exact coherentPrimeTailPivot_completeFiniteExtension base e code hcode
      dependent coefficient hresidual alpha hdistinct
  · intro z Atom hcircuit
    exact signedPrimeSource_finiteDifferentialCircuit_contains_HTAtom
      (continuumSparsePrimeOrientation base e z) Atom hcircuit
  · intro z h P hrel
    exact signedPrimeSource_polynomialFirstOrder_law_forces_HT_input
      (continuumSparsePrimeOrientation base e z) P hrel

end

end RHTower
