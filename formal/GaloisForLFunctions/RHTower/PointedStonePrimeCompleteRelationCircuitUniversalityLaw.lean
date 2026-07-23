import GaloisForLFunctions.HTGeometry.IsodivisorialPrimeWalshStoneSaturation
import GaloisForLFunctions.HTGeometry.FiniteRangePrimeDirichletRelationIdeal
import GaloisForLFunctions.RHTower.PrimeSourceFiniteDifferentialCircuit
import GaloisForLFunctions.RHTower.PrimeSourcePolynomialActivationBoundary

/-!
# Pointed Stone prime complete relation-circuit universality

Every pointed compact metrizable Stone space is already represented in the corpus as the recurring
pattern chamber of a sparse prime-orientation system.  On every finite coordinate-independent
chart, that topological realization canonically becomes a tail-pivot basis.  Consequently every
finite-prime-residual linear extension has exactly its displayed affine differential relations,
and every source coordinate retains both hypertranscendental extraction boundaries.
-/

open CategoryTheory Topology TopologicalSpace
open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- A sign-valued coefficient carrier is the corresponding signed-prime carrier. -/
theorem closedConstraintPrimeCoefficientShiftCarrier_primeDirichletSign
    (epsilon : Nat.Primes → Bool) (a : ℂ) :
    primeCoefficientShiftCarrier (fun p => primeDirichletSign (epsilon p)) a =
      signedPrimeShiftCarrier epsilon a := by
  unfold primeCoefficientShiftCarrier signedPrimeShiftCarrier
  congr 2
  exact (signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn epsilon a 0).symm

/-- A coordinate-independent finite chart of a closed Boolean constraint, together with arbitrary
columns in its tail span, is a prime-coefficient tail-pivot presentation. -/
def closedConstraintPrimeTailPivotPresentation
    {J R : Type*} [Countable J]
    (pi : ℕ ≃ Nat.Primes)
    (K : Set (J → Bool)) [Nonempty K]
    (hK : IsClosed K) (hall : allPositiveOrientationPattern ∈ K)
    (I : Finset J)
    (hlinear : ∀ c : I → ℂ,
      (∀ x ∈ orientationRestriction I '' K,
        ∑ i, c i * primeDirichletSign (x i) = 0) → c = 0)
    (dependent : R → Nat.Primes → ℂ) (coefficient : R → I → ℂ)
    (hresidual : ∀ r,
      {p | dependent r p -
        ∑ i, coefficient r i *
          primeDirichletSign
            (sparseClosedConstraintPrimeOrientation K i.1 p) ≠ 0}.Finite) :
    PrimeCoefficientTailPivotPresentation I R where
  pivot := fun i p =>
    primeDirichletSign (sparseClosedConstraintPrimeOrientation K i.1 p)
  dependent := dependent
  coefficient := coefficient
  pivotTailIndependent :=
    sparseClosedConstraint_tailIndependent_of_coordinateSigns
      pi K hK hall I hlinear
  pivotPatternRangeFinite :=
    primeOrientationCoefficientPattern_range_finite
      (fun i : I => sparseClosedConstraintPrimeOrientation K i.1)
  residualFinite := hresidual

/-- Every finite tail-linear extension of a coordinate-independent closed-constraint chart has
an exact complete relation ideal, pivot differential basis, and rectangular rank. -/
theorem closedConstraintPrimeTailPivot_completeFiniteExtension
    {J R A : Type*} [Countable J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (pi : ℕ ≃ Nat.Primes)
    (K : Set (J → Bool)) [Nonempty K]
    (hK : IsClosed K) (hall : allPositiveOrientationPattern ∈ K)
    (I : Finset J) (hI : I.Nonempty)
    (hlinear : ∀ c : I → ℂ,
      (∀ x ∈ orientationRestriction I '' K,
        ∑ i, c i * primeDirichletSign (x i) = 0) → c = 0)
    (dependent : R → Nat.Primes → ℂ) (coefficient : R → I → ℂ)
    (hresidual : ∀ r,
      {p | dependent r p -
        ∑ i, coefficient r i *
          primeDirichletSign
            (sparseClosedConstraintPrimeOrientation K i.1 p) ≠ 0}.Finite)
    (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    let P := closedConstraintPrimeTailPivotPresentation pi K hK hall I hlinear
      dependent coefficient hresidual
    (∀ ia, P.pivotPalette alpha ia =
      signedPrimeShiftCarrier
        (sparseClosedConstraintPrimeOrientation K ia.1.1) (alpha ia.2)) ∧
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
    Fintype.card (I × A) = Fintype.card A * Fintype.card I := by
  classical
  letI : Nonempty I := hI.to_subtype
  dsimp only
  exact ⟨
    fun ia => closedConstraintPrimeCoefficientShiftCarrier_primeDirichletSign _ _,
    (closedConstraintPrimeTailPivotPresentation pi K hK hall I hlinear
      dependent coefficient hresidual).complete_relationIdeal alpha hdistinct,
    (closedConstraintPrimeTailPivotPresentation pi K hK hall I hlinear
      dependent coefficient hresidual).pivotPalette_differentialIndependent alpha hdistinct,
    (closedConstraintPrimeTailPivotPresentation pi K hK hall I hlinear
      dependent coefficient hresidual).differentialBasis alpha hdistinct |>.2,
    (closedConstraintPrimeTailPivotPresentation pi K hK hall I hlinear
      dependent coefficient hresidual).differentialBasis_card⟩

/-- **Pointed Stone prime complete relation-circuit universality law.**  Every pointed light
profinite space is homeomorphic to its exact sparse recurring prime-pattern chamber.  Every
coordinate-independent finite chart admits complete relation classification for every
finite-prime-residual tail-linear extension, and every source coordinate retains the two
hypertranscendental circuit/latent-input boundaries. -/
theorem pointedStone_sparsePrime_completeRelationCircuitUniversality
    (S : LightProfinite) (base : S) (pi : ℕ ≃ Nat.Primes) :
    (∃ Phi : S ≃ₜ pointedStoneConstraint S base,
      Phi base =
        ⟨allPositiveOrientationPattern,
          allPositiveOrientationPattern_mem_pointedStoneConstraint S base⟩) ∧
    primeRecurringPatternChamber pi
        (sparseClosedConstraintPrimeOrientation (pointedStoneConstraint S base)) =
      pointedStoneConstraint S base ∧
    (∀ (I : Finset (Unit ⊕ Clopens (lightToProfinite.obj S))), I.Nonempty →
      ∀ (hlinear : ∀ c : I → ℂ,
        (∀ x ∈ orientationRestriction I '' pointedStoneConstraint S base,
          ∑ i, c i * primeDirichletSign (x i) = 0) → c = 0),
      ∀ {R A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
        (dependent : R → Nat.Primes → ℂ) (coefficient : R → I → ℂ)
        (hresidual : ∀ r,
          {p | dependent r p -
            ∑ i, coefficient r i *
              primeDirichletSign
                (sparseClosedConstraintPrimeOrientation
                  (pointedStoneConstraint S base) i.1 p) ≠ 0}.Finite)
        (alpha : A → ℂ)
        (_hdistinct : Function.Injective (fun a => (alpha a).re)),
        let P := closedConstraintPrimeTailPivotPresentation pi
          (pointedStoneConstraint S base)
          (isClosed_pointedStoneConstraint S base)
          (allPositiveOrientationPattern_mem_pointedStoneConstraint S base)
          I hlinear dependent coefficient hresidual
        (∀ ia, P.pivotPalette alpha ia =
          signedPrimeShiftCarrier
            (sparseClosedConstraintPrimeOrientation
              (pointedStoneConstraint S base) ia.1.1) (alpha ia.2)) ∧
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
        Fintype.card (I × A) = Fintype.card A * Fintype.card I) ∧
    ∀ j : Unit ⊕ Clopens (lightToProfinite.obj S),
      (∀ Atom : arithmeticFunctionRationalCoordinateField → Prop,
        FiniteDifferentialCircuit Atom
          (signedPrimeNaturalShiftPalette
            (sparseClosedConstraintPrimeOrientation
              (pointedStoneConstraint S base) j) 0) →
        ∃ a : arithmeticFunctionRationalCoordinateField,
          Atom a ∧ HypertranscendentalOver ℂ a) ∧
      ∀ h : arithmeticFunctionRationalCoordinateField,
        ∀ P : Polynomial (differentialAdjoin ℂ
          ({h} : Set arithmeticFunctionRationalCoordinateField)),
          (signedPrimeNaturalShiftPalette
              (sparseClosedConstraintPrimeOrientation
                (pointedStoneConstraint S base) j) 0)′ =
            Polynomial.eval₂
              (algebraMap
                (differentialAdjoin ℂ
                  ({h} : Set arithmeticFunctionRationalCoordinateField))
                arithmeticFunctionRationalCoordinateField)
              (signedPrimeNaturalShiftPalette
                (sparseClosedConstraintPrimeOrientation
                  (pointedStoneConstraint S base) j) 0) P →
          HypertranscendentalOver ℂ h := by
  refine ⟨⟨pointedStoneConstraintHomeomorph S base,
    pointedStoneConstraintHomeomorph_base S base⟩,
    pointedStoneConstraint_sparsePrime_realization S base pi, ?_, ?_⟩
  · intro I hI hlinear R A _ _ _ dependent coefficient hresidual alpha hdistinct
    exact closedConstraintPrimeTailPivot_completeFiniteExtension pi
      (pointedStoneConstraint S base)
      (isClosed_pointedStoneConstraint S base)
      (allPositiveOrientationPattern_mem_pointedStoneConstraint S base)
      I hI hlinear dependent coefficient hresidual alpha hdistinct
  · intro j
    constructor
    · intro Atom hcircuit
      exact signedPrimeSource_finiteDifferentialCircuit_contains_HTAtom
        (sparseClosedConstraintPrimeOrientation
          (pointedStoneConstraint S base) j) Atom hcircuit
    · intro h P hrel
      exact signedPrimeSource_polynomialFirstOrder_law_forces_HT_input
        (sparseClosedConstraintPrimeOrientation
          (pointedStoneConstraint S base) j) P hrel

end

end RHTower
