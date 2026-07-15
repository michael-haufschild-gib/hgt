import GaloisForLFunctions.HTGeometry.DifferentialPivotRelationIdeal
import GaloisForLFunctions.HTGeometry.FiniteRangePrimeDirichletModuli

/-!
# Complete relations and exact rank for finite-range prime Dirichlet palettes

A tail-pivot presentation chooses a tail-independent basis of prime coefficient columns and
expresses every remaining column modulo finite support in that basis.  The corresponding shifted
carrier family has exactly the displayed affine differential-linear relations and no others.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 60000

local instance complexFinitePrimeRationalAmbientScalarTower :
    IsScalarTower ℂ finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  .of_algebraMap_eq fun c => by
    change algebraMap ℂ arithmeticFunctionRationalCoordinateField c =
      finitePrimeRationalCoefficientFieldToFormalRatFunc
        (algebraMap ℂ finitePrimeRationalCoefficientField c)
    rw [IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      finitePrimeRationalCoefficientField]
    rw [finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap]
    rw [← IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      arithmeticFunctionFractionField]
    rw [IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField]

/-- A finite tail-pivot presentation of a prime coefficient family.  The `pivot` columns are
independent modulo finite support and each `dependent` column has the displayed tail coordinates. -/
structure PrimeCoefficientTailPivotPresentation (B R : Type*) [Fintype B] where
  pivot : B → Nat.Primes → ℂ
  dependent : R → Nat.Primes → ℂ
  coefficient : R → B → ℂ
  pivotTailIndependent : TailCoefficientIndependent pivot
  pivotPatternRangeFinite : (Set.range (coefficientPattern pivot)).Finite
  residualFinite : ∀ r,
    {p | dependent r p - ∑ b, coefficient r b * pivot b p ≠ 0}.Finite

def PrimeCoefficientTailPivotPresentation.pivotPalette
    {B R A : Type*} [Fintype B]
    (P : PrimeCoefficientTailPivotPresentation B R) (alpha : A → ℂ)
    (ba : B × A) : arithmeticFunctionRationalCoordinateField :=
  primeCoefficientShiftCarrier (P.pivot ba.1) (alpha ba.2)

def PrimeCoefficientTailPivotPresentation.dependentPalette
    {B R A : Type*} [Fintype B]
    (P : PrimeCoefficientTailPivotPresentation B R) (alpha : A → ℂ)
    (ra : R × A) : arithmeticFunctionRationalCoordinateField :=
  primeCoefficientShiftCarrier (P.dependent ra.1) (alpha ra.2)

/-- The block-diagonal tail-coordinate matrix: source coordinates do not mix distinct shifts. -/
def PrimeCoefficientTailPivotPresentation.paletteMatrix
    {B R A : Type*} [Fintype B] [DecidableEq A]
    (P : PrimeCoefficientTailPivotPresentation B R) :
    R × A → B × A → finitePrimeRationalCoefficientField :=
  fun ra ba => if ra.2 = ba.2 then
    algebraMap ℂ finitePrimeRationalCoefficientField (P.coefficient ra.1 ba.1)
  else 0

theorem exists_primeCoefficientTailPivotBaseCorrection
    {B R : Type*} [Fintype B]
    (P : PrimeCoefficientTailPivotPresentation B R)
    (r : R) (a : ℂ) (n : ℕ) :
    ∃ h : finitePrimeRationalCoefficientField,
      GaloisForLFunctions.differentialJet n
          (primeCoefficientShiftCarrier (P.dependent r) a) =
        algebraMap finitePrimeRationalCoefficientField
            arithmeticFunctionRationalCoordinateField h +
          ∑ b, algebraMap ℂ arithmeticFunctionRationalCoordinateField
              (P.coefficient r b) *
            GaloisForLFunctions.differentialJet n
              (primeCoefficientShiftCarrier (P.pivot b) a) := by
  classical
  let combo : Nat.Primes → ℂ := fun p =>
    ∑ b, P.coefficient r b * P.pivot b p
  have hsupport : {p | P.dependent r p - 1 * combo p ≠ 0}.Finite := by
    simpa [combo] using P.residualFinite r
  obtain ⟨h, hh⟩ :=
    primeCoefficientShiftCarrier_projectiveResidual_jet_mem_base
      (P.dependent r) combo 1 hsupport a n
  refine ⟨h, ?_⟩
  have hcombo := differentialJet_primeCoefficientShiftCarrier_linearCombination
    P.pivot (P.coefficient r) a n
  change GaloisForLFunctions.differentialJet n
      (primeCoefficientShiftCarrier (P.dependent r) a) = _
  change GaloisForLFunctions.differentialJet n
      (primeCoefficientShiftCarrier (P.dependent r) a) -
        algebraMap ℂ arithmeticFunctionRationalCoordinateField 1 *
          GaloisForLFunctions.differentialJet n
            (primeCoefficientShiftCarrier combo a) = _ at hh
  rw [map_one, one_mul, hcombo] at hh
  rw [← hh]
  ring

/-- The base correction selected from the finite prime residual at each dependent shift--jet. -/
def PrimeCoefficientTailPivotPresentation.baseCorrection
    {B R A : Type*} [Fintype B]
    (P : PrimeCoefficientTailPivotPresentation B R) (alpha : A → ℂ)
    (ra : R × A) (n : ℕ) : finitePrimeRationalCoefficientField :=
  Classical.choose
    (exists_primeCoefficientTailPivotBaseCorrection P ra.1 (alpha ra.2) n)

theorem PrimeCoefficientTailPivotPresentation.baseCorrection_spec
    {B R A : Type*} [Fintype B]
    (P : PrimeCoefficientTailPivotPresentation B R) (alpha : A → ℂ)
    (ra : R × A) (n : ℕ) :
    GaloisForLFunctions.differentialJet n (P.dependentPalette alpha ra) =
      algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField (P.baseCorrection alpha ra n) +
        ∑ b, algebraMap ℂ arithmeticFunctionRationalCoordinateField
            (P.coefficient ra.1 b) *
          GaloisForLFunctions.differentialJet n
            (P.pivotPalette alpha (b, ra.2)) := by
  exact Classical.choose_spec
    (exists_primeCoefficientTailPivotBaseCorrection P ra.1 (alpha ra.2) n)

theorem PrimeCoefficientTailPivotPresentation.palette_affineJet
    {B R A : Type*} [Fintype B] [Fintype A] [DecidableEq A]
    (P : PrimeCoefficientTailPivotPresentation B R) (alpha : A → ℂ)
    (ra : R × A) (n : ℕ) :
    GaloisForLFunctions.differentialJet n (P.dependentPalette alpha ra) =
      algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField (P.baseCorrection alpha ra n) +
        ∑ ba, algebraMap finitePrimeRationalCoefficientField
            arithmeticFunctionRationalCoordinateField (P.paletteMatrix ra ba) *
          GaloisForLFunctions.differentialJet n (P.pivotPalette alpha ba) := by
  classical
  rw [P.baseCorrection_spec alpha ra n]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_eq_single ra.2]
  · simp [PrimeCoefficientTailPivotPresentation.paletteMatrix,
      IsScalarTower.algebraMap_apply ℂ finitePrimeRationalCoefficientField
        arithmeticFunctionRationalCoordinateField]
  · intro a ha hane
    simp [PrimeCoefficientTailPivotPresentation.paletteMatrix, hane.symm]
  · simp

/-- The chosen pivot palette is differentially independent. -/
theorem PrimeCoefficientTailPivotPresentation.pivotPalette_differentialIndependent
    {B R A : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : PrimeCoefficientTailPivotPresentation B R) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (P.pivotPalette alpha) := by
  exact (primeCoefficientShiftPalette_differentialIndependent_iff
    P.pivot alpha hdistinct P.pivotPatternRangeFinite).mpr P.pivotTailIndependent

/-- **Complete finite-alphabet relation law.**  The full relation ideal is generated by the
displayed affine differential-linear tail relations. -/
theorem PrimeCoefficientTailPivotPresentation.complete_relationIdeal
    {B R A : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : PrimeCoefficientTailPivotPresentation B R) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    GaloisForLFunctions.differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha)) =
      differentialPivotRelationIdeal P.paletteMatrix P.baseCorrection := by
  apply differentialRelationIdeal_sumElim_eq_pivot
    (P.pivotPalette alpha) (P.dependentPalette alpha)
    P.paletteMatrix P.baseCorrection
  · exact P.pivotPalette_differentialIndependent alpha hdistinct
  · exact P.palette_affineJet alpha

/-- The tail pivots form an exact differential transcendence basis of the full palette field. -/
theorem PrimeCoefficientTailPivotPresentation.differentialBasis
    {B R A : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : PrimeCoefficientTailPivotPresentation B R) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (P.pivotPalette alpha) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha))) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (P.pivotPalette alpha)) := by
  constructor
  · exact P.pivotPalette_differentialIndependent alpha hdistinct
  · exact differentialAdjoin_sumElim_eq_left_of_affineJets
      (P.pivotPalette alpha) (P.dependentPalette alpha)
      P.paletteMatrix P.baseCorrection P.palette_affineJet

/-- The labelled differential basis has the exact rectangular rank `card(A) * card(B)`. -/
theorem PrimeCoefficientTailPivotPresentation.differentialBasis_card
    {B R A : Type*} [Fintype B] [Fintype A]
    (P : PrimeCoefficientTailPivotPresentation B R) :
    Fintype.card (B × A) = Fintype.card A * Fintype.card B := by
  rw [Fintype.card_prod, Nat.mul_comm]

end

end GaloisForLFunctions.HTGeometry
