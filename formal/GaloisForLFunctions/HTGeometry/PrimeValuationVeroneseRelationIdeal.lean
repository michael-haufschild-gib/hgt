import GaloisForLFunctions.HTGeometry.DifferentialPivotRelationIdeal
import GaloisForLFunctions.HTGeometry.PrimeValuationVeroneseDifferentialBasis

/-!
# Complete relation ideals across prime-power valuation layers

A valuation-tail pivot presentation chooses, independently in every prime-power layer, a
tail-independent coefficient basis and expresses the remaining coefficient columns modulo finite
prime support in that basis.  The global pivot palette is differentially independent across all
layers.  Consequently the displayed prolonged affine relations generate the complete differential
relation ideal of the full valuation-resolved palette.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

universe u

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 80000

local instance complexFinitePrimeRationalAmbientScalarTowerValuationRelation :
    IsScalarTower ℂ finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  .of_algebraMap_eq fun z => by
    change algebraMap ℂ arithmeticFunctionRationalCoordinateField z =
      finitePrimeRationalCoefficientFieldToFormalRatFunc
        (algebraMap ℂ finitePrimeRationalCoefficientField z)
    rw [IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      finitePrimeRationalCoefficientField]
    rw [finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap]
    rw [← IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      arithmeticFunctionFractionField]
    rw [IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField]

/-- A layerwise tail-pivot presentation.  Each degree has its own pivot and dependent alphabets;
there is no uniform-rank assumption across valuation layers. -/
structure PrimeValuationTailPivotPresentation
    (d : ℕ) (J R : Fin d → Type u) [∀ r, Fintype (J r)] where
  pivot : ∀ r, J r → Nat.Primes → ℂ
  dependent : ∀ r, R r → Nat.Primes → ℂ
  coefficient : ∀ r, R r → J r → ℂ
  pivotTailIndependent : ∀ r, TailCoefficientIndependent (pivot r)
  pivotPatternRangeFinite :
    ∀ r, (Set.range (coefficientPattern (pivot r))).Finite
  residualFinite : ∀ r q,
    {p | dependent r q p - ∑ j, coefficient r q j * pivot r j p ≠ 0}.Finite

def PrimeValuationTailPivotPresentation.pivotPalette
    {d : ℕ} {J R A : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationTailPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, J r × A r) : arithmeticFunctionRationalCoordinateField :=
  primePowerCoefficientShiftCarrier x.1 (P.pivot x.1 x.2.1) (α x.1 x.2.2)

def PrimeValuationTailPivotPresentation.dependentPalette
    {d : ℕ} {J R A : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationTailPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, R r × A r) : arithmeticFunctionRationalCoordinateField :=
  primePowerCoefficientShiftCarrier x.1 (P.dependent x.1 x.2.1) (α x.1 x.2.2)

/-- A finite residual produces the affine base correction for one dependent jet. -/
theorem exists_primeValuationTailPivotBaseCorrection
    {d : ℕ} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationTailPivotPresentation d J R)
    (r : Fin d) (q : R r) (a : ℂ) (n : ℕ) :
    ∃ h : finitePrimeRationalCoefficientField,
      GaloisForLFunctions.differentialJet n
          (primePowerCoefficientShiftCarrier r (P.dependent r q) a) =
        algebraMap finitePrimeRationalCoefficientField
            arithmeticFunctionRationalCoordinateField h +
          ∑ j, algebraMap ℂ arithmeticFunctionRationalCoordinateField
              (P.coefficient r q j) *
            GaloisForLFunctions.differentialJet n
              (primePowerCoefficientShiftCarrier r (P.pivot r j) a) := by
  classical
  let combo : Nat.Primes → ℂ := fun p ↦
    ∑ j, P.coefficient r q j * P.pivot r j p
  have hsupport : {p | P.dependent r q p - 1 * combo p ≠ 0}.Finite := by
    simpa [combo] using P.residualFinite r q
  obtain ⟨h, hh⟩ := primePowerCoefficientShiftCarrier_residual_jet_mem_base
    r (P.dependent r q) combo 1 hsupport a n
  refine ⟨h, ?_⟩
  have hcombo := differentialJet_primePowerCoefficientShiftCarrier_linearCombination
    r (P.pivot r) (P.coefficient r q) a n
  change GaloisForLFunctions.differentialJet n
      (primePowerCoefficientShiftCarrier r (P.dependent r q) a) = _
  change GaloisForLFunctions.differentialJet n
      (primePowerCoefficientShiftCarrier r (P.dependent r q) a) -
        algebraMap ℂ arithmeticFunctionRationalCoordinateField 1 *
          GaloisForLFunctions.differentialJet n
            (primePowerCoefficientShiftCarrier r combo a) = _ at hh
  rw [map_one, one_mul, hcombo] at hh
  rw [← hh]
  ring

/-- The selected finite-prime correction for a dependent layer--shift--jet. -/
def PrimeValuationTailPivotPresentation.baseCorrection
    {d : ℕ} {J R A : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationTailPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, R r × A r) (n : ℕ) : finitePrimeRationalCoefficientField :=
  Classical.choose
    (exists_primeValuationTailPivotBaseCorrection
      P x.1 x.2.1 (α x.1 x.2.2) n)

theorem PrimeValuationTailPivotPresentation.baseCorrection_spec
    {d : ℕ} {J R A : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationTailPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, R r × A r) (n : ℕ) :
    GaloisForLFunctions.differentialJet n (P.dependentPalette α x) =
      algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField (P.baseCorrection α x n) +
        ∑ j, algebraMap ℂ arithmeticFunctionRationalCoordinateField
            (P.coefficient x.1 x.2.1 j) *
          GaloisForLFunctions.differentialJet n
            (primePowerCoefficientShiftCarrier x.1 (P.pivot x.1 j) (α x.1 x.2.2)) := by
  exact Classical.choose_spec
    (exists_primeValuationTailPivotBaseCorrection
      P x.1 x.2.1 (α x.1 x.2.2) n)

/-- The global block-diagonal coordinate matrix: coefficients mix neither valuation degree nor
shift. -/
def PrimeValuationTailPivotPresentation.paletteMatrix
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (A r)]
    (P : PrimeValuationTailPivotPresentation d J R) :
    (Σ r, R r × A r) → (Σ r, J r × A r) →
      finitePrimeRationalCoefficientField
  | ⟨r, q, a⟩, ⟨s, j, b⟩ =>
      if hrs : r = s then by
        subst s
        exact if a = b then
          algebraMap ℂ finitePrimeRationalCoefficientField (P.coefficient r q j)
        else 0
      else 0

/-- Every dependent jet has the global block-affine pivot expression. -/
theorem PrimeValuationTailPivotPresentation.palette_affineJet
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (P : PrimeValuationTailPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, R r × A r) (n : ℕ) :
    GaloisForLFunctions.differentialJet n (P.dependentPalette α x) =
      algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField (P.baseCorrection α x n) +
        ∑ y, algebraMap finitePrimeRationalCoefficientField
            arithmeticFunctionRationalCoordinateField (P.paletteMatrix x y) *
          GaloisForLFunctions.differentialJet n (P.pivotPalette α y) := by
  classical
  rcases x with ⟨r, q, a⟩
  rw [P.baseCorrection_spec α ⟨r, (q, a)⟩ n]
  congr 1
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single r]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single a]
    · simp [PrimeValuationTailPivotPresentation.paletteMatrix,
        PrimeValuationTailPivotPresentation.pivotPalette,
        IsScalarTower.algebraMap_apply ℂ finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField]
    · intro b hb hba
      simp [PrimeValuationTailPivotPresentation.paletteMatrix, hba.symm]
    · simp
  · intro s hs hsr
    apply Finset.sum_eq_zero
    intro y hy
    rcases y with ⟨j, b⟩
    simp [PrimeValuationTailPivotPresentation.paletteMatrix, hsr.symm]
  · simp

/-- The global valuation-resolved pivot palette is differentially independent. -/
theorem PrimeValuationTailPivotPresentation.pivotPalette_differentialIndependent
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)] [∀ r, Nonempty (A r)]
    [Nonempty (Σ r, J r × A r)]
    (P : PrimeValuationTailPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (P.pivotPalette α) := by
  exact primePowerCoefficientShiftPalettes_differentialIndependent
    J A P.pivot α hdistinct P.pivotPatternRangeFinite P.pivotTailIndependent

/-- **Complete prime-valuation relation law.**  The prolonged affine reductions of the
nonpivot columns generate the full relation ideal.  There are no additional nonlinear relations
and no relations mixing distinct valuation degrees. -/
theorem PrimeValuationTailPivotPresentation.complete_relationIdeal
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (R r)] [∀ r, DecidableEq (R r)]
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)] [∀ r, Nonempty (A r)]
    [Nonempty (Σ r, J r × A r)]
    (P : PrimeValuationTailPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    GaloisForLFunctions.differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (Sum.elim (P.pivotPalette α) (P.dependentPalette α)) =
      differentialPivotRelationIdeal P.paletteMatrix (P.baseCorrection α) := by
  apply differentialRelationIdeal_sumElim_eq_pivot
    (P.pivotPalette α) (P.dependentPalette α)
    P.paletteMatrix (P.baseCorrection α)
  · exact P.pivotPalette_differentialIndependent α hdistinct
  · exact P.palette_affineJet α

/-- The valuation pivots are an exact differential transcendence basis of the full palette. -/
theorem PrimeValuationTailPivotPresentation.differentialBasis
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (R r)] [∀ r, DecidableEq (R r)]
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)] [∀ r, Nonempty (A r)]
    [Nonempty (Σ r, J r × A r)]
    (P : PrimeValuationTailPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (P.pivotPalette α) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (Sum.elim (P.pivotPalette α) (P.dependentPalette α))) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (P.pivotPalette α)) := by
  constructor
  · exact P.pivotPalette_differentialIndependent α hdistinct
  · exact differentialAdjoin_sumElim_eq_left_of_affineJets
      (P.pivotPalette α) (P.dependentPalette α)
      P.paletteMatrix (P.baseCorrection α) (P.palette_affineJet α)

end

end GaloisForLFunctions.HTGeometry
