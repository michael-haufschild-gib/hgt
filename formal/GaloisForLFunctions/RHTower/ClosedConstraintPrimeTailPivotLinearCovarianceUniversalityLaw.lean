import GaloisForLFunctions.HTGeometry.DifferentialShiftPivotLinearCovarianceUniversalityLaw
import GaloisForLFunctions.HTGeometry.FiniteShadowCapacity
import GaloisForLFunctions.RHTower.PointedStonePrimeCompleteRelationCircuitUniversalityLaw

/-!
# Linear covariance of closed-constraint prime tail-pivot relation circuits

The finite-prime rational coefficient field is itself differential, so the earlier covariance
theorem requiring its entire coefficient field to be constant cannot apply.  Only entries of the
actual coordinate matrix need be constants.  Combining that sharp finite-shadow jet identity with
the complete relation ideal of a sparse closed-constraint prime chart yields exact contravariant
covariance under every invertible entrywise-constant linear coordinate change.
-/

open CategoryTheory Topology TopologicalSpace
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Matrix MvPolynomial GaloisForLFunctions

noncomputable section

/-- Evaluating a jetwise linear substitution needs constancy only of entries in the displayed
matrix, not of unrelated elements of the polynomial coefficient field. -/
theorem differentialPolynomialEval_linearChange_of_coefficients_constant
    {F K n : Type*} [CommRing F] [CommRing K] [Algebra F K]
    [Differential K] [Fintype n]
    (M : Matrix n n F)
    (hMconst : ∀ i j, (algebraMap F K (M i j))′ = 0)
    (x : n → K) (P : DifferentialPolynomial n F) :
    differentialPolynomialEval (C := F) x
        (differentialJetLinearChangeAlgHom M P) =
      differentialPolynomialEval (C := F) (matrixLinearForms M x) P := by
  let left := (differentialPolynomialEval (C := F) x).comp
    (differentialJetLinearChangeAlgHom M)
  let right := differentialPolynomialEval (C := F) (matrixLinearForms M x)
  have heq : left = right := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, r⟩
    simp only [left, right, AlgHom.coe_comp, Function.comp_apply,
      differentialJetLinearChangeAlgHom_X, differentialPolynomialEval_X]
    rw [differentialJet_matrixLinearForms_of_coefficients_constant
      M hMconst x i r]
    simpa [differentialPolynomialEval, jetwiseMatrixLinearForms, matrixLinearForms] using!
      (aeval_jetwiseMatrixLinearPolynomial M
        (fun p : n × ℕ => differentialJet p.2 (x p.1)) (i, r))
  exact AlgHom.congr_fun heq P

/-- Relation ideals transform contravariantly under an invertible linear coordinate change whose
actual entries are differential constants. -/
theorem mem_differentialRelationIdeal_linearChange_of_coefficients_constant_iff
    {F K n : Type*} [CommRing F] [CommRing K] [Algebra F K]
    [Differential K] [Fintype n] [DecidableEq n]
    (M N : Matrix n n F)
    (hMconst : ∀ i j, (algebraMap F K (M i j))′ = 0)
    (hMN : M * N = 1) (hNM : N * M = 1)
    (x : n → K) (P : DifferentialPolynomial n F) :
    P ∈ differentialRelationIdeal (matrixLinearForms M x) ↔
      differentialJetLinearChangeAlgEquiv M N hMN hNM P ∈
        differentialRelationIdeal x := by
  rw [mem_differentialRelationIdeal_iff, mem_differentialRelationIdeal_iff]
  change differentialPolynomialEval (C := F) (matrixLinearForms M x) P = 0 ↔
    differentialPolynomialEval (C := F) x
      (differentialJetLinearChangeAlgHom M P) = 0
  rw [differentialPolynomialEval_linearChange_of_coefficients_constant
    M hMconst x P]

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Matrix MvPolynomial

/-- **Closed-constraint prime tail-pivot linear covariance universality law.**  Every complete
finite prime tail-pivot chart remains completely classified after any invertible entrywise-constant
linear change of all pivot and dependent coordinates.  The transformed polynomial belongs to the
same explicit pivot ideal, so no new nonlinear relation is hidden by the coordinate change. -/
theorem closedConstraintPrimeTailPivot_linearCovariantCompleteRelation
    {J R A : Type*} [Countable J]
    [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (pi : ℕ ≃ Nat.Primes)
    (K : Set (J → Bool)) [Nonempty K]
    (hK : IsClosed K) (hall : allPositiveOrientationPattern ∈ K)
    (I : Finset J) [DecidableEq I] (hI : I.Nonempty)
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
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (M N : Matrix ((I × A) ⊕ (R × A)) ((I × A) ⊕ (R × A))
      finitePrimeRationalCoefficientField)
    (hMconst : ∀ i j,
      (algebraMap finitePrimeRationalCoefficientField
        arithmeticFunctionRationalCoordinateField (M i j))′ = 0)
    (hMN : M * N = 1) (hNM : N * M = 1)
    (Q : DifferentialPolynomial ((I × A) ⊕ (R × A))
      finitePrimeRationalCoefficientField) :
    let P := closedConstraintPrimeTailPivotPresentation pi K hK hall I hlinear
      dependent coefficient hresidual
    Q ∈ differentialRelationIdeal
        (matrixLinearForms M
          (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha))) ↔
      differentialJetLinearChangeAlgEquiv M N hMN hNM Q ∈
        differentialPivotRelationIdeal P.paletteMatrix (P.baseCorrection alpha) := by
  classical
  letI : Nonempty I := hI.to_subtype
  let P := closedConstraintPrimeTailPivotPresentation pi K hK hall I hlinear
    dependent coefficient hresidual
  dsimp only
  rw [mem_differentialRelationIdeal_linearChange_of_coefficients_constant_iff
    M N hMconst hMN hNM
    (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha)) Q]
  rw [(closedConstraintPrimeTailPivot_completeFiniteExtension pi K hK hall I hI
    hlinear dependent coefficient hresidual alpha hdistinct).2.1]

end

end RHTower
