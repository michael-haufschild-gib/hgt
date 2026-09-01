import GaloisForLFunctions.HTGeometry.AsymmetricDifferenceTensor
import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphicIsomonodromy
import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedGaloisDichotomy
import GaloisForLFunctions.HTGeometry.RatFuncCoefficientExtension

/-!
# Meromorphic scalar extension of the Bessel PPV coordinate ring

The actual meromorphic Bessel solution and the full parameter-constant field coexist in the
faithful scalar extension `Constants(z) ⊗_{ℂ(z)} Mero(ℂ)`.  Its asymmetric tensor shift carries
the first Bessel solution column to the companion recurrence.  A determinant-one point then gives
a differential evaluator from the universal localized PPV coordinate ring.
-/

open scoped Differential TensorProduct

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions Bottcher

noncomputable section

local instance besselScalarComplexDifferential : Differential ℂ := complexZeroDifferential
local instance besselScalarRatFuncComplexDifferential : Differential (RatFunc ℂ) :=
  coordinateTotalDifferential
local instance besselScalarRatFuncConstantsDifferential : Differential (RatFunc Constants) :=
  coordinateTotalDifferential

local instance constantsDifferentialAlgebra : DifferentialAlgebra ℂ Constants :=
  DiffFieldExt.differentialAlgebra (diffClosureExt (F := ℂ))

local instance besselScalarRatFuncAlgebra : Algebra (RatFunc ℂ) (RatFunc Constants) :=
  (ratFuncCoeffMap (algebraMap ℂ Constants)).toAlgebra

local instance ratFuncConstantsDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (RatFunc Constants) := by
  constructor
  intro r
  exact ratFuncCoeffMap_deriv (algebraMap ℂ Constants)
    (fun c => (DifferentialAlgebra.deriv_algebraMap c).symm) r

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

local instance besselScalarMeroAlgebra : Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

theorem complex_polyTotalDeriv_eq_derivative (p : Polynomial ℂ) :
    polyTotalDeriv p = p.derivative := by
  rw [polyTotalDeriv_apply]
  have hcoeff : coeffDeriv p = 0 := by
    ext n
    rw [coeffDeriv_coeff, Polynomial.coeff_zero]
    rfl
  rw [hcoeff, add_zero]

theorem complex_coordinateTotalDerivation_eq_coordinateDerivation :
    coordinateTotalDerivation (K := ℂ) =
      Derivation.restrictScalars ℚ (ratFuncCoordinateDerivation ℂ) := by
  apply GaloisForLFunctions.fractionRing_derivation_ext (A := Polynomial ℂ)
  intro p
  rw [coordinateTotalDerivation_algebraMap]
  change algebraMap (Polynomial ℂ) (RatFunc ℂ) (polyTotalDeriv p) =
    ratFuncCoordinateDerivation ℂ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
  rw [ratFuncCoordinateDerivation_algebraMap,
    complex_polyTotalDeriv_eq_derivative]

local instance meromorphicDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  ⟨fun r => by
    change Differential.deriv
        (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ r) = _
    rw [show Differential.deriv r = coordinateTotalDerivation r by rfl,
      complex_coordinateTotalDerivation_eq_coordinateDerivation]
    exact meroField_deriv_ratfuncToMero r⟩

/-- Scalar extension containing both parameter constants and actual meromorphic Bessel values. -/
abbrev BesselScalarTensor :=
  RatFunc Constants ⊗[RatFunc ℂ] meroField Set.univ

local instance besselScalarTensorDifferential : Differential BesselScalarTensor :=
  tensorProductDifferential

local instance besselScalarTensorDifferentialAlgebra :
    DifferentialAlgebra (RatFunc Constants) BesselScalarTensor :=
  tensorProductDifferentialAlgebra_left

theorem ratFuncCoeffMap_orderShiftCoeff (c : ℂ) :
    ratFuncCoeffMap (algebraMap ℂ Constants) (FieldShift.orderShiftCoeff c) =
      FieldShift.orderShiftCoeff (algebraMap ℂ Constants c) := by
  rw [FieldShift.orderShiftCoeff, FieldShift.orderShiftCoeff,
    ratFuncCoeffMap_algebraMap_poly]
  congr 1
  simp

theorem besselScalarLeftShift_compat (r : RatFunc ℂ) :
    FieldShift.ratShiftEquiv
        (algebraMap (RatFunc ℂ) (RatFunc Constants) r) =
      algebraMap (RatFunc ℂ) (RatFunc Constants)
        (FieldShift.ratShiftEquiv r) := by
  exact (ratFuncCoeffMap_ratShift (algebraMap ℂ Constants) r).symm

theorem besselScalarRightShift_compat (r : RatFunc ℂ) :
    addTranslationMeroEquiv 1
        (algebraMap (RatFunc ℂ) (meroField Set.univ) r) =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
        (FieldShift.ratShiftEquiv r) :=
  addTranslationMeroEquiv_ratfuncToMero r

/-- Unit translation on the asymmetric Bessel scalar extension. -/
def besselScalarTensorShift : BesselScalarTensor ≃+* BesselScalarTensor :=
  asymmetricDifferenceTensorEquiv FieldShift.ratShiftEquiv
    FieldShift.ratShiftEquiv (addTranslationMeroEquiv 1)
    besselScalarLeftShift_compat besselScalarRightShift_compat

theorem besselScalarTensorShift_deriv (x : BesselScalarTensor) :
    besselScalarTensorShift (Differential.deriv x) =
      Differential.deriv (besselScalarTensorShift x) := by
  simpa only [besselScalarTensorShift] using
    (asymmetricDifferenceTensorEquiv_deriv
      (K := RatFunc ℂ) (A := RatFunc Constants) (B := meroField Set.univ)
      FieldShift.ratShiftEquiv FieldShift.ratShiftEquiv
      (addTranslationMeroEquiv 1) besselScalarLeftShift_compat
      besselScalarRightShift_compat besselRatShift_commutes
      (addTranslationMeroEquiv_deriv 1) x)

theorem besselScalarTensorShift_algebraMap (r : RatFunc Constants) :
    besselScalarTensorShift
        (algebraMap (RatFunc Constants) BesselScalarTensor r) =
      algebraMap (RatFunc Constants) BesselScalarTensor
        (FieldShift.ratShiftEquiv r) := by
  change besselScalarTensorShift (r ⊗ₜ[RatFunc ℂ] (1 : meroField Set.univ)) = _
  rw [besselScalarTensorShift, asymmetricDifferenceTensorEquiv_tmul, map_one]
  rfl

/-- Zeroth order value of the actual Bessel solution in the scalar extension. -/
def besselScalarY0 (s : ℝ) (hs : 0 < s) : BesselScalarTensor :=
  (1 : RatFunc Constants) ⊗ₜ[RatFunc ℂ] modifiedBesselKOrderMero s hs

/-- First order translate of the actual Bessel solution in the scalar extension. -/
def besselScalarY1 (s : ℝ) (hs : 0 < s) : BesselScalarTensor :=
  (1 : RatFunc Constants) ⊗ₜ[RatFunc ℂ]
    addTranslationMeroEquiv 1 (modifiedBesselKOrderMero s hs)

theorem besselScalarTensorShift_y0 (s : ℝ) (hs : 0 < s) :
    besselScalarTensorShift (besselScalarY0 s hs) = besselScalarY1 s hs := by
  rw [besselScalarY0, besselScalarY1, besselScalarTensorShift,
    asymmetricDifferenceTensorEquiv_tmul, map_one]

theorem besselScalarTensorShift_y1 (s : ℝ) (hs : 0 < s) :
    besselScalarTensorShift (besselScalarY1 s hs) =
      besselScalarY0 s hs +
        algebraMap (RatFunc Constants) BesselScalarTensor
            (FieldShift.orderShiftCoeff (slope s)) * besselScalarY1 s hs := by
  rw [besselScalarY1, besselScalarTensorShift,
    asymmetricDifferenceTensorEquiv_tmul, map_one,
    modifiedBesselKOrderMero_recurrence hs, TensorProduct.tmul_add]
  rw [show GaloisForLFunctions.HTGeometry.orderShiftCoeff (2 / (s : ℂ)) =
      FieldShift.orderShiftCoeff (2 / (s : ℂ)) by rfl]
  rw [show (1 : RatFunc Constants) ⊗ₜ[RatFunc ℂ]
      (algebraMap (RatFunc ℂ) (meroField Set.univ)
          (FieldShift.orderShiftCoeff (2 / (s : ℂ))) *
        addTranslationMeroEquiv 1 (modifiedBesselKOrderMero s hs)) =
      ((1 : RatFunc Constants) ⊗ₜ[RatFunc ℂ]
          algebraMap (RatFunc ℂ) (meroField Set.univ)
            (FieldShift.orderShiftCoeff (2 / (s : ℂ)))) *
        ((1 : RatFunc Constants) ⊗ₜ[RatFunc ℂ]
          addTranslationMeroEquiv 1 (modifiedBesselKOrderMero s hs)) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
  rw [besselScalarY0]
  have hcoeff : (1 : RatFunc Constants) ⊗ₜ[RatFunc ℂ]
        algebraMap (RatFunc ℂ) (meroField Set.univ)
          (FieldShift.orderShiftCoeff (2 / (s : ℂ))) =
      algebraMap (RatFunc Constants) BesselScalarTensor
        (FieldShift.orderShiftCoeff (slope s)) := by
    calc
      _ = algebraMap (RatFunc ℂ) (RatFunc Constants)
            (FieldShift.orderShiftCoeff (2 / (s : ℂ))) ⊗ₜ[RatFunc ℂ]
              (1 : meroField Set.univ) := by
          simpa only [Algebra.smul_def, mul_one] using
            (TensorProduct.smul_tmul
              (R := RatFunc ℂ)
              (FieldShift.orderShiftCoeff (2 / (s : ℂ)))
              (1 : RatFunc Constants) (1 : meroField Set.univ)).symm
      _ = FieldShift.orderShiftCoeff (slope s) ⊗ₜ[RatFunc ℂ]
            (1 : meroField Set.univ) := by
          rw [show algebraMap (RatFunc ℂ) (RatFunc Constants)
              (FieldShift.orderShiftCoeff (2 / (s : ℂ))) =
                FieldShift.orderShiftCoeff (slope s) by
            exact ratFuncCoeffMap_orderShiftCoeff (2 / (s : ℂ))]
      _ = _ := rfl
  rw [hcoeff]

/-- Determinant-one point whose first column is the actual Bessel solution. -/
def besselMeromorphicPPVMatrix (s : ℝ) (hs : 0 < s) :
    Matrix (Fin 2) (Fin 2) BesselScalarTensor :=
  !![besselScalarY0 s hs, 0;
    besselScalarY1 s hs,
      (1 : RatFunc Constants) ⊗ₜ[RatFunc ℂ] (modifiedBesselKOrderMero s hs)⁻¹]

def besselMeromorphicPPVPoint (s : ℝ) (hs : 0 < s) :
    Fin 2 × Fin 2 → BesselScalarTensor :=
  fun q => besselMeromorphicPPVMatrix s hs q.1 q.2

theorem besselMeromorphicPPVMatrix_det (s : ℝ) (hs : 0 < s) :
    (besselMeromorphicPPVMatrix s hs).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [besselMeromorphicPPVMatrix, besselScalarY0,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def,
    modifiedBesselKOrderMero_ne_zero hs]

def besselMeromorphicPPVPolynomialEval (s : ℝ) (hs : 0 < s) :
    DifferentialPolynomial (Fin 2 × Fin 2) (RatFunc Constants) →ₐ[RatFunc Constants]
      BesselScalarTensor :=
  differentialPolynomialEvalOver (besselMeromorphicPPVPoint s hs)

theorem besselMeromorphicPPVPolynomialEval_jetFundamentalMatrix
    (s : ℝ) (hs : 0 < s) :
    (jetFundamentalMatrix (RatFunc Constants) 2).map
        (besselMeromorphicPPVPolynomialEval s hs).toRingHom =
      besselMeromorphicPPVMatrix s hs := by
  ext i j
  simp [jetFundamentalMatrix, besselMeromorphicPPVPolynomialEval,
    besselMeromorphicPPVPoint]

theorem besselMeromorphicPPVPolynomialEval_jetFundamentalDet
    (s : ℝ) (hs : 0 < s) :
    besselMeromorphicPPVPolynomialEval s hs
        ((jetFundamentalMatrix (RatFunc Constants) 2).det) = 1 := by
  change (besselMeromorphicPPVPolynomialEval s hs).toRingHom
      ((jetFundamentalMatrix (RatFunc Constants) 2).det) = 1
  rw [RingHom.map_det, RingHom.mapMatrix_apply,
    besselMeromorphicPPVPolynomialEval_jetFundamentalMatrix,
    besselMeromorphicPPVMatrix_det]

/-- Differential evaluator from the determinant-localized universal Bessel PPV ring. -/
def besselMeromorphicPPVEval (s : ℝ) (hs : 0 < s) :
    ppvLocalization (RatFunc Constants) 2 →+* BesselScalarTensor :=
  IsLocalization.Away.lift ((jetFundamentalMatrix (RatFunc Constants) 2).det)
    (g := (besselMeromorphicPPVPolynomialEval s hs).toRingHom)
    (by
      rw [show (besselMeromorphicPPVPolynomialEval s hs).toRingHom
        ((jetFundamentalMatrix (RatFunc Constants) 2).det) = 1 by
          exact besselMeromorphicPPVPolynomialEval_jetFundamentalDet s hs]
      exact isUnit_one)

@[simp]
theorem besselMeromorphicPPVEval_algebraMap
    (s : ℝ) (hs : 0 < s)
    (P : DifferentialPolynomial (Fin 2 × Fin 2) (RatFunc Constants)) :
    besselMeromorphicPPVEval s hs (algebraMap _ _ P) =
      besselMeromorphicPPVPolynomialEval s hs P :=
  IsLocalization.Away.lift_eq _ _ _

theorem besselMeromorphicPPVEval_commutesDeriv
    (s : ℝ) (hs : 0 < s) (x : ppvLocalization (RatFunc Constants) 2) :
    besselMeromorphicPPVEval s hs (Differential.deriv x) =
      Differential.deriv (besselMeromorphicPPVEval s hs x) := by
  apply localization_ringHom_derivation_commutes_of_base
    (Submonoid.powers ((jetFundamentalMatrix (RatFunc Constants) 2).det))
    (ppvLocalizationDerivation (RatFunc Constants) 2) Differential.deriv
    (besselMeromorphicPPVEval s hs) _ x
  intro P
  rw [ppvLocalizationDerivation_algebraMap,
    besselMeromorphicPPVEval_algebraMap,
    besselMeromorphicPPVEval_algebraMap]
  exact differentialPolynomialEvalOver_derivation
    (besselMeromorphicPPVPoint s hs) P

theorem besselMeromorphicPPVEval_ppvFundamental
    (s : ℝ) (hs : 0 < s) (i j : Fin 2) :
    besselMeromorphicPPVEval s hs
        (ppvFundamental (RatFunc Constants) 2 i j) =
      besselMeromorphicPPVMatrix s hs i j := by
  change besselMeromorphicPPVEval s hs
      (algebraMap _ _ (jetFundamentalMatrix (RatFunc Constants) 2 i j)) = _
  rw [besselMeromorphicPPVEval_algebraMap]
  exact congrFun (congrFun
    (besselMeromorphicPPVPolynomialEval_jetFundamentalMatrix s hs) i) j

theorem besselMeromorphicPPVEval_base
    (s : ℝ) (hs : 0 < s) (r : RatFunc Constants) :
    besselMeromorphicPPVEval s hs
        (ppvBaseMap (RatFunc Constants) 2 r) =
      algebraMap (RatFunc Constants) BesselScalarTensor r := by
  change besselMeromorphicPPVEval s hs
      (algebraMap
        (DifferentialPolynomial (Fin 2 × Fin 2) (RatFunc Constants))
        (ppvLocalization (RatFunc Constants) 2) (MvPolynomial.C r)) = _
  rw [besselMeromorphicPPVEval_algebraMap]
  simp [besselMeromorphicPPVPolynomialEval]

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
