import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphicScalarExtension
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialSemilinearEval
import GaloisForLFunctions.HTGeometry.SigmaDeltaOrbitIdeal

/-!
# Relation-adapted Bessel parameterized Picard--Vessiot quotients

Any scalar differential relation satisfied by the actual meromorphic Bessel solution generates,
together with the normalized determinant relation, a proper sigma--delta orbit ideal in the
universal Bessel PPV coordinate ring.  Extending it to a maximal proper sigma--delta ideal produces
a genuine Bessel PPV datum in which that relation holds.
-/

open scoped Differential TensorProduct

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions Bottcher

noncomputable section

local instance : Differential ℂ := complexZeroDifferential
local instance : Differential (RatFunc ℂ) := coordinateTotalDifferential
local instance : Differential (RatFunc Constants) := coordinateTotalDifferential

local instance constantsDifferentialAlgebra : DifferentialAlgebra ℂ Constants :=
  DiffFieldExt.differentialAlgebra (diffClosureExt (F := ℂ))

local instance : Algebra (RatFunc ℂ) (RatFunc Constants) :=
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

local instance : Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance meromorphicDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  ⟨fun r => by
    change Differential.deriv
        (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ r) = _
    rw [show Differential.deriv r = coordinateTotalDerivation r by rfl,
      complex_coordinateTotalDerivation_eq_coordinateDerivation]
    exact meroField_deriv_ratfuncToMero r⟩

local instance : Differential BesselScalarTensor := tensorProductDifferential

local instance : DifferentialAlgebra (RatFunc Constants) BesselScalarTensor :=
  tensorProductDifferentialAlgebra_left

theorem ringEquiv_iterate_add {R : Type*} [Semiring R]
    (sigma : R ≃+* R) (m : ℕ) (x y : R) :
    ((sigma : R → R)^[m]) (x + y) =
      ((sigma : R → R)^[m]) x + ((sigma : R → R)^[m]) y := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', map_add, hm]

theorem ringEquiv_iterate_mul {R : Type*} [Semiring R]
    (sigma : R ≃+* R) (m : ℕ) (x y : R) :
    ((sigma : R → R)^[m]) (x * y) =
      ((sigma : R → R)^[m]) x * ((sigma : R → R)^[m]) y := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', map_mul, hm]

/-- Evaluate a scalar differential polynomial at the upper entry of the generic first column. -/
def besselScalarPPVRelation
    (P : DifferentialPolynomial Unit (RatFunc Constants)) :
    ppvLocalization (RatFunc Constants) 2 :=
  differentialPolynomialEvalOver
    (fun _ : Unit => ppvFundamental (RatFunc Constants) 2 0 0) P

theorem besselOrderPPVSigma_commutesDeriv
    (s : ℝ) (x : ppvLocalization (RatFunc Constants) 2) :
    besselOrderPPVSigma s (Differential.deriv x) =
      Differential.deriv (besselOrderPPVSigma s x) := by
  unfold besselOrderPPVSigma
  exact ppvSigma_commutes FieldShift.ratShiftEquiv besselRatShift_commutes
    (FieldShift.besselOrderCompanion (slope s)) (besselOrderCompanionInverse s)
    (besselOrderCompanion_mul_inverse s) (besselOrderCompanion_inverse_mul s) x

theorem besselOrderPPVSigma_fundamental_zero_zero (s : ℝ) :
    besselOrderPPVSigma s (ppvFundamental (RatFunc Constants) 2 0 0) =
      ppvFundamental (RatFunc Constants) 2 1 0 := by
  unfold besselOrderPPVSigma
  rw [ppvSigma_ppvFundamental]
  simp [FieldShift.besselOrderCompanion, Matrix.mul_apply, Fin.sum_univ_two]

theorem besselOrderPPVSigma_fundamental_one_zero (s : ℝ) :
    besselOrderPPVSigma s (ppvFundamental (RatFunc Constants) 2 1 0) =
      ppvFundamental (RatFunc Constants) 2 0 0 +
        ppvBaseMap (RatFunc Constants) 2
            (FieldShift.orderShiftCoeff (slope s)) *
          ppvFundamental (RatFunc Constants) 2 1 0 := by
  unfold besselOrderPPVSigma
  rw [ppvSigma_ppvFundamental]
  simp [FieldShift.besselOrderCompanion, Matrix.mul_apply, Fin.sum_univ_two]

theorem besselMeromorphicPPVEval_iterate_base
    (s : ℝ) (hs : 0 < s) (m : ℕ) (r : RatFunc Constants) :
    besselMeromorphicPPVEval s hs
        (((besselOrderPPVSigma s : _ → _)^[m])
          (ppvBaseMap (RatFunc Constants) 2 r)) =
      ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
        (algebraMap (RatFunc Constants) BesselScalarTensor r) := by
  induction m generalizing r with
  | zero => exact besselMeromorphicPPVEval_base s hs r
  | succ m hm =>
      rw [Function.iterate_succ_apply, besselOrderPPVSigma_base, hm,
        besselScalarTensorShift_algebraMap]
      rw [Function.iterate_succ_apply]

theorem besselMeromorphicPPVEval_iterate_firstColumn
    (s : ℝ) (hs : 0 < s) (m : ℕ) :
    besselMeromorphicPPVEval s hs
          (((besselOrderPPVSigma s : _ → _)^[m])
            (ppvFundamental (RatFunc Constants) 2 0 0)) =
        ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
          (besselScalarY0 s hs) ∧
      besselMeromorphicPPVEval s hs
          (((besselOrderPPVSigma s : _ → _)^[m])
            (ppvFundamental (RatFunc Constants) 2 1 0)) =
        ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
          (besselScalarY1 s hs) := by
  induction m with
  | zero =>
      constructor <;>
        simp [besselMeromorphicPPVEval_ppvFundamental,
          besselMeromorphicPPVMatrix, besselScalarY0, besselScalarY1]
  | succ m hm =>
      constructor
      · rw [Function.iterate_succ_apply, besselOrderPPVSigma_fundamental_zero_zero,
          hm.2, Function.iterate_succ_apply, besselScalarTensorShift_y0]
      · rw [Function.iterate_succ_apply,
          besselOrderPPVSigma_fundamental_one_zero,
          ringEquiv_iterate_add, ringEquiv_iterate_mul, map_add, map_mul,
          hm.1, hm.2,
          besselMeromorphicPPVEval_iterate_base,
          Function.iterate_succ_apply, besselScalarTensorShift_y1,
          ringEquiv_iterate_add, ringEquiv_iterate_mul]

theorem besselMeromorphicPPVEval_scalarRelation
    (s : ℝ) (hs : 0 < s)
    (P : DifferentialPolynomial Unit (RatFunc Constants)) :
    besselMeromorphicPPVEval s hs (besselScalarPPVRelation P) =
      differentialPolynomialEvalOver (K := RatFunc Constants)
        (fun _ : Unit => besselScalarY0 s hs) P := by
  have hmap := map_differentialPolynomialEvalOver
    (besselMeromorphicPPVEval s hs)
    (besselMeromorphicPPVEval_commutesDeriv s hs)
    (besselMeromorphicPPVEval_base s hs)
    (fun _ : Unit => ppvFundamental (RatFunc Constants) 2 0 0) P
  simpa [besselScalarPPVRelation, besselMeromorphicPPVMatrix,
    besselScalarY0] using hmap

theorem besselMeromorphicPPVEval_iterate_scalarRelation
    (s : ℝ) (hs : 0 < s)
    (P : DifferentialPolynomial Unit (RatFunc Constants)) (m : ℕ) :
    besselMeromorphicPPVEval s hs
        (((besselOrderPPVSigma s : _ → _)^[m])
          (besselScalarPPVRelation P)) =
      ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
        (differentialPolynomialEvalOver (K := RatFunc Constants)
          (fun _ : Unit => besselScalarY0 s hs) P) := by
  let Pm :=
    (((differentialPolynomialSigma FieldShift.ratShiftEquiv :
      DifferentialPolynomial Unit (RatFunc Constants) →
        DifferentialPolynomial Unit (RatFunc Constants))^[m]) P)
  have hsource := differentialPolynomialEvalOver_sigma_point_iterate
    (iota := Unit) FieldShift.ratShiftEquiv (besselOrderPPVSigma s)
    (besselOrderPPVSigma_base s) (besselOrderPPVSigma_commutesDeriv s)
    (fun _ : Unit => ppvFundamental (RatFunc Constants) 2 0 0) P m
  have heval := map_differentialPolynomialEvalOver
    (besselMeromorphicPPVEval s hs)
    (besselMeromorphicPPVEval_commutesDeriv s hs)
    (besselMeromorphicPPVEval_base s hs)
    (fun _ : Unit =>
      ((besselOrderPPVSigma s : _ → _)^[m])
        (ppvFundamental (RatFunc Constants) 2 0 0)) Pm
  have htarget := differentialPolynomialEvalOver_sigma_point_iterate
    (iota := Unit) FieldShift.ratShiftEquiv besselScalarTensorShift
    besselScalarTensorShift_algebraMap besselScalarTensorShift_deriv
    (fun _ : Unit => besselScalarY0 s hs) P m
  rw [← hsource]
  rw [heval]
  rw [show (fun _ : Unit => besselMeromorphicPPVEval s hs
        (((besselOrderPPVSigma s : _ → _)^[m])
          (ppvFundamental (RatFunc Constants) 2 0 0))) =
      (fun _ : Unit =>
        ((besselScalarTensorShift : BesselScalarTensor → BesselScalarTensor)^[m])
          (besselScalarY0 s hs)) by
    funext u
    exact (besselMeromorphicPPVEval_iterate_firstColumn s hs m).1]
  exact htarget

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
