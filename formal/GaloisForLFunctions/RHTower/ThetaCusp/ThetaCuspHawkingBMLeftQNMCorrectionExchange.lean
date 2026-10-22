import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLeftQNMMetricEquation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedCorrectionBoundary

set_option autoImplicit false

/-!
# Complete mixed correction exchange with the actual left QNM metric

The original continued left mode supplies its full metric equation. This removes
exactly the independent-test Einstein residual from the complete nonlinear
correction discrepancy. Both correction/source pairings, the cubic linear work
and the original differentiated boundary divergences remain.
-/

namespace RHTower.D4BMLeftQNMCorrectionExchange
open Set GaloisForLFunctions.HTGeometry ComplexCoordinateMetricTwoJet
open D4BMMetricReconstruction D4BMPhysicalModeAction D4BMLeftModeRadialEquation
open D4BMWeightedCorrectionDiscrepancy D4BMInhomogeneousCorrectionBoundary
noncomputable section
local notation "Jet" => CoordinateMetricTwoJet 4 ℂ
local notation "Space" => ComplexMetricTwoJetSpace 4
local notation "AngularPoint" => {z : D4BMHorizon.Point // 0 < z 1}

def leftJet (r : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) (z : AngularPoint) : Jet :=
  ofMetricField (metricField r side outer) (modePoint t z.val z.property).val

private theorem field_symmetry (r : XiZeroCopy) (side outer : Bool) (x : Fin 4 → ℝ) (i j : Fin 4) :
    metricField r side outer x i j=metricField r side outer x j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem symmetric_eq (M : Jet) (hm : ∀ i j, M.metric i j=M.metric j i)
    (hf : ∀ k i j, M.first k i j=M.first k j i)
    (hs : ∀ k l i j, M.second k l i j=M.second k l j i) : symmetricCorrection M=M := by
  have average (a b : ℂ) (h : a=b) : (a+b)/2=a := by rw [← h]; ring
  cases M with
  | mk m f s =>
    unfold symmetricCorrection
    congr 1
    · funext i j
      change (m i j+m j i)/2=m i j
      exact average _ _ (hm i j)
    · funext k i j
      change (f k i j+f k j i)/2=f k i j
      exact average _ _ (hf k i j)
    · funext k l i j
      change (s k l i j+s k l j i)/2=s k l i j
      exact average _ _ (hs k l i j)

/-- Symmetrization preserves every actual left metric derivative slot. -/
theorem leftJet_symmetric (r : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) (z : AngularPoint) :
    symmetricCorrection (leftJet r side outer t z)=leftJet r side outer t z := by
  have h (i j : Fin 4) : ScalarTwoJet.ofField (fun x => metricField r side outer x i j)
      (modePoint t z.val z.property).val =
      ScalarTwoJet.ofField (fun x => metricField r side outer x j i) (modePoint t z.val z.property).val := by
    congr 1
    funext x
    exact field_symmetry r side outer x i j
  apply symmetric_eq
  · intro i j
    exact congrArg ScalarTwoJet.value (h i j)
  · intro k i j
    exact congrArg (fun J => J.first k) (h i j)
  · intro k l i j
    exact congrArg (fun J => J.second k l) (h i j)

/-- The actual left field equation removes precisely the displayed moving-weight residual. -/
theorem testResidualWork_zero (q r : XiZeroCopy) (b side outer : Bool) (aS aV : ℂ)
    (t : Iio (0:ℝ)) (z : AngularPoint) (A : Jet) :
    testResidualWork (modePoint t z.val z.property) q b aS aV A (leftJet r side outer t z)=0 := by
  have hE (i j : Fin 4) : CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.actualJet (modePoint t z.val z.property)) (leftJet r side outer t z) (-3) i j=0 := by
    rw [D4BMBackground.actualJet_eq]
    exact metricField_einstein r side outer t z i j
  simp only [testResidualWork,hE,mul_zero,Finset.sum_const_zero]

/-- Exact complete mixed-source exchange at the original left QNM, with both
independent quadratic channels and every original boundary defect retained. -/
theorem complete_mixed_exchange (q : Fin 2 → XiZeroCopy) (b : Fin 2 → Bool)
    (aS aV : Fin 2 → ℂ) (r : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ)) (z : AngularPoint)
    (K L B : Fin 4 → Space) (A : Fin 4 → Jet) :
    let p := modePoint t z.val z.property
    let M := leftJet r side outer t z
    mixedDiscrepancy p q b aS aV K L (fun i => toSpace (symmetricCorrection (A i))) B M.metric =
      linearWork p (B 1) M.metric+
      (exchangedSourceWork p (q 0) (b 0) (aS 0) (aV 0) (symmetricCorrection (A 1)) M+
        boundaryDefect p (q 0) (b 0) (aS 0) (aV 0) (symmetricCorrection (A 1)) M)+
      (exchangedSourceWork p (q 1) (b 1) (aS 1) (aV 1) (symmetricCorrection (A 0)) M+
        boundaryDefect p (q 1) (b 1) (aS 1) (aV 1) (symmetricCorrection (A 0)) M) := by
  have h := D4BMMixedCorrectionBoundary.complete_mixed_exchange (modePoint t z.val z.property)
    q b aS aV K L B A (leftJet r side outer t z)
  rw [leftJet_symmetric] at h
  simpa only [testResidualWork_zero,add_zero] using h

end
end RHTower.D4BMLeftQNMCorrectionExchange
