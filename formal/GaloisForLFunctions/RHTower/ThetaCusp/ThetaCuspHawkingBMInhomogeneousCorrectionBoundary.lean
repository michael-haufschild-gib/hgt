import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMWeightedCorrectionDiscrepancy
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinOnShellPairing
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuadraticMixedSource

set_option autoImplicit false

/-!
# Original Einstein exchange with an inhomogeneous correction

The original physical first mode discharges only its own linear equation. The
full symmetric correction retains its cosmological Einstein residual and the
actual changing test weight. Exchanging the correction with an independent full test
retains that test's Einstein residual and the original differentiated boundary divergence. The explicit mixed
ingoing correction is included without assuming its linear residual vanishes.
-/

open scoped ContDiff BigOperators
namespace RHTower.D4BMInhomogeneousCorrectionBoundary
open GaloisForLFunctions.HTGeometry
open EinsteinCyclicVariation EinsteinOnShellPairing ComplexCoordinateMetricTwoJet
open D4BMBackground D4BMActualMetricSource D4BMMetricReconstruction
open D4BMWeightedCorrectionDiscrepancy
noncomputable section
local notation "Jet" => CoordinateMetricTwoJet 4 ℂ

/-- Complex symmetric correction data under transpose, retaining every ordered spatial derivative. -/
def symmetricCorrection (A : Jet) : Jet where
  metric i j := (A.metric i j+A.metric j i)/2
  first k i j := (A.first k i j+A.first k j i)/2
  second k l i j := (A.second k l i j+A.second k l j i)/2

private theorem symmetricCorrection_metric (A : Jet) (i j : Fin 4) :
    (symmetricCorrection A).metric i j=(symmetricCorrection A).metric j i := by
  simp only [symmetricCorrection,add_comm]

private theorem symmetricCorrection_first (A : Jet) (k i j : Fin 4) :
    (symmetricCorrection A).first k i j=(symmetricCorrection A).first k j i := by
  simp only [symmetricCorrection,add_comm]

private def modeJet (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool) (aS aV : ℂ) : Jet :=
  ofMetricField (D4BMLiteralCusp.physicalPerturbation q b aS aV) p.val

private theorem modeJet_space (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool) (aS aV : ℂ) :
    toSpace (modeJet p q b aS aV)=mode p q b aS aV := rfl

private theorem background_symm (x : Fin 4 → ℝ) (i j : Fin 4) :
    metric (x 1) (x 3) i j=metric (x 1) (x 3) j i := by
  by_cases hij : i=j
  · subst j; rfl
  · simp [metric,hij,Ne.symm hij]

private theorem mode_symm (q : XiZeroCopy) (b : Bool) (aS aV : ℂ)
    (x : Fin 4 → ℝ) (i j : Fin 4) :
    D4BMLiteralCusp.physicalPerturbation q b aS aV x i j=
      D4BMLiteralCusp.physicalPerturbation q b aS aV x j i := by
  let omega := Complex.I*D4BMModularCore.physicalRate q b
  let u := D4BMGlobalAngularResponse.center q
  let a := fun c => D4BMFundamentalMetric.primitives omega aS aV
    (D4BMLiteralCusp.scalar u) (D4BMLiteralCusp.vector u) c x
  have hs := congrArg (fun e : ScalarTwoJet.Expression Primitive => e.eval a)
    (covariantMetricExpression_symm omega (D4BMLiteralCusp.scalarQ u) i j)
  rw [covariantMetricExpression_eval,covariantMetricExpression_eval] at hs
  exact hs

private theorem field_first_symm (h : MetricField)
    (hs : ∀ x i j, h x i j=h x j i) (x : Fin 4 → ℝ) (l i j : Fin 4) :
    (ofMetricField h x).first l i j=(ofMetricField h x).first l j i := by
  have he : (fun y => h y i j)=(fun y => h y j i) := funext fun y => hs y i j
  change (ScalarTwoJet.ofField (fun y => h y i j) x).first l=
    (ScalarTwoJet.ofField (fun y => h y j i) x).first l
  rw [he]

private theorem mode_linear_zero (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (actualJet p) (modeJet p q b aS aV) (-3) i j=0 := by
  change D4BMLinearizedEinsteinSource.residual p (modeJet p q b aS aV) i j=0
  rw [modeJet,← (D4BMLinearizedEinsteinSource.source_hasDerivAt p
    (D4BMLiteralCusp.physicalPerturbation q b aS aV)
    (D4BMFullLinearEquation.literal_contDiffAt p (Complex.I*D4BMModularCore.physicalRate q b)
      (D4BMGlobalAngularResponse.center q) aS aV) i j).deriv]
  exact D4BMLiteralCusp.physicalPerturbation_first_source_zero q b aS aV p i j

/-- The original first source, full correction and independent full test jet. -/
def sourceJets (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (A M : Jet) : Fin 3 → Jet := ![modeJet p q b aS aV,A,M]

@[simp] private theorem sourceJets_zero (p : ExteriorPoint) (q : XiZeroCopy)
    (b : Bool) (aS aV : ℂ) (A M : Jet) :
    sourceJets p q b aS aV A M 0=modeJet p q b aS aV := rfl
@[simp] private theorem sourceJets_one (p : ExteriorPoint) (q : XiZeroCopy)
    (b : Bool) (aS aV : ℂ) (A M : Jet) : sourceJets p q b aS aV A M 1=A := rfl
@[simp] private theorem sourceJets_two (p : ExteriorPoint) (q : XiZeroCopy)
    (b : Bool) (aS aV : ℂ) (A M : Jet) : sourceJets p q b aS aV A M 2=M := rfl

/-- The original boundary divergence is differentiated before any physical integration. -/
def boundaryDefect (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (A M : Jet) : ℂ :=
  parameterDeriv (parameterDeriv (boundary (actualJet p) (sourceJets p q b aS aV A M) 2) 1) 0 0-
    parameterDeriv (parameterDeriv (boundary (actualJet p) (sourceJets p q b aS aV A M) 1) 2) 0 0

/-- Work of the unchanged correction against the original quadratic Einstein source. -/
def exchangedSourceWork (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (A M : Jet) : ℂ :=
  ∑ i,∑ j,fixedWeight p A.metric i j*secondVariation (backgroundSpace p) i j
    (mode p q b aS aV) (toSpace M)

/-- The independent test's complete Einstein residual remains part of the exchange. -/
def testResidualWork (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (A M : Jet) : ℂ :=
  ∑ i,∑ j,movingWeight p (mode p q b aS aV) A.metric i j*
    CoordinateMetricTwoJet.Linearization.cosmological (actualJet p) M (-3) i j

private theorem correction_exchange (p : ExteriorPoint) (q : XiZeroCopy)
    (b : Bool) (aS aV : ℂ) (A M : Jet)
    (hAs : ∀ i j, A.metric i j=A.metric j i)
    (hAf : ∀ k i j, A.first k i j=A.first k j i)
    (hMs : ∀ i j, M.metric i j=M.metric j i)
    (hMf : ∀ k i j, M.first k i j=M.first k j i) :
    correctionWork p (mode p q b aS aV) (toSpace A) M.metric=
      exchangedSourceWork p q b aS aV A M+testResidualWork p q b aS aV A M+
        boundaryDefect p q b aS aV A M := by
  have hzero (i j : Fin 4) : (actualJet p).einstein i j+(-3:ℂ)*(actualJet p).metric i j=0 := by
    simpa only [neg_mul,sub_eq_add_neg] using exterior_vacuum p i j
  have hb := bulk_second_eq_hessian_and_weights (actualJet p) (sourceJets p q b aS aV A M)
    (-3) (exterior_metric_det_ne_zero p) hzero 0 1 2
  have hc := bulk_second_eq_hessian_and_weights (actualJet p) (sourceJets p q b aS aV A M)
    (-3) (exterior_metric_det_ne_zero p) hzero 0 2 1
  have hb' : parameterDeriv (parameterDeriv
      (bulk (actualJet p) (sourceJets p q b aS aV A M) (-3) 2) 1) 0 0=
      correctionWork p (mode p q b aS aV) (toSpace A) M.metric := by
    rw [hb]
    simp only [sourceJets_zero,sourceJets_one,sourceJets_two,mode_linear_zero,mul_zero,add_zero]
    simp only [correctionWork,fixedWeight,movingWeight,linear_original,
      D4BMLinearizedEinsteinSource.residual,ofSpace_toSpace,modeJet_space]
    rfl
  have hc' : parameterDeriv (parameterDeriv
      (bulk (actualJet p) (sourceJets p q b aS aV A M) (-3) 1) 2) 0 0=
      exchangedSourceWork p q b aS aV A M+testResidualWork p q b aS aV A M := by
    rw [hc]
    simp only [sourceJets_zero,sourceJets_one,sourceJets_two,mode_linear_zero,mul_zero,add_zero,
      exchangedSourceWork,testResidualWork,fixedWeight,movingWeight,modeJet_space,
      ← Finset.sum_add_distrib]
    rfl
  have hs : ∀ v i j, (sourceJets p q b aS aV A M v).metric i j=
      (sourceJets p q b aS aV A M v).metric j i := by
    intro v i j
    fin_cases v
    · exact mode_symm q b aS aV p.val i j
    · exact hAs i j
    · exact hMs i j
  have hf : ∀ v l i j, (sourceJets p q b aS aV A M v).first l i j=
      (sourceJets p q b aS aV A M v).first l j i := by
    intro v l i j
    fin_cases v
    · exact field_first_symm _ (mode_symm q b aS aV) p.val l i j
    · exact hAf l i j
    · exact hMf l i j
  have he := paired_cyclicity_defect (actualJet p) (sourceJets p q b aS aV A M) (-3)
    (exterior_metric_det_ne_zero p) (background_symm p.val)
    (field_first_symm _ background_symm p.val) hs hf 0 1 2
  rw [hb',hc'] at he
  change _=boundaryDefect p q b aS aV A M at he
  exact eq_add_of_sub_eq' he

/-- The full independent test residual and original boundary defect both survive the source exchange. -/
theorem physical_correction_exchange (p : ExteriorPoint) (q : XiZeroCopy)
    (b : Bool) (aS aV : ℂ) (A M : Jet) :
    correctionWork p (mode p q b aS aV) (toSpace (symmetricCorrection A))
      (symmetricCorrection M).metric=
      exchangedSourceWork p q b aS aV (symmetricCorrection A) (symmetricCorrection M)+
        testResidualWork p q b aS aV (symmetricCorrection A) (symmetricCorrection M)+
        boundaryDefect p q b aS aV (symmetricCorrection A) (symmetricCorrection M) :=
  correction_exchange p q b aS aV _ _ (symmetricCorrection_metric A) (symmetricCorrection_first A)
    (symmetricCorrection_metric M) (symmetricCorrection_first M)

/-- An independent original Xi test discharges its full Einstein residual from the same exchange. -/
theorem physical_mode_correction_exchange (p : ExteriorPoint) (q r : XiZeroCopy)
    (b c : Bool) (aS aV mS mV : ℂ) (A : Jet) :
    correctionWork p (mode p q b aS aV) (toSpace (symmetricCorrection A))
      (mode p r c mS mV).1=
      exchangedSourceWork p q b aS aV (symmetricCorrection A) (ofSpace (mode p r c mS mV))+
        boundaryDefect p q b aS aV (symmetricCorrection A) (ofSpace (mode p r c mS mV)) := by
  have he := correction_exchange p q b aS aV (symmetricCorrection A) (modeJet p r c mS mV)
    (symmetricCorrection_metric A) (symmetricCorrection_first A)
    (mode_symm r c mS mV p.val) (field_first_symm _ (mode_symm r c mS mV) p.val)
  change correctionWork p (mode p q b aS aV) (toSpace (symmetricCorrection A))
      (modeJet p r c mS mV).metric=
    exchangedSourceWork p q b aS aV (symmetricCorrection A) (modeJet p r c mS mV)+
      boundaryDefect p q b aS aV (symmetricCorrection A) (modeJet p r c mS mV)
  simpa only [testResidualWork,mode_linear_zero,mul_zero,Finset.sum_const_zero,add_zero] using he

/-- The original full mixed ingoing correction obeys the same exchange at the actual exterior radius and height. -/
theorem original_mixed_correction_exchange (p : ExteriorPoint) (q : XiZeroCopy)
    (b : Bool) (aS aV : ℂ) (M : Jet)
    (s B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    let A := D4BMQuadraticMixedSource.correctionJet s (p.val 1) (p.val 3) B S Sx Sy Sxx Sxy Sxxx Sxxy
    correctionWork p (mode p q b aS aV) (toSpace A) (symmetricCorrection M).metric=
      exchangedSourceWork p q b aS aV A (symmetricCorrection M)+
        testResidualWork p q b aS aV A (symmetricCorrection M)+
        boundaryDefect p q b aS aV A (symmetricCorrection M) := by
  apply correction_exchange
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro k i j
    fin_cases i <;> fin_cases j <;> rfl
  · exact symmetricCorrection_metric M
  · exact symmetricCorrection_first M

end
end RHTower.D4BMInhomogeneousCorrectionBoundary
