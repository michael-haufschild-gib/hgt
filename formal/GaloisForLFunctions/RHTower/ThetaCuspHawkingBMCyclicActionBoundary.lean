import GaloisForLFunctions.HTGeometry.CoordinateEinsteinCyclicAction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralSourceReflection
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCorrectedMetricSource

set_option autoImplicit false

/-!
# Original cyclic action for the full physical theta-cusp metric family

Three independent Xi-labelled physical metrics retain both scalar and vector amplitudes.
Taking the complete spatial jet commutes with their actual affine field family. Intrinsic
background and mode identities give the cyclic bulk-and-boundary cubic action without
supplied geometric or field-equation premises. Global Peierls incidence, the common-cutoff
boundary limit, and fixed-clock extinction remain separate.
-/
open scoped ContDiff BigOperators

namespace RHTower.D4BMCyclicAction
open GaloisForLFunctions.HTGeometry
open EinsteinCyclicVariation D4BMBackground D4BMMetricReconstruction
open D4BMActualMetricSource
noncomputable section

/-- Three independent original Xi-labelled metric fields, with both amplitudes retained. -/
def modes (q : Fin 3 → XiZeroCopy) (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ)
    (k : Fin 3) : MetricField := D4BMLiteralCusp.physicalPerturbation (q k) (b k) (aS k) (aV k)

/-- Every derivative of the original fields is taken before evaluating at the exterior point. -/
def jets (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy) (b : Fin 3 → Bool)
    (aS aV : Fin 3 → ℂ) (k : Fin 3) : CoordinateMetricTwoJet 4 ℂ :=
  ofMetricField (modes q b aS aV k) p.val

private theorem background_symm (x : Fin 4 → ℝ) (i j : Fin 4) :
    metric (x 1) (x 3) i j = metric (x 1) (x 3) j i := by
  by_cases hij : i = j
  · subst j; rfl
  · simp [metric, hij, Ne.symm hij]

private theorem mode_symm (q : XiZeroCopy) (b : Bool) (aS aV : ℂ)
    (x : Fin 4 → ℝ) (i j : Fin 4) :
    D4BMLiteralCusp.physicalPerturbation q b aS aV x i j =
      D4BMLiteralCusp.physicalPerturbation q b aS aV x j i := by
  let omega := Complex.I * D4BMModularCore.physicalRate q b
  let u := D4BMGlobalAngularResponse.center q
  let a := fun c => D4BMFundamentalMetric.primitives omega aS aV
    (D4BMLiteralCusp.scalar u) (D4BMLiteralCusp.vector u) c x
  have hs := congrArg (fun e : ScalarTwoJet.Expression Primitive => e.eval a)
    (covariantMetricExpression_symm omega (D4BMLiteralCusp.scalarQ u) i j)
  rw [covariantMetricExpression_eval, covariantMetricExpression_eval] at hs
  exact hs

private theorem field_first_symm (h : MetricField)
    (hs : ∀ x i j, h x i j = h x j i) (x : Fin 4 → ℝ) (l i j : Fin 4) :
    (ofMetricField h x).first l i j = (ofMetricField h x).first l j i := by
  have he : (fun y => h y i j) = (fun y => h y j i) := funext fun y => hs y i j
  change (ScalarTwoJet.ofField (fun y => h y i j) x).first l =
    (ScalarTwoJet.ofField (fun y => h y j i) x).first l
  rw [he]

private theorem mode_smooth (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => D4BMLiteralCusp.physicalPerturbation q b aS aV x i j) p.val :=
  D4BMFullLinearEquation.literal_contDiffAt p
    (Complex.I * D4BMModularCore.physicalRate q b) (D4BMGlobalAngularResponse.center q) aS aV i j

private theorem fieldSpace_sum (p : ExteriorPoint) (F : Fin 3 → MetricField)
    (hF : ∀ v i j, ContDiffAt ℝ 2 (fun x => F v x i j) p.val) (s : Finset (Fin 3)) :
    ComplexCoordinateMetricTwoJet.toSpace (ofMetricField (fun x => ∑ v ∈ s, F v x) p.val) =
      ∑ v ∈ s, fieldSpace p (F v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext l i j
        change (ScalarTwoJet.ofField (fun _ => (0:ℂ)) p.val).first l = 0
        rw [ScalarTwoJet.ofField_constant]
        rfl
      · funext l m i j
        change (ScalarTwoJet.ofField (fun _ => (0:ℂ)) p.val).second l m = 0
        rw [ScalarTwoJet.ofField_constant]
        rfl
  | @insert v s hv ih =>
    have hsum (i j : Fin 4) : ContDiffAt ℝ 2 (fun x => (∑ w ∈ s, F w x) i j) p.val := by
      simp only [Matrix.sum_apply]
      exact ContDiffAt.sum fun w _ => hF w i j
    have he : (fun x => ∑ w ∈ insert v s, F w x) =
        (fun x => F v x + ∑ w ∈ s, F w x) := by
      funext x
      exact Finset.sum_insert hv
    rw [he, D4BMFullLinearEquation.fieldSpace_add p (F v) _ (hF v) hsum,
      ih, Finset.sum_insert hv]
    rfl

/-- The full metric family is formed before any spatial differentiation. -/
def metricFamily (q : Fin 3 → XiZeroCopy) (b : Fin 3 → Bool)
    (aS aV a : Fin 3 → ℂ) : MetricField :=
  fun x => metric (x 1) (x 3) + ∑ k, a k • modes q b aS aV k x

/-- Identification with the complete actual field jet, including every ordered second partial. -/
theorem metricFamily_jet (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV a : Fin 3 → ℂ) :
    ofMetricField (metricFamily q b aS aV a) p.val =
      family (actualJet p) (jets p q b aS aV) a := by
  let F : Fin 3 → MetricField := fun v x => a v • modes q b aS aV v x
  have hF (v : Fin 3) (i j : Fin 4) : ContDiffAt ℝ 2 (fun x => F v x i j) p.val :=
    contDiffAt_const.mul (mode_smooth p (q v) (b v) (aS v) (aV v) i j)
  have hsum (i j : Fin 4) : ContDiffAt ℝ 2 (fun x => (∑ v, F v x) i j) p.val := by
    simp only [Matrix.sum_apply]
    exact ContDiffAt.sum fun v _ => hF v i j
  have he : ComplexCoordinateMetricTwoJet.toSpace
      (ofMetricField (metricFamily q b aS aV a) p.val) =
      ComplexCoordinateMetricTwoJet.toSpace (actualJet p) +
        ∑ v, a v • ComplexCoordinateMetricTwoJet.toSpace (jets p q b aS aV v) := by
    change ComplexCoordinateMetricTwoJet.toSpace
      (ofMetricField (fun x => metric (x 1) (x 3) + ∑ v, F v x) p.val) = _
    rw [D4BMFullLinearEquation.fieldSpace_add p _ _ (fun i j => exterior_metric_contDiffAt p i j) hsum,
      fieldSpace_sum p F hF Finset.univ]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro v _
    exact D4BMCorrectedMetricSource.fieldSpace_smul p (modes q b aS aV v)
      (mode_smooth p (q v) (b v) (aS v) (aV v)) (a v)
  exact congrArg ComplexCoordinateMetricTwoJet.ofSpace he

/-- Actual theta-cusp metrics satisfy cyclicity of the original bulk-and-boundary cubic action.
No nondegeneracy, symmetry, field equation or boundary cancellation is supplied as a premise. -/
theorem physical_cubicAction_cyclic (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ) (i j k : Fin 3) :
    cubicAction (actualJet p) (jets p q b aS aV) (-3) i j k =
      cubicAction (actualJet p) (jets p q b aS aV) (-3) i k j := by
  apply cubicAction_cyclic
  · exact exterior_metric_det_ne_zero p
  · exact background_symm p.val
  · exact field_first_symm _ background_symm p.val
  · intro v
    exact mode_symm (q v) (b v) (aS v) (aV v) p.val
  · intro v
    exact field_first_symm _ (mode_symm (q v) (b v) (aS v) (aV v)) p.val

/-- The physical cubic coefficient is exactly the negative third variation of the original
Einstein--Hilbert density, with no supplied symmetry or boundary-cancellation premise. -/
theorem physical_cubicAction_eq_density_third (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ) (i j k : Fin 3) :
    cubicAction (actualJet p) (jets p q b aS aV) (-3) i j k =
      -parameterDeriv (parameterDeriv (parameterDeriv
        (density (actualJet p) (jets p q b aS aV) (-3)) k) j) i 0 := by
  apply cubicAction_eq_density_third
  · exact exterior_metric_det_ne_zero p
  · exact background_symm p.val
  · exact field_first_symm _ background_symm p.val
  · intro v
    exact mode_symm (q v) (b v) (aS v) (aV v) p.val
  · intro v
    exact field_first_symm _ (mode_symm (q v) (b v) (aS v) (aV v)) p.val

end
end RHTower.D4BMCyclicAction
