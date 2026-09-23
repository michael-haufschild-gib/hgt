import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMForcedMetricTensor
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMetricLinearCombination

/-! The constructed metric field solving every original forced mixed Einstein component. -/

open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMMetricReconstruction D4BMGlobalAngularResponse
noncomputable section

/-- The complete particular mixed response, constructed from the actual global inverse
and original squared scalar, with both radial stream factors retained. -/
def forcedMetricField (q : XiZeroCopy) (branch : Bool) (a : ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let s := physicalRate q branch
  fun i j => streamMetricField (2*s) (a^(2 : ℕ)) false (fullAngularCovector q branch) x i j-
    (s*(s-1)/4)*streamMetricField (2*s) (a^(2 : ℕ)) true (fullSquareCovector q) x i j

private theorem response_c2 (q : XiZeroCopy) (branch : Bool) (p : D4BMBackground.ExteriorPoint)
    (k : Fin 2) : ContDiffAt ℝ 2 (fullAngularCovector q branch k) (angularPoint p.val) := by
  have h := (contDiffAt_infty.mp (fullAngularCovector_smooth q branch (angularPoint p.val) p.property.2 k)) 2
  norm_num at h
  exact h

private theorem square_c2 (q : XiZeroCopy) (p : D4BMBackground.ExteriorPoint) (k : Fin 2) :
    ContDiffAt ℝ 2 (fullSquareCovector q k) (angularPoint p.val) := by
  simpa using fullSquareCovector_smooth q (angularPoint p.val) p.property.2 2 k

/-- Every metric component of the constructed response has actual continuous second derivatives. -/
theorem forcedMetricField_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => forcedMetricField q branch a x i j) p.val :=
  (streamMetricField_smooth _ _ false _ p (response_c2 q branch p) i j).sub
    (contDiffAt_const.mul (streamMetricField_smooth _ _ true _ p (square_c2 q p) i j))

/-- The constructed full metric solves all sixteen forced mixed Einstein equations
with the original source normalization and every actual coordinate derivative retained. -/
theorem forcedMetricField_einstein (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (forcedMetricField q branch a) p.val) (-3) i j +
      literalMixedSource q branch (p.val 1)
        (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) a p.val) (angularPoint p.val) i j = 0 := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  have hJ : (D4BMBackground.jet (p.val 1) (p.val 3)).metric.det ≠ 0 := by
    change (D4BMBackground.metric (p.val 1) (p.val 3)).det ≠ 0
    rw [D4BMBackground.metric_det _ _ hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 4 hr) (pow_ne_zero 4 (inv_ne_zero hy)))
  unfold forcedMetricField
  rw [ofMetricField_combination _ _ _ p.val
    (streamMetricField_smooth _ _ false _ p (response_c2 q branch p))
    (streamMetricField_smooth _ _ true _ p (square_c2 q p)),
    cosmological_metricJetCombination _ _ _ hJ,
    streamMetricField_einstein _ _ false _ p (response_c2 q branch p) (fullAngularCovector_divergence q branch),
    streamMetricField_einstein _ _ true _ p (square_c2 q p) (fullSquareCovector_divergence q),
    envelope_double,streamMetricTensor_forced q branch p]
  ring

end
end RHTower.D4BMModularCore
