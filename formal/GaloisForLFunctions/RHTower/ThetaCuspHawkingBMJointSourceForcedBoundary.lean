import GaloisForLFunctions.HTGeometry.BochnerLaplaceHolomorphy
import GaloisForLFunctions.HTGeometry.HilbertHalfPlaneBoundary
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCausalCuspSourceIdentification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointVectorBoundary

/-! The complete physical time source gives one Hardy boundary of the original joint inverse. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def causalResponseShift (q : XiZeroCopy) : ℝ := causalGreenThreshold q+1

theorem causalResponseShift_pos (q : XiZeroCopy) : 0 < causalResponseShift q := by
  have ht := causalPrincipalThreshold_pos q
  have hm : causalPrincipalThreshold q ≤ causalGreenThreshold q := le_max_left _ _
  unfold causalResponseShift
  linarith

/-- One transform of the actual frequency-independent source in the original spatial space. -/
def causalCuspLaplace (q : XiZeroCopy) (branch : Bool) (a : ℂ) : ℂ → SpatialSpace :=
  bochnerLaplaceRay (causalCuspSourceVector q branch a)

theorem causalCuspSource_shift_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    IntegrableOn (fun t => expRay (causalResponseShift q : ℂ) t • causalCuspSourceVector q branch a t)
      (Ioi (0 : ℝ)) := by
  have hi := causalCuspSourceVector_laplace_integrable q branch a (causalResponseShift q)
    (by simp only [Complex.ofReal_re,causalResponseShift,causalGreenThreshold];
        have := le_max_left (causalPrincipalThreshold q) (principalThreshold q); linarith)
  simpa only [expRay,neg_mul] using hi

def causalCuspLaplaceBound (q : XiZeroCopy) (branch : Bool) (a : ℂ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), ‖expRay (causalResponseShift q : ℂ) t • causalCuspSourceVector q branch a t‖

theorem causalCuspLaplace_bound (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q ≤ w.re) : ‖causalCuspLaplace q branch a w‖ ≤ causalCuspLaplaceBound q branch a :=
  bochnerLaplaceRay_norm_le (causalCuspSource_shift_integrable q branch a) w hw

theorem causalCuspLaplace_differentiableAt (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q < w.re) : DifferentiableAt ℂ (causalCuspLaplace q branch a) w :=
  bochnerLaplaceRay_differentiableAt (causalCuspSourceVector_continuous q branch a).aestronglyMeasurable
    (causalCuspSource_shift_integrable q branch a) w hw

/-- This family uses the original inverse applied to the complete physical source transform. -/
def causalJointFrequencyResponse (q : XiZeroCopy) (branch : Bool) (a w : ℂ) : SpatialSpace :=
  waveSpatialResolvent jointEmbedding w (causalCuspLaplace q branch a w)

theorem causalJointFrequencyResponse_differentiableAt (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q < w.re) : DifferentiableAt ℂ (causalJointFrequencyResponse q branch a) w := by
  have hw₀ : 0 < w.re := (causalResponseShift_pos q).trans hw
  exact jointEmbedding.differentiableAt.comp w
    ((waveEnergyInverse_differentiableAt jointEmbedding jointEmbedding_norm_le w hw₀).clm_apply
      (jointEmbedding.adjoint.differentiableAt.comp w (causalCuspLaplace_differentiableAt q branch a w hw)))

/-- All Hardy and vector bounds are discharged from the actual source and original inverse. -/
def causalJointForcedBoundary (q : XiZeroCopy) (branch : Bool) (a : ℂ) : CauchyBoundedHilbertMap SpatialSpace where
  value := fun w => causalJointFrequencyResponse q branch a (w+causalResponseShift q)
  shift := causalResponseShift q
  shift_pos := causalResponseShift_pos q
  bound := causalCuspLaplaceBound q branch a / causalResponseShift q
  holo := by
    intro w hw
    exact (causalJointFrequencyResponse_differentiableAt q branch a (w+causalResponseShift q)
      (by simp only [Complex.add_re,Complex.ofReal_re]; linarith)).comp w
        (differentiableAt_id.add_const _)
  norm_le := by
    intro w hw
    have hb := shiftedWaveVector_bound jointEmbedding jointEmbedding_norm_le
      (causalCuspLaplace q branch a (w+causalResponseShift q))
      (causalResponseShift q) (causalResponseShift_pos q) w hw
    have hs := causalCuspLaplace_bound q branch a (w+causalResponseShift q)
      (by simp only [Complex.add_re,Complex.ofReal_re]; linarith)
    exact hb.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hs (causalResponseShift_pos q).le) (norm_nonneg _))

/-- The input retained by the inverse is exactly the literal cusp residual in its Green chamber. -/
theorem causalCuspLaplace_original (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalGreenThreshold q < w.re) :
    causalCuspLaplace q branch a w =
      cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w)
        (principalChamber_of_threshold q w ((le_max_right _ _).trans_lt hw)) := by
  simpa only [causalCuspLaplace,bochnerLaplaceRay,expRay,neg_mul] using
    causalCuspSourceVector_laplace_original q branch a w hw

end
end RHTower.D4BMJointSource
