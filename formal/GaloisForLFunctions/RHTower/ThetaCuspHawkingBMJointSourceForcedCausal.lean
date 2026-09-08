import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceForcedBoundary
import GaloisForLFunctions.HTGeometry.HilbertHalfPlaneCausal

/-! A frequency-independent causal joint response to the full literal cusp source. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Undo only the fixed convergence shift of the original source-resolvent product. -/
def causalJointForcedResponse (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) : SpatialSpace :=
  (Real.exp (causalResponseShift q*t) : ℂ) • (causalJointForcedBoundary q branch a).causalDatum t

theorem causalJointForcedResponse_support (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t < 0 → causalJointForcedResponse q branch a t = 0 := by
  filter_upwards [(causalJointForcedBoundary q branch a).causalDatum_support] with t ht hneg
  simp only [causalJointForcedResponse,ht hneg,smul_zero]

theorem causalJointForcedResponse_integrand (q : XiZeroCopy) (branch : Bool) (a w : ℂ) (t : ℝ) :
    expRay w t • causalJointForcedResponse q branch a t =
      expRay (w-causalResponseShift q) t • (causalJointForcedBoundary q branch a).causalDatum t := by
  simp only [causalJointForcedResponse,smul_smul,expRay,Complex.ofReal_exp,Complex.ofReal_mul,← Complex.exp_add]
  congr 2
  ring

/-- The response is an admitted exponentially weighted spatial-vector L² time family. -/
theorem causalJointForcedResponse_weighted_memLp (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    MemLp (fun t => expRay ((causalResponseShift q : ℂ)+1) t • causalJointForcedResponse q branch a t)
      2 volume := by
  have he : (causalResponseShift q : ℂ)+1-causalResponseShift q = 1 := by ring
  simpa only [causalJointForcedResponse_integrand,he] using
    (causalJointForcedBoundary q branch a).causalDatum_weighted_memLp

/-- Actual absolute Bochner convergence, with no supplied time-growth estimate. -/
theorem causalJointForcedResponse_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q+1 < w.re) :
    IntegrableOn (fun t => expRay w t • causalJointForcedResponse q branch a t) (Ioi (0 : ℝ)) := by
  have hi := (causalJointForcedBoundary q branch a).causalDatum_integrable (w-causalResponseShift q)
    (by simp only [Complex.sub_re,Complex.ofReal_re]; linarith)
  simpa only [causalJointForcedResponse_integrand] using hi

/-- The transform is the original inverse applied to the actual complete source transform. -/
theorem causalJointForcedResponse_laplace (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q+1 < w.re) :
    (∫ t in Ioi (0 : ℝ), expRay w t • causalJointForcedResponse q branch a t) =
      causalJointFrequencyResponse q branch a w := by
  simp only [causalJointForcedResponse_integrand]
  rw [(causalJointForcedBoundary q branch a).causalDatum_laplace _
    (by simp only [Complex.sub_re,Complex.ofReal_re]; linarith)]
  change causalJointFrequencyResponse q branch a (w-causalResponseShift q+causalResponseShift q) = _
  rw [sub_add_cancel]

/-- The causal response transforms to the exact original joint response of the literal cusp residual. -/
theorem causalJointForcedResponse_laplace_original (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q+1 < w.re) :
    (∫ t in Ioi (0 : ℝ), expRay w t • causalJointForcedResponse q branch a t) =
      jointEmbedding (jointWaveResponse w
        (by have := causalResponseShift_pos q; linarith)
        (cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w)
          (principalChamber_of_threshold q w (by
            have := le_max_right (causalPrincipalThreshold q) (principalThreshold q)
            unfold causalResponseShift causalGreenThreshold at hw
            linarith)))) := by
  have hw₀ : 0 < w.re := by have := causalResponseShift_pos q; linarith
  have ht : causalGreenThreshold q < w.re := by unfold causalResponseShift at hw; linarith
  rw [causalJointForcedResponse_laplace q branch a w hw]
  unfold causalJointFrequencyResponse
  rw [causalCuspLaplace_original q branch a w ht]
  exact congrArg jointEmbedding (waveEnergyInverse_jointResponse w hw₀ _)

/-- The transformed causal response lies in the original unbounded operator domain and solves its full forced equation. -/
theorem causalJointForcedResponse_operator (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q+1 < w.re) :
    let U := ∫ t in Ioi (0 : ℝ), expRay w t • causalJointForcedResponse q branch a t
    ∃ hmem : U ∈ jointEnergyOperator.domain,
      jointEnergyOperator ⟨U,hmem⟩+(w^2-1) • U =
        ∫ t in Ioi (0 : ℝ), expRay w t • causalCuspSourceVector q branch a t := by
  have hw₀ : 0 < w.re := by have := causalResponseShift_pos q; linarith
  dsimp only
  rw [causalJointForcedResponse_laplace q branch a w hw]
  have he : causalJointFrequencyResponse q branch a w =
      jointEmbedding (jointWaveResponse w hw₀ (causalCuspLaplace q branch a w)) :=
    congrArg jointEmbedding (waveEnergyInverse_jointResponse w hw₀ _)
  rw [he]
  exact jointWaveResponse_operator w hw₀ (causalCuspLaplace q branch a w)

/-- A closed construction from the literal source: causal support, weighted L² admission,
absolute Laplace convergence, and the original operator-domain equation are all proved. -/
theorem causalCuspSource_original_joint_response (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∃ U : ℝ → SpatialSpace,
      (∀ᵐ t ∂(volume : Measure ℝ), t < 0 → U t = 0) ∧
      MemLp (fun t => expRay ((causalResponseShift q : ℂ)+1) t • U t) 2 volume ∧
      ∀ w : ℂ, causalResponseShift q+1 < w.re →
        IntegrableOn (fun t => expRay w t • U t) (Ioi (0 : ℝ)) ∧
        (∫ t in Ioi (0 : ℝ), expRay w t • U t) = causalJointFrequencyResponse q branch a w ∧
        ∃ hmem : (∫ t in Ioi (0 : ℝ), expRay w t • U t) ∈ jointEnergyOperator.domain,
          jointEnergyOperator ⟨∫ t in Ioi (0 : ℝ), expRay w t • U t,hmem⟩+
            (w^2-1) • (∫ t in Ioi (0 : ℝ), expRay w t • U t) =
              ∫ t in Ioi (0 : ℝ), expRay w t • causalCuspSourceVector q branch a t := by
  refine ⟨causalJointForcedResponse q branch a,causalJointForcedResponse_support q branch a,
    causalJointForcedResponse_weighted_memLp q branch a,?_⟩
  intro w hw
  exact ⟨causalJointForcedResponse_integrable q branch a w hw,
    causalJointForcedResponse_laplace q branch a w hw,
    causalJointForcedResponse_operator q branch a w hw⟩

end
end RHTower.D4BMJointSource
