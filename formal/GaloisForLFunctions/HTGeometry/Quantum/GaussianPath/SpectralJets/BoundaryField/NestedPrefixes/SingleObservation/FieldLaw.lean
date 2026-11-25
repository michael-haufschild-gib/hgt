import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.PhaseLaws.FrequencyDistribution
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ConditionalLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.JointHaar

/-! # One late observation with only one unrevealed field -/

open Filter MeasureTheory Topology Set ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
noncomputable section

/-- Conditional energies after replacing the last field by y. -/
def fieldEnergy (ω : PathPauliDisorder) (k : ℕ) (y : ℝ) :=
  orderedBoundaryEnergy ω k (y-ω (PrefixCouplings.terminalCoordinate k))

theorem continuous_fieldEnergy (ω : PathPauliDisorder) (k : ℕ) (i : Config k) :
    Continuous (fun y => fieldEnergy ω k y i) :=
  (continuous_orderedBoundaryEnergy ω k i).comp (continuous_id.sub continuous_const)

/-- Relative phases at one specified date under a replacement law for the last field. -/
def snapshot (ω : PathPauliDisorder) (k : ℕ) (r : Config k) (μ : ProbabilityMeasure ℝ) (T : ℝ) :
    ProbabilityMeasure (UnitAddTorus {i : Config k // i≠r}) :=
  let f := fun y => projectiveFrequency (fun i => -fieldEnergy ω k y i) r
  have hc : Continuous (fun y => finiteClockPhasePoint (f y) T) :=
    continuous_pi fun i => (AddCircle.continuous_mk' (1:ℝ)).comp
      ((continuous_const.mul ((continuous_fieldEnergy ω k i.val).neg.sub
        (continuous_fieldEnergy ω k r).neg)).div_const _)
  μ.map hc.aemeasurable

/-- Every nonconstant phase character has an absolutely continuous conditional
action law. Its Fourier transform at a single late date therefore vanishes. -/
theorem gaussian_field_snapshot :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (k : ℕ) (r : Config k) (μ : ProbabilityMeasure ℝ),
      (μ : Measure ℝ) ≪ volume →
      Tendsto (snapshot ω k r μ) atTop (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  classical
  filter_upwards [gaussian_ordered_null_frequencies] with ω hω k r μ hμ
  let f (y : ℝ) := projectiveFrequency (fun i => -fieldEnergy ω k y i) r
  have hf : Measurable f := measurable_pi_lambda _ fun i =>
    ((continuous_fieldEnergy ω k i.val).neg.sub (continuous_fieldEnergy ω k r).neg).measurable
  apply PrescribedTimes.PhaseLaws.frequencySnapshot_haar μ f hf
  intro m h₀
  let c := liftPacket r m
  have hc : c≠0 := by
    intro h
    apply h₀
    funext j
    simpa only [c,lift_off_anchor,Pi.zero_apply] using congrFun h j.val
  let A (y : ℝ) := ∑ i, (c i:ℝ)*fieldEnergy ω k y i
  have hA : Continuous A := continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_fieldEnergy ω k i)
  have heq : (fun y => -finiteTorusCharacterDetuning m (f y))=A := by
    funext y
    rw [show f y=projectiveFrequency (fun i => -fieldEnergy ω k y i) r from rfl,←lift_energy]
    simp only [A,c,mul_neg,Finset.sum_neg_distrib,neg_neg]
  rw [heq]
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hz
  rw [Measure.map_apply hA.measurable hS]
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hh := (measurePreserving_add_right (volume : Measure ℝ) (-ω (PrefixCouplings.terminalCoordinate k))).quasiMeasurePreserving
  filter_upwards [hμ.ae_le (hh.ae (hω k S hz))] with y hy
  simpa only [A,fieldEnergy,sub_eq_add_neg,mem_preimage,c] using hy c hc (lift_sum r m)

#print axioms gaussian_field_snapshot
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
