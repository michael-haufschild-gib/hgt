import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleFourierDecay
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
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro m
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases h₀ : m=0
  · subst m
    simp
  rw [if_neg h₀]
  let c := liftPacket r m
  have hc : c≠0 := by
    intro h
    apply h₀
    funext j
    simpa only [c,lift_off_anchor,Pi.zero_apply] using congrFun h j.val
  let A (y : ℝ) := ∑ i, (c i:ℝ)*fieldEnergy ω k y i
  have hA : Continuous A := continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_fieldEnergy ω k i)
  let ν := (μ : Measure ℝ).map A
  have hac : ν ≪ volume := by
    apply Measure.AbsolutelyContinuous.mk
    intro S hS hz
    rw [Measure.map_apply hA.measurable hS]
    apply measure_eq_zero_iff_ae_notMem.mpr
    have hh := (measurePreserving_add_right (volume : Measure ℝ) (-ω (PrefixCouplings.terminalCoordinate k))).quasiMeasurePreserving
    filter_upwards [hμ.ae_le (hh.ae (hω k S hz))] with y hy
    simpa only [A,fieldEnergy,sub_eq_add_neg,mem_preimage,c] using hy c hc (lift_sum r m)
  have hf := (spectralDensityFourierAmplitude_tendsto_zero_cocompact (spectralMeasureDensity ν)).mono_left
    (atTop_le_cocompact : (atTop : Filter ℝ)≤cocompact ℝ)
  apply hf.congr
  intro T
  rw [spectralDensityFourierAmplitude_spectralMeasureDensity ν hac,snapshot,ProbabilityMeasure.toMeasure_map,
    integral_map _ (UnitAddTorus.mFourier m).continuous.aestronglyMeasurable]
  rw [show ν=(μ : Measure ℝ).map A from rfl,integral_map hA.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with y
  rw [mFourier_finiteClockPhasePoint]
  have hdet : finiteTorusCharacterDetuning m (projectiveFrequency (fun i => -fieldEnergy ω k y i) r) = -A y := by
    rw [←lift_energy]
    simp only [A,c,mul_neg,Finset.sum_neg_distrib]
  rw [hdet,mul_neg,Complex.ofReal_neg]

#print axioms gaussian_field_snapshot
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
