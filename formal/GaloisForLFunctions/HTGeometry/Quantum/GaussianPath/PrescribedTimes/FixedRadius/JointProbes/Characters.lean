import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FixedRadius.JointProbes.Weights
import GaloisForLFunctions.HTGeometry.PauliChainDephasing
import GaloisForLFunctions.HTGeometry.ActivePhaseLattice
import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw

/-! # Simultaneous phase readings on one sphere of frozen Pauli chains -/
open Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.FixedRadius
noncomputable section

abbrev chainSphere (k : ℕ) := coeffSphere (Fintype.card (ChainLabel (k+3)))

variable {I : Type} [Fintype I] {k : ℕ} {i₀ : Fin (2^(k+3))}

/-- Relative phases at a common date with independent prescribed slopes.
The additive offset can depend on the entire coupling direction. -/
def probePoint (λ' : I → ℝ) (offset : chainSphere k → UnitAddTorus (I × phaseIndex i₀))
    (t : ℝ) (θ : chainSphere k) : UnitAddTorus (I × phaseIndex i₀) :=
  offset θ + finiteClockPhasePoint (fun p => λ' p.1 *
    projectivePhase (chainPauliFin_isHermitian (k+3)) i₀ (sphereCoeff θ) p.2) (-t)

theorem measurable_probePoint (λ' : I → ℝ) {offset : chainSphere k → UnitAddTorus (I × phaseIndex i₀)}
    (ho : Measurable offset) (t : ℝ) : Measurable (probePoint λ' offset t) := by
  apply ho.add
  apply measurable_pi_lambda
  intro p
  apply (AddCircle.continuous_mk' 1).measurable.comp
  have hphase := ((continuous_projectivePhase (chainPauliFin_isHermitian (k+3)) i₀ p.2).comp
    continuous_sphereCoeff).measurable
  exact ((measurable_const.mul (measurable_const.mul hphase)).div_const _)

/-- A bounded measurable angular selection and a direction-dependent phase
origin both survive in the amplitude of a single dephasing integral. -/
theorem selected_joint_character (λ' : I → ℝ) (hλ : RationallyIndependentFrequency λ')
    {offset : chainSphere k → UnitAddTorus (I × phaseIndex i₀)} (ho : Measurable offset)
    {g : chainSphere k → ℂ} (hg : Measurable g) (C : ℝ) (hC : 0≤C) (hbound : ∀ θ, ‖g θ‖≤C)
    (m : I × phaseIndex i₀ → ℤ) (hm : m≠0) :
    Tendsto (fun t : ℝ => ∫ θ, g θ * UnitAddTorus.mFourier m (probePoint λ' offset t θ)
      ∂(sphereLaw (Fintype.card (ChainLabel (k+3))))) atTop (𝓝 0) := by
  let f (θ : chainSphere k) := g θ * UnitAddTorus.mFourier m (offset θ)
  have hf : Measurable f := hg.mul ((UnitAddTorus.mFourier m).continuous.measurable.comp ho)
  have hf' (θ) : ‖f θ‖≤C := by
    simpa only [f,norm_mul,show ‖UnitAddTorus.mFourier m (offset θ)‖=1 by simp [UnitAddTorus.mFourier],
      mul_one] using hbound θ
  let w := probeWeight i₀ λ' m
  have hosc := tendsto_integral_exp_sortedSpectralAction_zero_pauliChain k w
    (probeWeight_balanced i₀ λ' m) (probeWeight_ne_zero i₀ hλ hm) f hf hC hf'
  let c := ((volume : Measure (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k+3)))))).toSphere univ)⁻¹
  have hlim := (hosc.mono_left atTop_le_cocompact).const_smul c.toReal
  rw [smul_zero] at hlim
  refine hlim.congr fun t => ?_
  rw [sphereLaw,integral_smul_measure]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun θ => ?_)
  rw [probePoint,mFourier_add_point,mFourier_finiteClockPhasePoint,probe_detuning]
  simp only [f,w,sphereCoeff,neg_mul,Complex.ofReal_neg,mul_assoc]

#print axioms selected_joint_character
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.FixedRadius
