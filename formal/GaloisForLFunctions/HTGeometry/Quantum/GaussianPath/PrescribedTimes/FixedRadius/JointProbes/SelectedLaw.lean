import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FixedRadius.JointProbes.Characters
import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification
import Mathlib.Probability.ConditionalProbability

/-! # Product Haar phases after any fixed angular selection -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.FixedRadius
noncomputable section

private theorem coeff_count_pos (k : ℕ) : 0 < Fintype.card (ChainLabel (k+3)) :=
  lt_of_le_of_lt (Nat.zero_le _) ((pathCoeffEquiv (k+1)).symm (Sum.inl (0,0))).isLt

/-- Uniform coupling direction conditioned to a set of positive area. -/
def selectedDirections {k : ℕ} (B : Set (chainSphere k))
    (hB : sphereLaw (Fintype.card (ChainLabel (k+3))) B ≠ 0) : ProbabilityMeasure (chainSphere k) :=
  letI := isProbabilityMeasure_sphereLaw (coeff_count_pos k)
  ⟨_,cond_isProbabilityMeasure hB⟩

variable {I : Type} [Fintype I] {k : ℕ} {i₀ : Fin (2^(k+3))}

/-- All prescribed probe coordinates become independent uniform phases,
even when selected directions and phase origins depend measurably on the chain. -/
theorem selected_probe_law (λ' : I → ℝ) (hλ : RationallyIndependentFrequency λ')
    {offset : chainSphere k → UnitAddTorus (I × phaseIndex i₀)} (ho : Measurable offset)
    (B : Set (chainSphere k)) (hm : MeasurableSet B)
    (hB : sphereLaw (Fintype.card (ChainLabel (k+3))) B ≠ 0) :
    Tendsto (fun t : ℝ => (selectedDirections B hB).map
      (f:=probePoint λ' offset t) (measurable_probePoint λ' ho t).aemeasurable)
      atTop (𝓝 (finiteTorusHaarProbabilityMeasure (I × phaseIndex i₀))) := by
  classical
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro m
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hz : m=0
  · subst m
    simp
  rw [if_neg hz]
  let μ := sphereLaw (Fintype.card (ChainLabel (k+3)))
  let g := B.indicator (fun _ => (1:ℂ))
  have hbound (θ) : ‖g θ‖≤1 := by
    by_cases hh : θ∈B <;> simp [g,hh]
  have h := selected_joint_character λ' hλ ho (measurable_const.indicator hm) 1 zero_le_one hbound m hz
  have hs := h.const_smul (μ B)⁻¹.toReal
  rw [smul_zero] at hs
  refine hs.congr fun t => ?_
  rw [ProbabilityMeasure.toMeasure_map,integral_map (measurable_probePoint λ' ho t).aemeasurable
    (UnitAddTorus.mFourier m).continuous.aestronglyMeasurable]
  change _=∫ θ, UnitAddTorus.mFourier m (probePoint λ' offset t θ) ∂(cond μ B)
  rw [cond,integral_smul_measure,←integral_indicator hm]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun θ => ?_)
  by_cases hh : θ∈B <;> simp [g,hh]

#print axioms selected_probe_law
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.FixedRadius
