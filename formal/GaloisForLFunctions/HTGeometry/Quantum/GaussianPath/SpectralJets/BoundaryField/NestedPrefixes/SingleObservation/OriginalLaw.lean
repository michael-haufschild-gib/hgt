import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation.FieldLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Single readings of the original larger register at dates chosen by the other fields -/

open Set Filter Topology MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
open PrefixCouplings
noncomputable section

/-- Ordered relative phases of the actual draw at time t. -/
def originalPhase (k : ℕ) (r : Config k) (ω : PathPauliDisorder) (t : ℝ) :=
  finiteClockPhasePoint (projectiveFrequency (fun i => -orderedBoundaryEnergy ω k 0 i) r) t

theorem measurable_phase_at (k : ℕ) (r : Config k) {t : PathPauliDisorder → ℝ} (ht : Measurable t) :
    Measurable (fun ω => originalPhase k r ω (t ω)) := by
  apply measurable_pi_lambda
  intro i
  exact (AddCircle.continuous_mk' (1:ℝ)).measurable.comp
    ((ht.mul ((continuous_frozen_energy k i.val).neg.sub (continuous_frozen_energy k r).neg).measurable).div_const _)

/-- A single observation, at any diverging sequence of dates measurable
from all but the last longitudinal field, recovers Haar probabilities of
continuity sets over the original disorder law. -/
theorem original_snapshot_probability (k : ℕ) (r : Config k)
    (t : ℕ → PathPauliDisorder → ℝ) (ht : ∀ n, Measurable (t n))
    (hdiv : ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto (fun n => t n (eraseTerminal k ω)) atTop atTop)
    (A : Set (UnitAddTorus {i : Config k // i≠r})) (hA : MeasurableSet A)
    (hb : volume (frontier A)=0) :
    Tendsto (fun n => pathPauliDisorderLaw {ω | originalPhase k r ω (t n (eraseTerminal k ω))∈A})
      atTop (𝓝 (volume A)) := by
  classical
  let μ := gaussianReal 0 1
  let G : ProbabilityMeasure ℝ := ⟨μ,inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))⟩
  let P := pathPauliDisorderLaw
  let i := terminalCoordinate k
  let R (p : PathPauliDisorder × ℝ) := Function.update p.1 i p.2
  have hR : MeasurePreserving R (P.prod μ) P := resample_preserving μ i
  let B (n : ℕ) := {ω | originalPhase k r ω (t n (eraseTerminal k ω))∈A}
  have hm (n : ℕ) : MeasurableSet (B n) :=
    hA.preimage (measurable_phase_at k r ((ht n).comp (continuous_eraseTerminal k).measurable))
  let F (n : ℕ) (ω : PathPauliDisorder) := μ (Prod.mk ω ⁻¹' (R ⁻¹' B n))
  have hF (n : ℕ) : Measurable (F n) := measurable_measure_prodMk_left ((hm n).preimage hR.measurable)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (volume A)) := by
    filter_upwards [gaussian_field_snapshot,hdiv] with ω hω hT
    have hG : (G : Measure ℝ) ≪ volume := gaussianReal_absolutelyContinuous 0 one_ne_zero
    have h := (hω k r G hG).comp hT
    have hb' : (finiteTorusHaarProbabilityMeasure _ : Measure _) (frontier A)=0 := by
      rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
    have ha := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hb'
    rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at ha
    apply ha.congr
    intro n
    change (snapshot ω k r G (t n (eraseTerminal k ω)) : Measure _) A=_
    rw [snapshot,ProbabilityMeasure.toMeasure_map,Measure.map_apply_of_aemeasurable _ hA]
    congr 1
    ext y
    have he := ordered_congr (boundary_update ω k y 0)
    simp only [add_zero] at he
    change _ ↔ originalPhase k r (Function.update ω i y)
      (t n (Function.update (Function.update ω i y) i 0))∈A
    simp only [Function.update_idem,originalPhase,he,fieldEnergy,eraseTerminal,i,mem_preimage]
  haveI : IsProbabilityMeasure P := by dsimp [P,pathPauliDisorderLaw]; infer_instance
  have h := tendsto_lintegral_of_dominated_convergence (μ:=P) (fun _ => 1) hF
    (fun n => .of_forall fun ω => (show μ _ ≤ 1 from prob_le_one)) (by simp) hlim
  simp only [lintegral_const,measure_univ,mul_one] at h
  apply h.congr
  intro n
  rw [←Measure.prod_apply ((hm n).preimage hR.measurable),hR.measure_preimage (hm n).nullMeasurableSet]

#print axioms original_snapshot_probability
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
