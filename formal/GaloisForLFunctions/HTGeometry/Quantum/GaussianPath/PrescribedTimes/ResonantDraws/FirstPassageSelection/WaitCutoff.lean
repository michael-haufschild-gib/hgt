import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.Posterior
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.Survival

/-! # First-wait tails excluded by an empty observation -/
open Set Filter MeasureTheory ProbabilityTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
noncomputable section

private theorem wait_le_delay {n j s : ℕ} {x : PrefixIndex n → ℝ} {t : ℝ} (ht : 0≤t)
    (h : pathGateDistance n 0 x (crossingOrigin n j (9/80) x+t)≤1/10) :
    crossingWait n j s x≤t := by
  have hh := (crossingWait_le_iff n j 0 x t).mpr
    ⟨_,⟨le_add_of_nonneg_right ht,le_rfl⟩,h⟩
  exact (crossingWait_antitone (Nat.zero_le s) x).trans hh

/-- The posterior recovers each fixed first-wait tail. At the moving
deadline equal to the observation delay, its tail vanishes exactly.
One weak bond gives this missing prior tail mass at least c/t⁹. -/
theorem gaussian_empty_observation_wait_cutoff :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n P (9/80)
      let E (t : ℝ) := {x | pathGateDistance n 0 x (σ x+t)≤1/10}
      ∃ c > (0:ℝ), ∀ s≤P/2,
        let tail (v : ℝ) := {x | v<crossingWait n P s x}
        (∀ v, Tendsto (fun t => μ.real (tail v ∩ E t)/μ.real (E t)) atTop (𝓝 (μ.real (tail v)))) ∧
        ∀ t≥(1:ℝ), μ.real (tail t ∩ E t)=0 ∧ c≤t^9*μ.real (tail t) := by
  filter_upwards [WeakBonds.SingleCut.gaussian_one_bond_survival] with k hk
  intro n P μ σ E
  obtain ⟨c,hc,hfloor⟩ := hk
  refine ⟨c,hc,fun s hs => ?_⟩
  intro tail
  constructor
  · intro v
    have he : (1/10:ℝ)<sqrt 2 := by
      have h := sq_sqrt (by norm_num : (0:ℝ)≤2)
      nlinarith only [h,sqrt_nonneg 2]
    exact gaussian_late_empty_posterior k P (by norm_num : (0:ℝ)<1/10) he _
      (measurableSet_lt measurable_const (measurable_crossingWait n P s))
  · intro t ht
    have hzero : tail t ∩ E t=∅ := eq_empty_iff_forall_notMem.mpr fun x hx =>
      hx.1.not_ge (wait_le_delay (s:=s) (zero_le_one.trans ht) hx.2)
    refine ⟨by rw [hzero,measureReal_empty],(hfloor t ht).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans ht) _)
    exact measureReal_mono fun x hx => hx.2.2 s hs

#print axioms gaussian_empty_observation_wait_cutoff
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
