import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.PlateauConfidence.Entropy
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateCircuitBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.HaarScale

/-! # Time needed to see near-Hilbert complexity with exponentially small failure -/
open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.PlateauConfidence
noncomputable section

private theorem empty_subset (n s : ℕ) (t : ℝ) :
    {x | pathGateDistance n 0 x t ≤ 1/10} ⊆ {x | pathGateDistance n s x t ≤ 1/10} := by
  intro x hx
  let U := unitaryEvolution (numberedGenerator n x) t
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist U 0 (1/10)).mpr hx
  exact (hasProjectiveCircuitApproximation_iff_infDist U s (1/10)).mp
    ⟨z,hz,C,hC.trans (Nat.zero_le s),he⟩

/-- A near-Hilbert gate budget has two doubly exponential confidence
deadlines. Reaching failure probability (9/10)^D at any prescribed
laboratory date requires log time of order at least D. Every date past
2^(D^c) attains that confidence, also at delays from the first crossing. -/
theorem gaussian_near_hilbert_confidence_window :
    ∃ c : ℕ, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let N := k+3
      let D : ℕ := 2^N
      let P := nearHilbertContinuousCircuitBudget N
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n P (9/80)
      let p (t : ℝ) := μ.real {x | pathGateDistance n P x t≤1/10}
      let q (t : ℝ) := μ.real {x | pathGateDistance n P x (σ x+t)≤1/10}
      (∀ t : ℝ, p t≤(9/10:ℝ)^D → -log (9/10)/18*(D:ℝ)≤log (1+|t|)) ∧
      ∀ t : ℝ, (2:ℝ)^(D^c)≤t → p t≤(9/10:ℝ)^D ∧ q t≤(9/10:ℝ)^D := by
  obtain ⟨c,hc⟩ := gaussian_late_circuit_bound
  refine ⟨c,?_⟩
  have hlow := (tendsto_add_atTop_nat 1).eventually
    (gaussian_scalar_probability_deadline (by norm_num : (0:ℝ)<9/10) (by norm_num))
  filter_upwards [hlow,eventually_ge_atTop 64] with k hl hk
  intro n N D P μ σ p q
  have hm : Fintype.card (PrefixIndex n)≤12*N := by
    rw [Fintype.card_congr (pathCoeffEquiv n)]
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    dsimp only [n,N]; omega
  constructor
  · intro t ht
    have hp : prescribedScalarProbability n t≤p t := measureReal_mono (μ:=μ) (empty_subset n P t)
    have hh := hl t (hp.trans ht)
    simpa only [D,N,Nat.cast_pow,Nat.cast_ofNat] using hh
  · intro t ht
    have hh := hc k P P t ht
    have hc' := complete_budget_price (N:=N) (by dsimp only [N]; omega) hm
    exact ⟨hh.1.trans hc',hh.2.trans hc'⟩

#print axioms gaussian_near_hilbert_confidence_window
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.PlateauConfidence
