import GaloisForLFunctions.RHTower.StaticChoiPhaseDensity
import GaloisForLFunctions.RHTower.StaticChoiPhaseTargetEntropy

/-!
# Static Choi complexity plateau

This capstone combines exact equal-weight Choi geometry with the universal
phase-coherence entropy bound.  It controls any finite dictionary of
Hilbert--Schmidt target balls, independently of the Hamiltonian eigenbasis.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

theorem continuous_uniformPhaseDensity (d : ℕ) :
    Continuous (uniformPhaseDensity d) := by
  unfold uniformPhaseDensity
  fun_prop

/-- Every Hilbert--Schmidt ball in the Choi phase image is controlled by a
translated coherence cap with defect `2 * δ²`. -/
theorem uniformPhaseDensity_metricBallTarget_controlled
    {d : ℕ} (hd : 0 < d) {δ : ℝ} (hδ : 0 ≤ δ)
    (c : EuclideanSpace ℂ (Fin d × Fin d)) :
    TorusTargetControlled
      (torusMetricBallTarget (uniformPhaseDensity d) c δ)
      (2 * δ ^ 2) := by
  apply torusMetricBallTarget_controlled
  intro x y hxy
  exact uniformPhaseDensity_pair_mem_torusCoherenceTarget hd hδ x y hxy

/-- Eigenbasis-free entropy bound for a finite dictionary of target balls in
the equal-weight Choi phase torus. -/
theorem measureReal_iUnion_uniformPhaseDensity_metricBallTarget_le
    {d κ : ℕ} (hd : 0 < d)
    (target : Fin κ → EuclideanSpace ℂ (Fin d × Fin d))
    {δ : ℝ} (hδ : 0 < δ) :
    volume.real
        (⋃ k, torusMetricBallTarget
          (uniformPhaseDensity d) (target k) δ) ≤
      (κ : ℝ) *
        ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
          Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ (d - 1)) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  simpa only [Fintype.card_fin] using
    (measureReal_iUnion_torusTargetControlled_le
      (fun k : Fin κ ↦ torusMetricBallTarget
        (uniformPhaseDensity d) (target k) δ)
      (by positivity : 0 < 2 * δ ^ 2)
      (fun k ↦ uniformPhaseDensity_metricBallTarget_controlled
        hd hδ.le (target k)))

/-- Padded circuit words give the exact dictionary multiplier
`|gate|^(s+1)`. -/
theorem measureReal_iUnion_uniformPhaseDensity_paddedCircuitTargets_le
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    {δ : ℝ} (hδ : 0 < δ) :
    volume.real
        (⋃ w, torusMetricBallTarget
          (uniformPhaseDensity d) (target w) δ) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
          Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ (d - 1)) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  simpa only [Fintype.card_fin] using
    (measureReal_iUnion_paddedCircuitTargets_le s
      (fun w ↦ torusMetricBallTarget
        (uniformPhaseDensity d) (target w) δ)
      (by positivity : 0 < 2 * δ ^ 2)
      (fun w ↦ uniformPhaseDensity_metricBallTarget_controlled
        hd hδ.le (target w)))

end RHTower
