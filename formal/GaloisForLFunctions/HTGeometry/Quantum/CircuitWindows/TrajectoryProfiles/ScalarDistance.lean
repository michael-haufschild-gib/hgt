import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhaseBoxes

/-! # Uniform distance between two translated physical trajectories -/
open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TrajectoryProfiles
open SharpOccupation (Register)
noncomputable section

private theorem forward_distance {N : ℕ} (H : selfAdjoint (Register N)) {w δ : ℝ}
    (h : HasProjectiveCircuitApproximation N δ 0 (unitaryEvolution H.val w)) (s : ℕ) (u : ℝ) :
    orbitCircuitDistance H s (u+w) ≤ orbitCircuitDistance H s u+δ := by
  have hu : HasProjectiveCircuitApproximation N (orbitCircuitDistance H s u) s (unitaryEvolution H.val u) :=
    (hasProjectiveCircuitApproximation_iff_infDist ..).mpr le_rfl
  have hh := affordable_add_time H hu h
  rw [Nat.add_zero] at hh
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp hh

/-- A zero-gate increment is an approximate period for every physical
circuit budget, uniformly in the time at which it is applied. -/
theorem scalar_shift_all_distances {N : ℕ} (H : selfAdjoint (Register N)) {w δ : ℝ}
    (h : HasProjectiveCircuitApproximation N δ 0 (unitaryEvolution H.val w)) (s : ℕ) (u : ℝ) :
    |orbitCircuitDistance H s (u+w)-orbitCircuitDistance H s u| ≤ δ := by
  have hp := forward_distance H h s u
  have hm := forward_distance H (h.neg_time H) s (u+w)
  rw [show u+w+ -w=u by ring] at hm
  exact abs_le.mpr ⟨by linarith only [hm],by linarith only [hp]⟩

/-- At time zero the empty circuit attains zero error. -/
private theorem empty_at_zero {N : ℕ} (H : selfAdjoint (Register N)) : orbitCircuitDistance H 0 0=0 := by
  rw [orbitCircuitDistance,unitaryEvolution,zero_smul,NormedSpace.exp_zero]
  apply Metric.infDist_zero_of_mem
  exact mem_phaseCircuitMatrixImageAtMost_iff.mpr
    ⟨1,norm_one,TwoQubitCircuit.one N,le_rfl,by rw [TwoQubitCircuit.one_eval,one_smul]; rfl⟩

/-- The zero budget at the identity attains the largest discrepancy over
all times and budgets. The entire shifted distance profile therefore
returns to accuracy δ exactly at the scalar returns to accuracy δ. -/
theorem profile_replay_iff_scalar {N : ℕ} (H : selfAdjoint (Register N)) (z v δ : ℝ) :
    (∀ t : ℝ, ∀ s : ℕ, |orbitCircuitDistance H s (z+t)-orbitCircuitDistance H s (v+t)| ≤ δ) ↔
      HasProjectiveCircuitApproximation N δ 0 (unitaryEvolution H.val (z-v)) := by
  constructor
  · intro h
    have hz := (abs_le.mp (h (-v) 0)).2
    rw [add_neg_cancel,empty_at_zero,sub_zero,←sub_eq_add_neg] at hz
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hz
  · intro h t s
    rw [show z+t=v+t+(z-v) by ring]
    exact scalar_shift_all_distances H h s (v+t)

#print axioms profile_replay_iff_scalar
end
end GaloisForLFunctions.HTGeometry.TrajectoryProfiles
