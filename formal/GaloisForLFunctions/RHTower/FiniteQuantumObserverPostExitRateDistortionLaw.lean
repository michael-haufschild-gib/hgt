import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphRateDistortionLaw

/-!
# Post-exit observer-graph rate--distortion law

A recurrence certificate can be physically vacuous if its guaranteed return
occurs before the system has left its initial observer neighborhood.  This
file closes that loophole for stroboscopic observations.

If departure is certified at a time strictly before one positive tick, then
every positive recurrence tick occurs strictly after departure.  Rescaling
the energies by the tick duration transfers the observer-graph
rate--distortion law to physical time without changing its graph-rank
deadline or distortion budget.
-/

noncomputable section

namespace RHTower

/-- Evolution for `n` physical ticks equals unit-tick evolution with every
energy scaled by the tick duration. -/
theorem finiteObserverHamiltonianVertexPhase_nat_mul_tick
    {d : ℕ} (n : ℕ) (tick : ℝ) (energy : Fin d → ℝ) :
    finiteObserverHamiltonianVertexPhase ((n : ℝ) * tick) energy =
      finiteObserverHamiltonianVertexPhase (n : ℝ)
        (fun i => tick * energy i) := by
  funext i
  unfold finiteObserverHamiltonianVertexPhase
  congr 1
  push_cast
  ring

/-- Scaled-energy and physical-time descriptions give the same squared
observer distance. -/
theorem finiteQuantumObserverDistanceSq_nat_mul_tick
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (n : ℕ) (tick : ℝ) (energy : Fin d → ℝ) :
    finiteQuantumObserverDistanceSq lam
        (finiteObserverHamiltonianVertexPhase
          ((n : ℝ) * tick) energy) block =
      finiteQuantumObserverDistanceSq lam
        (finiteObserverHamiltonianVertexPhase (n : ℝ)
          (fun i => tick * energy i)) block := by
  rw [finiteObserverHamiltonianVertexPhase_nat_mul_tick]

/-- The full coherence graph omits no positive off-diagonal observer
weight.  Hence its omitted directed mass vanishes exactly. -/
theorem finiteObserverOmittedDirectedWeightMass_coherenceGraph_eq_zero
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) :
    finiteObserverOmittedDirectedWeightMass
        (finiteObserverCoherenceGraph lam block) lam block = 0 := by
  classical
  rw [finiteObserverOmittedDirectedWeightMass]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  split_ifs with homit
  · have hle :
        finiteObserverUnionWeight lam block i j ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      exact homit.2 ⟨homit.1, Or.inl hpos⟩
    exact le_antisymm hle
      (finiteObserverUnionWeight_nonneg lam block hlam i j)
  · rfl

/--
**Deterministic post-exit observer-graph rate--distortion law.**

Suppose the system is certified outside an observer ball of squared radius
`exitRadius²` at a nonnegative time `exitTime` strictly before one positive
tick.  For every chosen synchronization graph there is a positive tick
number `n` such that:

* the physical recurrence time is strictly after the certified exit;
* it is no later than the tick-scaled graph-rank deadline;
* the exit certificate remains in the same observer metric; and
* the return distance obeys the selected/omitted directed-mass budget.
-/
theorem exists_finiteQuantumObserver_postExit_graph_rateDistortion
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ)
    (tick exitTime exitRadius : ℝ)
    (htick : 0 < tick)
    (hexitTimeNonneg : 0 ≤ exitTime)
    (hexitBeforeTick : exitTime < tick)
    (hexitCertificate :
      exitRadius ^ (2 : ℕ) ≤
        finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase exitTime energy) block) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card G.ConnectedComponent) ∧
      0 ≤ exitTime ∧
      exitTime < (n : ℝ) * tick ∧
      (n : ℝ) * tick ≤
        tick *
          (((Q + 1) ^
            (d - Nat.card G.ConnectedComponent) : ℕ) : ℝ) ∧
      exitRadius ^ (2 : ℕ) ≤
        finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase exitTime energy) block ∧
      finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * tick) energy) block ≤
        4 * finiteObserverOmittedDirectedWeightMass G lam block +
          4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) *
            finiteObserverSelectedDirectedWeightMass G lam block := by
  obtain ⟨n, hn0, hnQ, hdist⟩ :=
    exists_finiteQuantumObserver_graph_rateDistortion
      G lam block hlam (fun i => tick * energy i) Q
  refine ⟨n, hn0, hnQ, hexitTimeNonneg, ?_, ?_,
    hexitCertificate, ?_⟩
  · have hnOne : 1 ≤ n :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn0)
    have hnOneReal : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnOne
    have htickLe : tick ≤ (n : ℝ) * tick := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hnOneReal htick.le
    exact lt_of_lt_of_le hexitBeforeTick htickLe
  · have hnQReal :
        (n : ℝ) ≤
          (((Q + 1) ^
            (d - Nat.card G.ConnectedComponent) : ℕ) : ℝ) := by
      exact_mod_cast hnQ
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hnQReal htick.le
  · simpa only [finiteQuantumObserverDistanceSq_nat_mul_tick]
      using hdist

/-- Post-exit law for the full observer coherence graph.  Its omitted-mass
remainder is exactly zero. -/
theorem exists_finiteQuantumObserver_postExit_fullCoherence_rateDistortion
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ)
    (tick exitTime exitRadius : ℝ)
    (htick : 0 < tick)
    (hexitTimeNonneg : 0 ≤ exitTime)
    (hexitBeforeTick : exitTime < tick)
    (hexitCertificate :
      exitRadius ^ (2 : ℕ) ≤
        finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase exitTime energy) block) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card
          (finiteObserverCoherenceGraph lam block).ConnectedComponent) ∧
      0 ≤ exitTime ∧
      exitTime < (n : ℝ) * tick ∧
      (n : ℝ) * tick ≤
        tick *
          (((Q + 1) ^
            (d - Nat.card
              (finiteObserverCoherenceGraph
                lam block).ConnectedComponent) : ℕ) : ℝ) ∧
      exitRadius ^ (2 : ℕ) ≤
        finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase exitTime energy) block ∧
      finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * tick) energy) block ≤
        4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) *
          finiteObserverSelectedDirectedWeightMass
            (finiteObserverCoherenceGraph lam block) lam block := by
  obtain ⟨n, hn0, hnQ, hexit0, hnAfter, hnDeadline,
      hexit, hdist⟩ :=
    exists_finiteQuantumObserver_postExit_graph_rateDistortion
      (finiteObserverCoherenceGraph lam block)
      lam block hlam energy Q tick exitTime exitRadius
      htick hexitTimeNonneg hexitBeforeTick hexitCertificate
  refine ⟨n, hn0, hnQ, hexit0, hnAfter, hnDeadline, hexit, ?_⟩
  simpa [finiteObserverOmittedDirectedWeightMass_coherenceGraph_eq_zero
    lam block hlam] using hdist

/-- Post-exit specialization to the strong-edge threshold graph. -/
theorem exists_finiteQuantumObserver_postExit_thresholdGraph_rateDistortion
    {d : ℕ} {J : Type*} [Fintype J]
    (τ : ℝ) (lam : J → ℝ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ)
    (tick exitTime exitRadius : ℝ)
    (htick : 0 < tick)
    (hexitTimeNonneg : 0 ≤ exitTime)
    (hexitBeforeTick : exitTime < tick)
    (hexitCertificate :
      exitRadius ^ (2 : ℕ) ≤
        finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase exitTime energy) block) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card
          (finiteObserverThresholdCoherenceGraph
            τ lam block).ConnectedComponent) ∧
      0 ≤ exitTime ∧
      exitTime < (n : ℝ) * tick ∧
      (n : ℝ) * tick ≤
        tick *
          (((Q + 1) ^
            (d - Nat.card
              (finiteObserverThresholdCoherenceGraph
                τ lam block).ConnectedComponent) : ℕ) : ℝ) ∧
      exitRadius ^ (2 : ℕ) ≤
        finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase exitTime energy) block ∧
      finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * tick) energy) block ≤
        4 * finiteObserverOmittedDirectedWeightMass
            (finiteObserverThresholdCoherenceGraph τ lam block)
            lam block +
          4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) *
            finiteObserverSelectedDirectedWeightMass
              (finiteObserverThresholdCoherenceGraph τ lam block)
              lam block :=
  exists_finiteQuantumObserver_postExit_graph_rateDistortion
    (finiteObserverThresholdCoherenceGraph τ lam block)
    lam block hlam energy Q tick exitTime exitRadius
    htick hexitTimeNonneg hexitBeforeTick hexitCertificate

end RHTower
