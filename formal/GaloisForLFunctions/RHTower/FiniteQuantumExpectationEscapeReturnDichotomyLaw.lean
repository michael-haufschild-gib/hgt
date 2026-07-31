import GaloisForLFunctions.RHTower.FiniteQuantumExpectationGraphRateDistortionLaw

/-!
# Non-vacuous escape--return law for scalar quantum histories

A recurrence deadline is physically empty if the observed history never
first leaves the claimed return neighborhood.  This file removes that
loophole without an exit assumption.

At the graph rate--distortion radius, exactly one of two exhaustive outcomes
holds:

1. the complete finite family of expectation histories never leaves the
   radius at any nonnegative time; or
2. it leaves the radius, and a later sampled time returns within the same
   radius before the graph-rank deadline.

The second branch uses a freely chosen positive guard time.  Sampling at
multiples of `exitTime + guardTime` forces every certified return to occur
strictly after the supplied exit.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The guaranteed scalar-history distortion radius for one chosen graph
and resolution. -/
def finiteQuantumExpectationGraphDistortionBudget
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ)
    (Q : ℕ) : ℝ :=
  2 * finiteExpectationOmittedDirectedMass G lam coeff +
    2 * (2 * Real.pi / (Q + 1 : ℝ)) *
      finiteExpectationSelectedDirectedMass G lam coeff

/-- Scaling energies by a physical tick is exactly equivalent to evaluating
the original energy list at the correspondingly scaled time. -/
theorem finiteObserverHamiltonianVertexPhase_scaledEnergy
    {d : ℕ} (n : ℕ) (tick : ℝ) (energy : Fin d → ℝ) :
    finiteObserverHamiltonianVertexPhase (n : ℝ)
        (fun i => tick * energy i) =
      finiteObserverHamiltonianVertexPhase ((n : ℝ) * tick) energy := by
  funext i
  unfold finiteObserverHamiltonianVertexPhase
  congr 1
  push_cast
  ring

/--
Post-exit scalar-history recurrence.

Once an exit has been certified at `exitTime`, choosing any later positive
sampling tick forces the Dirichlet return to occur strictly after that exit.
The distortion radius and graph-rank exponent are unchanged.
-/
theorem exists_finiteQuantumExpectation_postExit_graph_rateDistortion
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ)
    (exitTime tick : ℝ)
    (hexitTime : 0 ≤ exitTime) (htick : exitTime < tick)
    (hexit :
      finiteQuantumExpectationGraphDistortionBudget
          G lam coeff Q <
        finiteQuantumExpectationTotalDeviation lam
          (finiteObserverHamiltonianVertexPhase exitTime energy) coeff) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card G.ConnectedComponent) ∧
      exitTime < (n : ℝ) * tick ∧
      (n : ℝ) * tick ≤
        (((Q + 1) ^
          (d - Nat.card G.ConnectedComponent) : ℕ) : ℝ) * tick ∧
      finiteQuantumExpectationGraphDistortionBudget
          G lam coeff Q <
        finiteQuantumExpectationTotalDeviation lam
          (finiteObserverHamiltonianVertexPhase exitTime energy) coeff ∧
      finiteQuantumExpectationTotalDeviation lam
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * tick) energy) coeff ≤
        finiteQuantumExpectationGraphDistortionBudget
          G lam coeff Q := by
  obtain ⟨n, hn0, hnQ, hreturn⟩ :=
    exists_finiteQuantumExpectation_graph_rateDistortion
      G lam coeff hlam (fun i => tick * energy i) Q
  have htick0 : 0 < tick := hexitTime.trans_lt htick
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn0)
  refine ⟨n, hn0, hnQ, ?_, ?_, hexit, ?_⟩
  · calc
      exitTime < tick := htick
      _ = (1 : ℝ) * tick := by ring
      _ ≤ (n : ℝ) * tick := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hn1) htick0.le
  · exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hnQ) htick0.le
  · rw [finiteQuantumExpectationGraphDistortionBudget]
    rw [finiteObserverHamiltonianVertexPhase_scaledEnergy] at hreturn
    exact hreturn

/--
**Universal scalar expectation escape--return dichotomy.**

For every finite scalar quantum history family, chosen graph, resolution,
and positive guard time, either the histories never leave the graph
rate--distortion neighborhood at any nonnegative time, or they leave it and
subsequently return to it.  In the return branch the event is strictly
post-exit in the same metric and obeys the graph-rank deadline.
-/
theorem finiteQuantumExpectation_neverExits_or_postExit_return
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteQuantumExpectationTotalDeviation lam
          (finiteObserverHamiltonianVertexPhase t energy) coeff ≤
        finiteQuantumExpectationGraphDistortionBudget
          G lam coeff Q) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card G.ConnectedComponent) ∧
      finiteQuantumExpectationGraphDistortionBudget
          G lam coeff Q <
        finiteQuantumExpectationTotalDeviation lam
          (finiteObserverHamiltonianVertexPhase exitTime energy) coeff ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^
          (d - Nat.card G.ConnectedComponent) : ℕ) : ℝ) *
            (exitTime + guardTime) ∧
      finiteQuantumExpectationTotalDeviation lam
          (finiteObserverHamiltonianVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) coeff ≤
        finiteQuantumExpectationGraphDistortionBudget
          G lam coeff Q := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        finiteQuantumExpectationTotalDeviation lam
            (finiteObserverHamiltonianVertexPhase t energy) coeff ≤
          finiteQuantumExpectationGraphDistortionBudget
            G lam coeff Q
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    have htick : exitTime < exitTime + guardTime := by linarith
    obtain ⟨n, hn0, hnQ, hpost, hdeadline, _hexit, hreturn⟩ :=
      exists_finiteQuantumExpectation_postExit_graph_rateDistortion
        G lam coeff hlam energy Q exitTime
        (exitTime + guardTime) hexitTime htick hexit
    exact
      ⟨exitTime, n, hexitTime, hn0, hnQ, hexit,
        hpost, hdeadline, hreturn⟩

end RHTower
