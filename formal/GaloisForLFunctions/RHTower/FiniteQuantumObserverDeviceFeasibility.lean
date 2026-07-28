import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphRecurrenceBound

/-!
# Device-window certificate for observer recurrence

The graph-rank deadline becomes a device-feasibility statement once a
stroboscopic tick duration and a coherent observation window are supplied.
If the certified worst-case horizon fits inside that window, the guaranteed
observer recurrence occurs before coherence is lost.

This is an exact analytic certificate. Whether a particular device satisfies
its hypothesis depends on measured hardware parameters.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Graph-rank recurrence with the corresponding physical time certified
inside a supplied coherent observation window. -/
theorem exists_finiteQuantumObserver_graphRank_recurrence_within_window
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ)
    (tickTime coherentWindow : ℝ) (htick : 0 ≤ tickTime)
    (hwindow :
      (((Q + 1) ^
        (d - Nat.card
          (finiteObserverCoherenceGraph lam block).ConnectedComponent) : ℕ) :
          ℝ) * tickTime ≤ coherentWindow) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card
          (finiteObserverCoherenceGraph lam block).ConnectedComponent) ∧
      (n : ℝ) * tickTime ≤ coherentWindow ∧
      finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) block ≤
        4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
          ∑ i, ∑ j, finiteObserverUnionWeight lam block i j := by
  obtain ⟨n, hn0, hnQ, hdist⟩ :=
    exists_finiteQuantumObserver_graphRank_distance_recurrence
      lam block hlam energy Q
  refine ⟨n, hn0, hnQ, ?_, hdist⟩
  apply le_trans ?_ hwindow
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnQ) htick

end RHTower
