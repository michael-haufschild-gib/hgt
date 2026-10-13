import GaloisForLFunctions.HTGeometry.LpDominatedConvergence
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Compact dominated history hulls with proper normed fibers

Each depth may carry an entire normed channel space. A fixed square-summable
energy envelope controls its full fiber balls, including all channel mixing.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology
variable {I : Type*} {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]

def lpFiberSolidHull (x : lp E 2) : Set (lp E 2) := {y | ∀ i, ‖y i‖ ≤ ‖x i‖}

abbrev LpFiberBall (x : lp E 2) := ∀ i, Metric.closedBall (0 : E i) ‖x i‖

theorem lpFiberBall_norm_le (x : lp E 2) (u : LpFiberBall x) (i : I) :
    ‖(u i : E i)‖ ≤ ‖x i‖ := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using (u i).property

def lpFiberBallHistory (x : lp E 2) (u : LpFiberBall x) : lp E 2 :=
  ⟨fun i => (u i : E i), (lp.memℓp x).mono' (lpFiberBall_norm_le x u)⟩

@[simp] theorem lpFiberBallHistory_apply (x : lp E 2) (u : LpFiberBall x) (i : I) :
    lpFiberBallHistory x u i = (u i : E i) := rfl

theorem lpFiberBallHistory_mem (x : lp E 2) (u : LpFiberBall x) :
    lpFiberBallHistory x u ∈ lpFiberSolidHull x := lpFiberBall_norm_le x u

theorem lpFiberSolidHull_norm_le {x y : lp E 2} (hy : y ∈ lpFiberSolidHull x) :
    ‖y‖ ≤ ‖x‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) hy

theorem zero_mem_lpFiberSolidHull (x : lp E 2) : (0 : lp E 2) ∈ lpFiberSolidHull x := by
  intro i
  simp only [lp.coeFn_zero, Pi.zero_apply, norm_zero, norm_nonneg]

theorem lpFiberBallHistory_continuous (x : lp E 2) : Continuous (lpFiberBallHistory x) := by
  rw [continuous_iff_continuousAt]
  intro u
  apply tendsto_lpTwo_of_dominated _ _ x
    (fun a => lpFiberBallHistory_mem x a) (lpFiberBallHistory_mem x u)
  intro i
  exact (continuous_subtype_val.comp (continuous_apply i)).tendsto u

theorem range_lpFiberBallHistory (x : lp E 2) :
    Set.range (lpFiberBallHistory x) = lpFiberSolidHull x := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact lpFiberBallHistory_mem x u
  · intro hy
    refine ⟨fun i => ⟨y i, ?_⟩, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy i

/-- Proper fibers pay compactness of the actual full history hull. -/
theorem isCompact_lpFiberSolidHull [∀ i, ProperSpace (E i)] (x : lp E 2) :
    IsCompact (lpFiberSolidHull x) := by
  rw [← range_lpFiberBallHistory]
  exact isCompact_range (lpFiberBallHistory_continuous x)

theorem isClosed_lpFiberSolidHull [∀ i, ProperSpace (E i)] (x : lp E 2) :
    IsClosed (lpFiberSolidHull x) := (isCompact_lpFiberSolidHull x).isClosed

end
end GaloisForLFunctions.HTGeometry
