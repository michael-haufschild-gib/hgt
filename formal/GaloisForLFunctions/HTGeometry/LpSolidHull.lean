import GaloisForLFunctions.HTGeometry.LpDominatedConvergence
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Compact solid hulls of square-summable histories

All coordinate contractions of one fixed history form exactly its compact
coordinatewise solid hull. The mask space carries the product topology.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

abbrev LpCoordinateMask (I : Type*) := I → Metric.closedBall (0 : ℂ) 1

def lpSolidHull {I : Type*} (x : lp (fun _ : I => ℂ) 2) : Set (lp (fun _ : I => ℂ) 2) :=
  {y | ∀ i, ‖y i‖ ≤ ‖x i‖}

theorem lpCoordinateMask_norm_le {I : Type*} (m : LpCoordinateMask I) (i : I) :
    ‖(m i : ℂ)‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using (m i).property

def lpMaskedHistory {I : Type*} (x : lp (fun _ : I => ℂ) 2) (m : LpCoordinateMask I) :
    lp (fun _ : I => ℂ) 2 :=
  lpDiagonalCLM (fun i => (m i : ℂ)) zero_le_one (lpCoordinateMask_norm_le m) x

@[simp] theorem lpMaskedHistory_apply {I : Type*} (x : lp (fun _ : I => ℂ) 2)
    (m : LpCoordinateMask I) (i : I) : lpMaskedHistory x m i = (m i : ℂ) * x i := rfl

theorem lpMaskedHistory_mem_solidHull {I : Type*} (x : lp (fun _ : I => ℂ) 2)
    (m : LpCoordinateMask I) : lpMaskedHistory x m ∈ lpSolidHull x := by
  intro i
  rw [lpMaskedHistory_apply, norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (lpCoordinateMask_norm_le m i) (norm_nonneg _)

theorem lpSolidHull_norm_le {I : Type*} {x y : lp (fun _ : I => ℂ) 2}
    (hy : y ∈ lpSolidHull x) : ‖y‖ ≤ ‖x‖ :=
  lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) hy

theorem lpMaskedHistory_continuous {I : Type*} (x : lp (fun _ : I => ℂ) 2) :
    Continuous (lpMaskedHistory x) := by
  rw [continuous_iff_continuousAt]
  intro m
  apply tendsto_lpTwo_of_dominated (lpMaskedHistory x) (lpMaskedHistory x m) x
    (fun a => lpMaskedHistory_mem_solidHull x a) (lpMaskedHistory_mem_solidHull x m)
  intro i
  exact ((continuous_subtype_val.comp (continuous_apply i)).mul continuous_const).tendsto m

/-- Every coordinatewise dominated history is an actual coordinate mask of the original one. -/
theorem range_lpMaskedHistory {I : Type*} (x : lp (fun _ : I => ℂ) 2) :
    Set.range (lpMaskedHistory x) = lpSolidHull x := by
  classical
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    exact lpMaskedHistory_mem_solidHull x m
  · intro hy
    let m : LpCoordinateMask I := fun i =>
      ⟨if x i = 0 then 0 else y i / x i, by
        rw [Metric.mem_closedBall, dist_zero_right]
        split_ifs with hi
        · simp only [norm_zero, zero_le_one]
        · rw [norm_div]
          exact (div_le_one (norm_pos_iff.mpr hi)).mpr (hy i)⟩
    refine ⟨m, lp.ext (funext fun i => ?_)⟩
    change (if x i = 0 then 0 else y i / x i) * x i = y i
    by_cases hi : x i = 0
    · have hyi : y i = 0 := norm_le_zero_iff.mp (by simpa only [hi, norm_zero] using hy i)
      simp only [hi, hyi, if_pos, mul_zero]
    · simp only [hi, if_false, div_mul_cancel₀ _ hi]

/-- Compactness is proved for the literal hull, with no compactness premise. -/
theorem isCompact_lpSolidHull {I : Type*} (x : lp (fun _ : I => ℂ) 2) :
    IsCompact (lpSolidHull x) := by
  rw [← range_lpMaskedHistory]
  exact isCompact_range (lpMaskedHistory_continuous x)

theorem isClosed_lpSolidHull {I : Type*} (x : lp (fun _ : I => ℂ) 2) :
    IsClosed (lpSolidHull x) := (isCompact_lpSolidHull x).isClosed

end
end GaloisForLFunctions.HTGeometry
