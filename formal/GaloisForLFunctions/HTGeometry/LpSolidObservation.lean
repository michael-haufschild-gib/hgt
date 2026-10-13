import GaloisForLFunctions.HTGeometry.LpSolidHull
import Mathlib.Topology.Order.Compact

/-! # The attained worst observation over a fixed history's masks

The supremum of all masked responses is finite and attained by an actual
coordinate mask. Its budget is the operator norm times the history norm.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

variable {I Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

def lpSolidObservation (T : lp (fun _ : I => ℂ) 2 →L[ℂ] Y)
    (x : lp (fun _ : I => ℂ) 2) : ℝ :=
  sSup ((fun y => ‖T y‖) '' lpSolidHull x)

theorem lpSolidObservation_attained (T : lp (fun _ : I => ℂ) 2 →L[ℂ] Y)
    (x : lp (fun _ : I => ℂ) 2) :
    ∃ m : LpCoordinateMask I, ‖T (lpMaskedHistory x m)‖ = lpSolidObservation T x := by
  have hzero : (0 : lp (fun _ : I => ℂ) 2) ∈ lpSolidHull x := by
    intro i
    simp only [lp.coeFn_zero, Pi.zero_apply, norm_zero, norm_nonneg]
  have hK := (isCompact_lpSolidHull x).image T.continuous.norm
  obtain ⟨y, hy, he⟩ := hK.sSup_mem ((show (lpSolidHull x).Nonempty from ⟨0, hzero⟩).image _)
  rw [← range_lpMaskedHistory] at hy
  obtain ⟨m, rfl⟩ := hy
  exact ⟨m, he⟩

theorem lpSolidObservation_nonneg (T : lp (fun _ : I => ℂ) 2 →L[ℂ] Y)
    (x : lp (fun _ : I => ℂ) 2) : 0 ≤ lpSolidObservation T x := by
  obtain ⟨m, hm⟩ := lpSolidObservation_attained T x
  rw [← hm]
  exact norm_nonneg _

theorem norm_apply_le_lpSolidObservation (T : lp (fun _ : I => ℂ) 2 →L[ℂ] Y)
    {x y : lp (fun _ : I => ℂ) 2} (hy : y ∈ lpSolidHull x) :
    ‖T y‖ ≤ lpSolidObservation T x :=
  le_csSup ((isCompact_lpSolidHull x).image T.continuous.norm).bddAbove ⟨y, hy, rfl⟩

theorem norm_masked_le_lpSolidObservation (T : lp (fun _ : I => ℂ) 2 →L[ℂ] Y)
    (x : lp (fun _ : I => ℂ) 2) (m : LpCoordinateMask I) :
    ‖T (lpMaskedHistory x m)‖ ≤ lpSolidObservation T x :=
  norm_apply_le_lpSolidObservation T (lpMaskedHistory_mem_solidHull x m)

theorem lpSolidObservation_le (T : lp (fun _ : I => ℂ) 2 →L[ℂ] Y)
    (x : lp (fun _ : I => ℂ) 2) : lpSolidObservation T x ≤ ‖T‖ * ‖x‖ := by
  obtain ⟨m, hm⟩ := lpSolidObservation_attained T x
  rw [← hm]
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (lpSolidHull_norm_le (lpMaskedHistory_mem_solidHull x m)) (norm_nonneg _))

end
end GaloisForLFunctions.HTGeometry
