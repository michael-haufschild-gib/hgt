import GaloisForLFunctions.HTGeometry.AtomKernelTailBound

/-!
# A single dominant for the scaled kernel

The infinite-measure case of the atom limit needs no interchange of two limits.  Combining the
constant bound near the node with the Herglotz tail bound away from it produces one dominating
function, independent of the height, valid for all heights at most one.

Near the node it is the constant one, integrable because the measure of a bounded set is finite;
away from the node it is a multiple of the Herglotz weight, integrable by the Herglotz condition.
Dominated convergence then applies directly.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Classical

/-- The scaled kernel never exceeds one, at any height including zero. -/
theorem atomKernel_le_one' (a t y : ℝ) : atomKernel a y t ≤ 1 := by
  rw [atomKernel]
  rcases eq_or_ne ((t - a) ^ (2 : ℕ) + y ^ (2 : ℕ)) 0 with hz | hz
  · rw [hz, div_zero]
    norm_num
  · rw [div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm hz))]
    nlinarith [sq_nonneg (t - a)]

/-- The height-independent dominant: constant near the node, Herglotz weight away from it. -/
def atomDominant (a R : ℝ) (t : ℝ) : ℝ :=
  if |t - a| < R then 1 else tailComparison a R / (1 + t ^ (2 : ℕ))

theorem atomDominant_nonneg {a R : ℝ} (hR : 0 < R) (t : ℝ) : 0 ≤ atomDominant a R t := by
  rw [atomDominant]
  split
  · norm_num
  · have := tailComparison_pos (a := a) hR
    positivity

/-- **The dominant dominates.**  For heights at most one the scaled kernel is bounded by the
height-independent dominant everywhere. -/
theorem atomKernel_le_atomDominant {a R y : ℝ} (hR : 0 < R) (hy : y ^ (2 : ℕ) ≤ 1) (t : ℝ) :
    atomKernel a y t ≤ atomDominant a R t := by
  rw [atomDominant]
  split
  · exact atomKernel_le_one' a t y
  · rename_i hfar
    have hge : R ≤ |t - a| := le_of_not_gt hfar
    refine le_trans (atomKernel_le_tail_weight hR hge) ?_
    have hpos : (0 : ℝ) < 1 + t ^ (2 : ℕ) := by positivity
    have hC : 0 < tailComparison a R := tailComparison_pos (a := a) hR
    rw [div_le_div_iff₀ hpos hpos]
    nlinarith [mul_nonneg (mul_pos hC hpos).le (sub_nonneg.2 hy)]

/-- The dominant is the sum of an indicator of a bounded set and a multiple of the Herglotz weight,
which is the form in which its integrability is checked. -/
theorem atomDominant_eq_indicator (a R : ℝ) (t : ℝ) :
    atomDominant a R t =
      Set.indicator {s : ℝ | |s - a| < R} (fun _ => (1 : ℝ)) t +
        Set.indicator {s : ℝ | ¬ |s - a| < R}
          (fun s => tailComparison a R / (1 + s ^ (2 : ℕ))) t := by
  rw [atomDominant]
  by_cases h : |t - a| < R
  · have hin : t ∈ {s : ℝ | |s - a| < R} := h
    have hout : t ∉ {s : ℝ | ¬ |s - a| < R} := by simpa using h
    rw [if_pos h, Set.indicator_of_mem hin, Set.indicator_of_notMem hout]
    ring
  · have hin : t ∉ {s : ℝ | |s - a| < R} := h
    have hout : t ∈ {s : ℝ | ¬ |s - a| < R} := h
    rw [if_neg h, Set.indicator_of_notMem hin, Set.indicator_of_mem hout]
    ring

end

end GaloisForLFunctions.HTGeometry
