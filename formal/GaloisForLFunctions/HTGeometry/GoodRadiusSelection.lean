import Mathlib

/-!
# Finding a point outside an exceptional set

A set of measure below the length of an interval cannot contain that interval, so the interval holds
a point outside it.  In particular a set of finite measure `M` misses a point of every interval
longer than `M`.

This is the selection step every Borel-type argument needs at scales the doubling lemma does not
reach: the exceptional set of a Wiman–Valiron estimate has finite measure, so good radii occur in
every sufficiently long window, and the length required is fixed rather than shrinking.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

/-- **A short interval meets the good set.**  If the exceptional set has measure below the length of
an interval, that interval contains a point outside it. -/
theorem exists_notMem_of_volume_lt {B : Set ℝ} {a b : ℝ} (_hab : a ≤ b)
    (h : volume B < ENNReal.ofReal (b - a)) : ∃ x ∈ Icc a b, x ∉ B := by
  by_contra hcon
  push Not at hcon
  have hsub : Icc a b ⊆ B := fun x hx => hcon x hx
  have hvol : volume (Icc a b) ≤ volume B := measure_mono hsub
  rw [Real.volume_Icc] at hvol
  exact absurd hvol (not_le.mpr h)

/-- **Every sufficiently long interval beyond the exceptional set meets the good set.**  A set of
finite measure cannot contain an interval longer than that measure. -/
theorem exists_notMem_of_volume_ne_top_of_lt {B : Set ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hB : volume B ≤ ENNReal.ofReal M) {a b : ℝ} (hab : M < b - a) :
    ∃ x ∈ Icc a b, x ∉ B := by
  refine exists_notMem_of_volume_lt (by linarith) (lt_of_le_of_lt hB ?_)
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hab

end GaloisForLFunctions.HTGeometry
