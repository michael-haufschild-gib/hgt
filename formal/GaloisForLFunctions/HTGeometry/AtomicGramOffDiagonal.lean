import GaloisForLFunctions.HTGeometry.AtomicGramEntrySum

/-!
# The off-diagonal atomic Gram entries vanish linearly

Every atom term of an off-diagonal entry is bounded by the height times an explicit weight built
from the atom separations, whichever of the three cases it falls into.  Summing gives a linear bound
for the whole entry, so the off-diagonal entries vanish with the height.

The two rates are unified first: the quadratically small cases are weakened to the linear rate, so
one weight function covers all three cases.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

open scoped Classical

/-- The separation weight of an atom against a pair of distinct nodes. -/
def offDiagWeight {d : ℕ} (a : Fin d → ℝ) (l m j : Fin d) : ℝ :=
  if j = l then 1 / |a l - a m|
  else if j = m then 1 / |a m - a l|
  else 1 / (|a j - a l| * |a j - a m|)

/-- **The off-diagonal atomic entry vanishes linearly in the height.** -/
theorem norm_atomicGram_offdiag_le {d : ℕ} (a c : Fin d → ℝ)
    (ha : Function.Injective a) {y : ℝ} (hy : y ≠ 0) (hy1 : |y| ≤ 1)
    {l m : Fin d} (hlm : l ≠ m) :
    ‖atomicGram a c y l m‖ ≤ ∑ j, |y| * ‖(c j : ℂ)‖ * offDiagWeight a l m j := by
  classical
  have hlm' : a l ≠ a m := fun h => hlm (ha h)
  refine norm_atomicGram_le_of_termwise a c y l m _ ?_
  intro j
  rw [offDiagWeight]
  by_cases hjl : j = l
  · subst hjl
    rw [if_pos rfl]
    have h := norm_scaled_atomic_distinct_le (a := a j) (b := a m) hy hlm' ((c j : ℂ))
    calc _ ≤ |y| * ‖(c j : ℂ)‖ / |a j - a m| := h
      _ = |y| * ‖(c j : ℂ)‖ * (1 / |a j - a m|) := by ring
  · rw [if_neg hjl]
    by_cases hjm : j = m
    · subst hjm
      rw [if_pos rfl]
      have h := norm_scaled_atomic_mirrored_le (a := a l) (b := a j) hy (Ne.symm hlm')
        ((c j : ℂ))
      calc _ ≤ |y| * ‖(c j : ℂ)‖ / |a j - a l| := h
        _ = |y| * ‖(c j : ℂ)‖ * (1 / |a j - a l|) := by ring
    · rw [if_neg hjm]
      have hja : a j ≠ a l := fun h => hjl (ha h)
      have hjb : a j ≠ a m := fun h => hjm (ha h)
      have h := norm_scaled_atomic_far_le (a := a l) (a' := a m) (b := a j) y hja hjb
        ((c j : ℂ))
      have hsq : y ^ (2 : ℕ) ≤ |y| := sq_le_abs_of_abs_le_one hy1
      have hpos : (0 : ℝ) < |a j - a l| * |a j - a m| := by
        have h1 : (0 : ℝ) < |a j - a l| := abs_pos.2 (sub_ne_zero.2 hja)
        have h2 : (0 : ℝ) < |a j - a m| := abs_pos.2 (sub_ne_zero.2 hjb)
        positivity
      calc _ ≤ y ^ (2 : ℕ) * ‖(c j : ℂ)‖ / (|a j - a l| * |a j - a m|) := h
        _ ≤ |y| * ‖(c j : ℂ)‖ / (|a j - a l| * |a j - a m|) := by
            gcongr
        _ = |y| * ‖(c j : ℂ)‖ * (1 / (|a j - a l| * |a j - a m|)) := by ring

end

end GaloisForLFunctions.HTGeometry
