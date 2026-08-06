import GaloisForLFunctions.RHTower.ZetaTwistCuspRadius
import GaloisForLFunctions.RHTower.ZetaStandardTwistDichotomy

/-!
# The cusp gap is the distance to the rest of the spectrum

The two Hurwitz exponents at the shifts `α` and `-α` are the distances from `α`
down to `⌊α⌋` and up to `⌊α⌋ + 1`, so their minimum is the distance from `α` to
the integer lattice — and the integer lattice is exactly the singular set of the
standard twist family.  At a singular shift the distance to the *rest* of the
singular set is one, which is what the two exponents give there as well.

So the growth functional of the factorially normalized shifted twists equals
`1/(2π Δ(α))` with `Δ(α)` read off from the singular set alone.  That is the
cusp radius law at a boundary base point.
-/

open Complex HurwitzZeta Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

section Geometry

theorem fract_eq_zero_iff (α : ℝ) : Int.fract α = 0 ↔ ∃ m : ℤ, (m : ℝ) = α := by
  constructor
  · intro h
    refine ⟨⌊α⌋, ?_⟩
    have := Int.fract_add_floor α
    rw [h, zero_add] at this
    exact this
  · rintro ⟨m, rfl⟩
    exact Int.fract_intCast m

theorem infDist_intRange {α : ℝ} (h : Int.fract α ≠ 0) :
    Metric.infDist α (zetaTwistSingularSet) = min (Int.fract α) (1 - Int.fract α) := by
  have hf0 : 0 < Int.fract α := lt_of_le_of_ne (Int.fract_nonneg α) (Ne.symm h)
  have hf1 : Int.fract α < 1 := Int.fract_lt_one α
  have hfl : (⌊α⌋ : ℝ) ∈ zetaTwistSingularSet :=
    (mem_zetaTwistSingularSet _).mpr ⟨⌊α⌋, rfl⟩
  have hne : (zetaTwistSingularSet).Nonempty := ⟨_, hfl⟩
  have hfr : Int.fract α = α - (⌊α⌋ : ℝ) := rfl
  refine le_antisymm ?_ ?_
  · refine le_min ?_ ?_
    · have hle := Metric.infDist_le_dist_of_mem (x := α) hfl
      rw [Real.dist_eq] at hle
      have habs : |α - (⌊α⌋ : ℝ)| = Int.fract α := by
        rw [← hfr]
        exact abs_of_nonneg (Int.fract_nonneg α)
      rwa [habs] at hle
    · have hmem : ((⌊α⌋ : ℝ) + 1) ∈ zetaTwistSingularSet :=
        (mem_zetaTwistSingularSet _).mpr ⟨⌊α⌋ + 1, by push_cast; ring⟩
      have hle := Metric.infDist_le_dist_of_mem (x := α) hmem
      rw [Real.dist_eq] at hle
      have habs : |α - ((⌊α⌋ : ℝ) + 1)| = 1 - Int.fract α := by
        rw [show α - ((⌊α⌋ : ℝ) + 1) = Int.fract α - 1 from by rw [hfr]; ring,
          abs_of_nonpos (by linarith)]
        ring
      rwa [habs] at hle
  · refine (Metric.le_infDist hne).mpr fun β hβ => ?_
    obtain ⟨m, rfl⟩ := (mem_zetaTwistSingularSet β).mp hβ
    rw [Real.dist_eq]
    have hj : α - (m : ℝ) = ((⌊α⌋ - m : ℤ) : ℝ) + Int.fract α := by
      push_cast
      rw [hfr]
      ring
    rcases le_or_gt 0 (⌊α⌋ - m) with hjs | hjs
    · have hjR : (0 : ℝ) ≤ ((⌊α⌋ - m : ℤ) : ℝ) := by exact_mod_cast hjs
      rw [hj, abs_of_nonneg (by linarith)]
      have : min (Int.fract α) (1 - Int.fract α) ≤ Int.fract α := min_le_left _ _
      linarith
    · have hjR : ((⌊α⌋ - m : ℤ) : ℝ) ≤ -1 := by
        have : (⌊α⌋ - m) ≤ -1 := by omega
        exact_mod_cast this
      rw [hj, abs_of_nonpos (by linarith)]
      have : min (Int.fract α) (1 - Int.fract α) ≤ 1 - Int.fract α := min_le_right _ _
      linarith

/-- **The cusp gap is the distance from the shift to the rest of the singular
set.** -/
theorem infDist_singular_sdiff_eq_twistGap (α : ℝ) :
    Metric.infDist α (zetaTwistSingularSet \ {α}) = twistGap α := by
  by_cases h : Int.fract α = 0
  · have hmem : α ∈ zetaTwistSingularSet :=
      (mem_zetaTwistSingularSet α).mpr ((fract_eq_zero_iff α).mp h)
    rw [infDist_zetaTwistSingularSet_sdiff hmem, twistGap_of_fract_zero h]
  · have hnot : α ∉ zetaTwistSingularSet := by
      intro hc
      exact h ((fract_eq_zero_iff α).mpr ((mem_zetaTwistSingularSet α).mp hc))
    have hset : zetaTwistSingularSet \ {α} = zetaTwistSingularSet :=
      Set.sdiff_singleton_eq_self hnot
    rw [hset, infDist_intRange h, twistGap_of_fract_ne_zero h]

end Geometry

section BoundaryLaw

variable {s₀ : ℂ}

/-- **The cusp radius law at a boundary base point.**  For the standard twist of
the zeta function the growth functional of the factorially normalized shifted
twists at a real shift `α` is exactly `1/(2π Δ(α))`, where `Δ(α)` is the distance
from `α` to the rest of the singular set of the twist family.

The two sides are computed from disjoint data: the left from the Hurwitz formula
and the growth of the two Hurwitz zeta values along a rightward shift, the right
from the location of the singularities of the family. -/
theorem hadamardLimsup_zetaTwistShift_eq_infDist (α : ℝ) (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) :
    hadamardLimsup (fun k : ℕ =>
        expZeta ((α : ℝ) : UnitAddCircle) (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = ENNReal.ofReal
          (1 / (2 * Real.pi * Metric.infDist α (zetaTwistSingularSet \ {α}))) := by
  rw [hadamardLimsup_zetaTwistShift α hs, infDist_singular_sdiff_eq_twistGap α]

/-- **The cusp radius law at an integer shift.**  There the gap is one and the
growth functional is `1/(2π)`, matching the value computed from the functional
equation of the zeta function. -/
theorem hadamardLimsup_zetaTwistShift_int (m : ℤ) (hs : ∀ n : ℕ, s₀ ≠ (n : ℂ)) :
    hadamardLimsup (fun k : ℕ =>
        expZeta (((m : ℝ)) : UnitAddCircle) (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = ENNReal.ofReal (1 / (2 * Real.pi)) := by
  rw [hadamardLimsup_zetaTwistShift (m : ℝ) hs,
    twistGap_of_fract_zero (Int.fract_intCast m), mul_one]

end BoundaryLaw

end RHTower
