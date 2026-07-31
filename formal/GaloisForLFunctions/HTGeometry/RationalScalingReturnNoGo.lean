import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Constructions

/-!
# Rational scaling returns: no compact factor makes the diagonal `ℚ₊`-action proper

The candidate globalization of the rectangular prime tangent maps places a compact solenoid
`S` next to a real scaling direction and lets positive rationals act diagonally, scaling the
real coordinate.  Properness of that action is what a Hausdorff lamination quotient needs:
for compact `K`, only finitely many group elements may return `K` to itself.

This file proves the obstruction in abstract, strengthened form — the compact factor is
**arbitrary**, so no choice of solenoid can help:

* `rationalScaling_interval_meets_iff` — the exact return window of the card: for `q > 0`,
  the scaled block `q · [1,2]` meets `[1,2]` iff `q ∈ [1/2, 2]`;
* `infinite_rationalScaling_returns` — infinitely many positive rationals lie in the window;
* `compactFactor_rationalScaling_returns_infinite` — for **any** nonempty compact space `X`,
  the diagonal rational scaling on `X × ℝ` returns the compact block `X × [1,2]` to itself
  for infinitely many positive rationals.  The finite-return (proper-discontinuity) condition
  fails on this single compact witness, so the quotient cannot be the required Hausdorff
  lamination — the noncompact rational-Witt transversal is load-bearing.

Unconditional; no adelic, zeta, or positivity input.
-/

namespace GaloisForLFunctions

noncomputable section

open Set

/-- **The exact return window**: for `q > 0`, the scaled block `q · [1,2]` meets `[1,2]` iff
`1/2 ≤ q ≤ 2`. -/
theorem rationalScaling_interval_meets_iff (q : ℚ) (hq : 0 < q) :
    ((fun t : ℝ => (q : ℝ) * t) '' Icc 1 2 ∩ Icc 1 2).Nonempty ↔
      (q : ℝ) ∈ Icc (1 / 2 : ℝ) 2 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, hx⟩
    obtain ⟨ht1, ht2⟩ := ht
    obtain ⟨hx1, hx2⟩ := hx
    constructor
    · -- `q t ≥ 1` and `t ≤ 2` give `2 q ≥ q t ≥ 1`
      nlinarith
    · -- `q t ≤ 2` and `t ≥ 1` give `q ≤ q t ≤ 2`
      nlinarith
  · rintro ⟨hq1, hq2⟩
    by_cases hqone : (1 : ℝ) ≤ (q : ℝ)
    · -- q ∈ [1, 2]: the point q·1 lies in both
      exact ⟨(q : ℝ) * 1, ⟨1, by constructor <;> norm_num, rfl⟩,
        by constructor <;> nlinarith⟩
    · -- q ∈ [1/2, 1): the point q·2 lies in both
      push Not at hqone
      exact ⟨(q : ℝ) * 2, ⟨2, by constructor <;> norm_num, rfl⟩,
        by constructor <;> nlinarith⟩

/-- Infinitely many positive rationals lie in the return window: `1 + 1/(n+1)` for every
`n`. -/
theorem infinite_rationalScaling_returns :
    {q : ℚ | 0 < q ∧
      ((fun t : ℝ => (q : ℝ) * t) '' Icc 1 2 ∩ Icc 1 2).Nonempty}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => 1 + 1 / ((n : ℚ) + 1))
  · intro a b hab
    have ha : ((a : ℚ) + 1) ≠ 0 := by positivity
    have hb : ((b : ℚ) + 1) ≠ 0 := by positivity
    have h1 : 1 / ((a : ℚ) + 1) = 1 / ((b : ℚ) + 1) := by linarith [add_left_cancel hab]
    have h2 : ((a : ℚ) + 1) = ((b : ℚ) + 1) := by
      field_simp at h1
      linarith
    exact_mod_cast add_right_cancel h2
  · intro n
    have hpos : (0 : ℚ) < 1 + 1 / ((n : ℚ) + 1) := by positivity
    refine ⟨hpos, ?_⟩
    rw [rationalScaling_interval_meets_iff _ hpos]
    have h1 : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one h1]
      linarith
    have hcast : ((1 + 1 / ((n : ℚ) + 1) : ℚ) : ℝ) = 1 + 1 / ((n : ℝ) + 1) := by
      push_cast
      ring
    rw [hcast]
    constructor
    · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · linarith

/-- **No compact factor rescues properness**: for any nonempty compact space `X`, the diagonal
rational scaling on `X × ℝ` returns the compact block `X × [1,2]` to itself for infinitely
many positive rationals.  The finite-return condition of proper discontinuity fails on this
single compact witness. -/
theorem compactFactor_rationalScaling_returns_infinite
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [Nonempty X] :
    IsCompact ((univ : Set X) ×ˢ Icc (1 : ℝ) 2) ∧
    {q : ℚ | 0 < q ∧
      ((fun p : X × ℝ => (p.1, (q : ℝ) * p.2)) ''
          ((univ : Set X) ×ˢ Icc (1 : ℝ) 2) ∩
        ((univ : Set X) ×ˢ Icc (1 : ℝ) 2)).Nonempty}.Infinite := by
  constructor
  · exact isCompact_univ.prod isCompact_Icc
  · apply Set.Infinite.mono _ infinite_rationalScaling_returns
    intro q hq
    obtain ⟨hq0, ⟨x, ⟨t, ht, rfl⟩, hx⟩⟩ := hq
    obtain ⟨s⟩ := ‹Nonempty X›
    refine ⟨hq0, ⟨(s, (q : ℝ) * t), ⟨(s, t), ⟨mem_univ s, ht⟩, rfl⟩,
      ⟨mem_univ s, hx⟩⟩⟩

end

end GaloisForLFunctions
