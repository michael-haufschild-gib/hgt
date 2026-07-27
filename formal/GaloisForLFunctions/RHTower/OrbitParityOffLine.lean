import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Even

/-!
# Orbit parity of the off-critical part of a symmetric divisor

Let a divisor in the `s`-plane be invariant under the functional-equation involution `s ↦ 1 - s`
and under Schwarz conjugation `s ↦ conj s`.  Their composite

`feSchwarz s = 1 - conj s`

is again an involution, it preserves the ordinate `Im s`, it reflects the abscissa across `1/2`,
and its fixed points are exactly the points of the critical line.

Consequently, on any single ordinate, the total multiplicity carried by points *off* the critical
line is **even**: those points come in genuine two-element orbits `1/2 ± δ + iγ`, whereas an
on-critical point is a fixed point and contributes an orbit of size one.

The arithmetic consequence is a parity constraint on divisor relocation: a deformation that moves
a symmetric divisor off the critical line while preserving the multiplicity at each ordinate can
only move multiplicity that was already even.  A simple on-critical zero cannot be relocated
transversally at fixed ordinate multiplicity.

Everything here is finite combinatorics of one involution; no analytic input is used.
-/

open Finset

namespace RHTower

/-- The composite of the functional-equation involution `s ↦ 1 - s` with Schwarz conjugation. -/
def feSchwarz (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

@[simp] theorem feSchwarz_re (s : ℂ) : (feSchwarz s).re = 1 - s.re := by
  simp [feSchwarz]

@[simp] theorem feSchwarz_im (s : ℂ) : (feSchwarz s).im = s.im := by
  simp [feSchwarz]

theorem feSchwarz_involutive : Function.Involutive feSchwarz := by
  intro s
  apply Complex.ext <;> simp

/-- The fixed points of `feSchwarz` are exactly the points of the critical line. -/
theorem feSchwarz_eq_self_iff {s : ℂ} : feSchwarz s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    rw [feSchwarz_re] at this
    linarith
  · intro h
    apply Complex.ext
    · rw [feSchwarz_re, h]; norm_num
    · rw [feSchwarz_im]

/-- **Orbit parity.**  If a finite family of points is stable under `feSchwarz`, carries a
`feSchwarz`-invariant multiplicity, and avoids the critical line, then its total multiplicity is
even: the points pair off into genuine two-element orbits. -/
theorem even_sum_of_offCritical
    (D : ℂ → ℕ) (S : Finset ℂ)
    (hS : ∀ s ∈ S, feSchwarz s ∈ S)
    (hD : ∀ s, D (feSchwarz s) = D s)
    (hoff : ∀ s ∈ S, s.re ≠ 1 / 2) :
    Even (∑ s ∈ S, D s) := by
  classical
  set L : Finset ℂ := S.filter (fun s => s.re < 1 / 2) with hL
  set R : Finset ℂ := S.filter (fun s => 1 / 2 < s.re) with hR
  have hdisj : Disjoint L R := by
    refine Finset.disjoint_left.2 ?_
    intro a haL haR
    rw [hL, Finset.mem_filter] at haL
    rw [hR, Finset.mem_filter] at haR
    linarith [haL.2, haR.2]
  have hunion : L ∪ R = S := by
    apply Finset.Subset.antisymm
    · intro a ha
      rcases Finset.mem_union.1 ha with h | h
      · exact (Finset.mem_filter.1 h).1
      · exact (Finset.mem_filter.1 h).1
    · intro a ha
      rcases lt_trichotomy a.re (1 / 2 : ℝ) with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ha, h⟩)
      · exact absurd h (hoff a ha)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ha, h⟩)
  have hbij : ∑ s ∈ L, D s = ∑ s ∈ R, D s := by
    refine Finset.sum_nbij' (i := fun s => feSchwarz s) (j := fun s => feSchwarz s)
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [hL, Finset.mem_filter] at ha
      rw [hR, Finset.mem_filter]
      refine ⟨hS a ha.1, ?_⟩
      rw [feSchwarz_re]
      linarith [ha.2]
    · intro a ha
      rw [hR, Finset.mem_filter] at ha
      rw [hL, Finset.mem_filter]
      refine ⟨hS a ha.1, ?_⟩
      rw [feSchwarz_re]
      linarith [ha.2]
    · intro a _
      exact feSchwarz_involutive a
    · intro a _
      exact feSchwarz_involutive a
    · intro a _
      exact (hD a).symm
  have hsplit : ∑ s ∈ S, D s = ∑ s ∈ L, D s + ∑ s ∈ R, D s := by
    rw [← hunion, Finset.sum_union hdisj]
  rw [hsplit, ← hbij]
  exact ⟨∑ s ∈ L, D s, rfl⟩

/-- **Relocation parity.**  Restated for use as a scope constraint: a symmetric divisor whose
off-critical part at one ordinate has odd total multiplicity cannot exist.  Equivalently, moving a
divisor off the critical line at fixed ordinate multiplicity consumes an even amount of
multiplicity. -/
theorem not_odd_sum_of_offCritical
    (D : ℂ → ℕ) (S : Finset ℂ)
    (hS : ∀ s ∈ S, feSchwarz s ∈ S)
    (hD : ∀ s, D (feSchwarz s) = D s)
    (hoff : ∀ s ∈ S, s.re ≠ 1 / 2) :
    ¬ Odd (∑ s ∈ S, D s) := by
  have h := even_sum_of_offCritical D S hS hD hoff
  intro hodd
  exact (Nat.not_odd_iff_even.2 h) hodd

end RHTower
