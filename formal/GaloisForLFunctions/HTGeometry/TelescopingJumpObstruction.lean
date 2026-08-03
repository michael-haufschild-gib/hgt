import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

/-!
# A telescoping difference cannot have a single jump on an orbit

The discrete-residue obstruction to rational summability is combinatorial.  Along one integer orbit
a rational function `g` has finitely many poles; the poles of the telescoped difference
`g(u+1) - g(u)` occur exactly where the membership indicator of that finite set changes, since at an
extreme pole one of the two terms is regular and cannot cancel the other.

A nonempty finite set of integers always has **two** such change points: the top element, whose
successor is missing, and the predecessor of the bottom element, which is itself missing.  So a
telescoped difference never has exactly one pole on an orbit, and a rational function with a single
pole class on an orbit is not rationally summable.

Both statements below are pure statements about finite sets of integers, and the second is the form
the discrete-residue argument uses.
-/

open scoped BigOperators

namespace GaloisForLFunctions

/-- **Two jumps.**  The membership indicator of a nonempty finite set of integers changes at two
distinct places: after its maximum and before its minimum. -/
theorem exists_two_jumps (S : Finset ℤ) (hS : S.Nonempty) :
    ∃ a b : ℤ, a ≠ b ∧ ¬ ((a ∈ S) ↔ (a + 1 ∈ S)) ∧ ¬ ((b ∈ S) ↔ (b + 1 ∈ S)) := by
  classical
  refine ⟨S.max' hS, S.min' hS - 1, ?_, ?_, ?_⟩
  · have hmin : S.min' hS ≤ S.max' hS := S.min'_le_max' hS
    omega
  · intro hiff
    have hmem : S.max' hS + 1 ∈ S := hiff.mp (S.max'_mem hS)
    have hle : S.max' hS + 1 ≤ S.max' hS := S.le_max' _ hmem
    omega
  · intro hiff
    have hsucc : S.min' hS - 1 + 1 ∈ S := by
      have : S.min' hS - 1 + 1 = S.min' hS := by omega
      rw [this]
      exact S.min'_mem hS
    have hmem : S.min' hS - 1 ∈ S := hiff.mpr hsucc
    have hle : S.min' hS ≤ S.min' hS - 1 := S.min'_le _ hmem
    omega

/-- **A single jump forces emptiness.**  If the membership indicator of a finite set of integers is
constant across every step but one, the set is empty.  This is the discrete-residue obstruction: a
telescoped difference cannot have exactly one pole on an integer orbit. -/
theorem eq_empty_of_single_jump (S : Finset ℤ) (p : ℤ)
    (h : ∀ q : ℤ, q ≠ p → ((q ∈ S) ↔ (q + 1 ∈ S))) : S = ∅ := by
  classical
  by_contra hne
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_jumps S (Finset.nonempty_iff_ne_empty.mpr hne)
  rcases eq_or_ne a p with rfl | hap
  · exact hb (h b (fun hcon => hab (hcon.trans rfl).symm))
  · exact ha (h a hap)

/-! ## The obstruction at the level of pole orders -/

/-- **Two order jumps.**  A finitely supported order function on an orbit changes value at two
distinct steps: after the top of its support and before the bottom. -/
theorem exists_two_order_jumps (f : ℤ → ℕ) (hfin : (Function.support f).Finite)
    (hne : ∃ n, f n ≠ 0) :
    ∃ a b : ℤ, a ≠ b ∧ f a ≠ f (a + 1) ∧ f b ≠ f (b + 1) := by
  classical
  obtain ⟨n₀, hn₀⟩ := hne
  have hmem : n₀ ∈ hfin.toFinset := hfin.mem_toFinset.mpr hn₀
  have hS : hfin.toFinset.Nonempty := ⟨n₀, hmem⟩
  refine ⟨hfin.toFinset.max' hS, hfin.toFinset.min' hS - 1, ?_, ?_, ?_⟩
  · have hle : hfin.toFinset.min' hS ≤ hfin.toFinset.max' hS :=
      hfin.toFinset.min'_le_max' hS
    omega
  · have htop : f (hfin.toFinset.max' hS) ≠ 0 :=
      hfin.mem_toFinset.mp (hfin.toFinset.max'_mem hS)
    have hout : f (hfin.toFinset.max' hS + 1) = 0 := by
      by_contra hcon
      have := hfin.toFinset.le_max' _ (hfin.mem_toFinset.mpr hcon)
      omega
    rw [hout]
    exact htop
  · have hbot : f (hfin.toFinset.min' hS - 1 + 1) ≠ 0 := by
      have hrw : hfin.toFinset.min' hS - 1 + 1 = hfin.toFinset.min' hS := by omega
      rw [hrw]
      exact hfin.mem_toFinset.mp (hfin.toFinset.min'_mem hS)
    have hout : f (hfin.toFinset.min' hS - 1) = 0 := by
      by_contra hcon
      have := hfin.toFinset.min'_le _ (hfin.mem_toFinset.mpr hcon)
      omega
    rw [hout]
    exact fun hcon => hbot hcon.symm

/-- **A single order jump forces the vanishing of the order.** -/
theorem eq_zero_of_single_order_jump (f : ℤ → ℕ) (hfin : (Function.support f).Finite)
    (p : ℤ) (h : ∀ q : ℤ, q ≠ p → f q = f (q + 1)) : ∀ n, f n = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_order_jumps f hfin hcon
  rcases eq_or_ne a p with rfl | hap
  · exact hb (h b fun hcon' => hab (hcon'.trans rfl).symm)
  · exact ha (h a hap)

/-- **The interface form.**  If every order jump of the pole function forces a pole of the
telescoped difference, and the difference has at most one pole on the orbit, then the pole function
vanishes identically: no poles at all. -/
theorem eq_zero_of_jump_poles_subsingleton (f : ℤ → ℕ) (hfin : (Function.support f).Finite)
    (D : Set ℤ) (hD : ∀ n : ℤ, f n ≠ f (n + 1) → n ∈ D) (hsub : D.Subsingleton) :
    ∀ n, f n = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_order_jumps f hfin hcon
  exact hab (hsub (hD a ha) (hD b hb))

end GaloisForLFunctions
