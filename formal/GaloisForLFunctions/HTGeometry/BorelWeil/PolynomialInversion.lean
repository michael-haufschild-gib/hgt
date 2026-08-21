/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# A vanishing criterion for polynomials related by an inversion

If two polynomials over an infinite field satisfy `x ^ d * q(x) = r(-x⁻¹)` for every `x ≠ 0` with
`d > 0`, then `q = 0`.  Indeed the right-hand side, after clearing denominators, is a polynomial of
degree at most `deg r`, whereas the left-hand side has degree at least `d + deg r` unless `q`
vanishes.

This is the degree bookkeeping behind the Borel–Weil vanishing theorem for non-dominant weights.
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Polynomial

variable {k : Type*} [Field k] [Infinite k]

/-- **Inversion vanishing criterion.** -/
theorem eq_zero_of_pow_mul_eval {q r : Polynomial k} {d : ℕ} (hd : 0 < d)
    (h : ∀ x : k, x ≠ 0 → x ^ d * q.eval x = r.eval (-x⁻¹)) : q = 0 := by
  classical
  set p : Polynomial k := r.comp (-Polynomial.X) with hp
  have hpe : ∀ y : k, p.eval y = r.eval (-y) := by
    intro y; simp [hp, Polynomial.eval_comp]
  set D := p.natDegree with hD
  set pr := p.reflect D with hpr
  have hpr_eval : ∀ x : k, x ≠ 0 → pr.eval x = x ^ D * p.eval x⁻¹ := by
    intro x hx
    haveI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
    have hmain := Polynomial.eval₂_reflect_mul_pow (RingHom.id k) (x⁻¹) D p (le_of_eq hD.symm)
    have hinv : (⅟(x⁻¹) : k) = x := by
      rw [invOf_eq_inv, inv_inv]
    rw [hinv] at hmain
    simp only [Polynomial.eval₂_id] at hmain
    rw [← hmain, ← hpr,
      show (x : k) ^ D * (Polynomial.eval x pr * (x⁻¹ : k) ^ D)
          = Polynomial.eval x pr * ((x : k) ^ D * (x⁻¹ : k) ^ D) by ring,
      ← mul_pow, mul_inv_cancel₀ hx, one_pow, mul_one]
  have key : Polynomial.X ^ (d + D) * q = pr := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ ((Set.finite_singleton (0 : k)).infinite_compl)
    intro x hx
    have hx0 : x ≠ 0 := hx
    simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hpr_eval x hx0, hpe x⁻¹, ← h x hx0, pow_add]
    ring
  have hdeg : pr.natDegree ≤ D := by
    have h0 := Polynomial.natDegree_reflect_le (N := D) (p := p)
    rw [← hD, max_self, ← hpr] at h0
    exact h0
  by_contra hq
  have hne : (Polynomial.X : Polynomial k) ^ (d + D) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hdeg2 : (Polynomial.X ^ (d + D) * q).natDegree = d + D + q.natDegree := by
    rw [Polynomial.natDegree_mul hne hq, Polynomial.natDegree_X_pow]
  rw [key] at hdeg2
  omega

end GaloisForLFunctions.HTGeometry.BorelWeil
