import GaloisForLFunctions.HTGeometry.NevDenominatorFactor

/-!
# The `B, D` Wronskian is the reproducing kernel

Both truncated entries are two-term combinations of `Q_{n+1}` and `Qₙ` (link to
`NevDenominatorFactor`), so the combination `Bₙ(x)Dₙ(y) − Dₙ(x)Bₙ(y)` collapses: the coefficient that
survives is the Wronskian at the origin, and the polynomial factor is the Christoffel--Darboux
numerator.  What is left is

`Bₙ(x)Dₙ(y) − Dₙ(x)Bₙ(y) = h₀·(x − y)·Kₙ(x,y)`.

Setting `y` to a zero of `Bₙ·τ − Dₙ` turns the left side into `(Bₙ(x)τ − Dₙ(x))·Bₙ(y)`, which
exhibits the denominator as a linear factor times a kernel — the source of the sign change at a node.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The `B, D` Wronskian identity at finite level.** -/
theorem nevBD_wronskian (h : PositiveMomentForm s) (n : ℕ) (x y : ℝ) :
    nevBreal s n x * nevDreal s n y - nevDreal s n x * nevBreal s n y
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          ((x - y) * (cdKernel s n x).eval y) := by
  have hnne : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    (monicOrtho_inner_self_pos h n).ne'
  have h0ne : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
    (monicOrtho_inner_self_pos h 0).ne'
  have hcd := christoffelDarboux h n x y
  rw [eq_div_iff hnne] at hcd
  have hker := cdKernel_eval s n x y
  have hw := wronskian_eval_zero h n
  rw [nevBreal_closed h n x, nevBreal_closed h n y, nevDreal_closed h n x,
    nevDreal_closed h n y]
  rw [← hker] at hcd
  set A1 := (monicOrtho s (n + 1)).eval x with hA1
  set A0 := (monicOrtho s n).eval x with hA0
  set B1 := (monicOrtho s (n + 1)).eval y with hB1
  set B0 := (monicOrtho s n).eval y with hB0
  set P1 := (monicOrtho s (n + 1)).eval 0 with hP1
  set P0 := (monicOrtho s n).eval 0 with hP0
  set R1 := (secondKind s (n + 1)).eval 0 with hR1
  set R0 := (secondKind s n).eval 0 with hR0
  set hn' := momentInner s (monicOrtho s n) (monicOrtho s n) with hhn
  set h0' := momentInner s (monicOrtho s 0) (monicOrtho s 0) with hh0
  set K := (cdKernel s n x).eval y with hK
  -- the three scalar facts
  have hstep2 : P0 * R1 - P1 * R0 = hn' / h0' := by
    have : P1 * R0 - P0 * R1 = -(hn' / h0') := hw
    linarith
  have hstep3 : A1 * B0 - A0 * B1 = hn' * ((x - y) * K) := by
    have : (x - y) * K * hn' = A1 * B0 - A0 * B1 := hcd
    linarith
  have hexpand : h0' / hn' * (R0 * A1 - R1 * A0) * (h0' / hn' * (P0 * B1 - P1 * B0))
      - h0' / hn' * (P0 * A1 - P1 * A0) * (h0' / hn' * (R0 * B1 - R1 * B0))
      = h0' ^ (2 : ℕ) / hn' ^ (2 : ℕ) * ((P0 * R1 - P1 * R0) * (A1 * B0 - A0 * B1)) := by
    field_simp
    ring
  rw [hexpand, hstep2, hstep3]
  field_simp

end HTGeometry
