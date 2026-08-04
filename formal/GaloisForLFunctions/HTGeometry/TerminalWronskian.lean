import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Complex.Basic

/-!
# The terminal multiplier is not constant in its own coordinate

The multiplier of a coordinate jet contains, at the newest coordinate, the rational function

`W = Q'·v/Q + α·Q`.

It is constant in that coordinate exactly when the polynomial Wronskian `N'·Q − N·Q'` vanishes, where
`N = Q'·v + α·Q²` is the cleared numerator.  Expanding,

`N'·Q − N·Q' = α·Q²·Q' + ((Q'v)'·Q − (Q')²·v)`,

and for `deg Q ≥ 1` and linear `v` the first term has degree `3·deg Q − 1` while the rest has degree at
most `2·deg Q − 1`.  So the Wronskian is nonzero, and the multiplier genuinely depends on its own
coordinate — the diagonal entry of the height induction.

The exponential tower is the degenerate-looking case `Q = v = X`, where the Wronskian is `α·X²` — the
statement is sharp: for constant `Q` the multiplier really is independent of the coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- The cleared numerator of the terminal multiplier. -/
noncomputable def terminalNumer (Q v : Polynomial ℂ) (α : ℂ) : Polynomial ℂ :=
  Q.derivative * v + Polynomial.C α * Q ^ 2

/-- The Wronskian of the numerator against the denominator. -/
noncomputable def terminalWronskian (Q v : Polynomial ℂ) (α : ℂ) : Polynomial ℂ :=
  (terminalNumer Q v α).derivative * Q - terminalNumer Q v α * Q.derivative

theorem terminalWronskian_expand (Q v : Polynomial ℂ) (α : ℂ) :
    terminalWronskian Q v α
      = Polynomial.C α * (Q ^ 2 * Q.derivative)
        + ((Q.derivative * v).derivative * Q - Q.derivative ^ 2 * v) := by
  rw [terminalWronskian, terminalNumer]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_pow, zero_mul, zero_add]
  ring

/-- **The terminal multiplier is nonconstant in its coordinate.**  For a nonconstant `Q`, a linear
`v` and a nonzero slope, the Wronskian does not vanish. -/
theorem terminalWronskian_ne_zero {Q v : Polynomial ℂ} {α : ℂ}
    (hα : α ≠ 0) (hQ : 1 ≤ Q.natDegree) (hv : v.degree ≤ 1) :
    terminalWronskian Q v α ≠ 0 := by
  have hQ0 : Q ≠ 0 := fun h => by simp [h] at hQ
  have hQ'0 : Q.derivative ≠ 0 := by
    intro h
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
    omega
  have hdegQ : Q.degree = (Q.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hQ0
  have hdegQ' : Q.derivative.degree = ((Q.natDegree - 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hQ'0, Polynomial.natDegree_derivative_eq _ (by omega)]
  -- the dominant term
  have hmain : (Polynomial.C α * (Q ^ 2 * Q.derivative)).degree
      = ((2 * Q.natDegree + (Q.natDegree - 1) : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hα, zero_add, Polynomial.degree_mul,
      Polynomial.degree_pow, hdegQ, hdegQ']
    push_cast
    ring
  -- the remaining terms
  have hrest : ((Q.derivative * v).derivative * Q - Q.derivative ^ 2 * v).degree
      ≤ ((2 * Q.natDegree - 1 : ℕ) : WithBot ℕ) := by
    refine le_trans (Polynomial.degree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.degree_mul_le _ _) ?_
      have h1 : (Q.derivative * v).derivative.degree ≤ ((Q.natDegree - 1 : ℕ) : WithBot ℕ) := by
        refine le_trans (Polynomial.degree_derivative_le) ?_
        refine le_trans (Polynomial.degree_mul_le _ _) ?_
        rw [hdegQ']
        exact le_trans (add_le_add_left hv _) (by push_cast; omega_nat_cast_le)
      calc (Q.derivative * v).derivative.degree + Q.degree
          ≤ ((Q.natDegree - 1 : ℕ) : WithBot ℕ) + (Q.natDegree : WithBot ℕ) :=
            add_le_add h1 (le_of_eq hdegQ)
        _ = ((Q.natDegree - 1 + Q.natDegree : ℕ) : WithBot ℕ) := by push_cast; ring
        _ ≤ ((2 * Q.natDegree - 1 : ℕ) : WithBot ℕ) := by
            exact_mod_cast Nat.cast_le.mpr (by omega)
    · refine le_trans (Polynomial.degree_mul_le _ _) ?_
      have h2 : (Q.derivative ^ 2).degree ≤ ((2 * (Q.natDegree - 1) : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_pow, hdegQ']
        push_cast
        ring_nf
        exact le_refl _
      calc (Q.derivative ^ 2).degree + v.degree
          ≤ ((2 * (Q.natDegree - 1) : ℕ) : WithBot ℕ) + 1 := add_le_add h2 hv
        _ ≤ ((2 * Q.natDegree - 1 : ℕ) : WithBot ℕ) := by
            exact_mod_cast Nat.cast_le.mpr (by omega)
  have hlt : ((2 * Q.natDegree - 1 : ℕ) : WithBot ℕ)
      < ((2 * Q.natDegree + (Q.natDegree - 1) : ℕ) : WithBot ℕ) := by
    exact_mod_cast Nat.cast_lt.mpr (by omega)
  rw [terminalWronskian_expand]
  intro h0
  have hdeg := Polynomial.degree_add_eq_left_of_degree_lt
    (p := Polynomial.C α * (Q ^ 2 * Q.derivative))
    (q := (Q.derivative * v).derivative * Q - Q.derivative ^ 2 * v)
    (by rw [hmain]; exact lt_of_le_of_lt hrest hlt)
  rw [h0, Polynomial.degree_zero, hmain] at hdeg
  exact absurd hdeg.symm (by simp)

end GaloisForLFunctions.HTGeometry
