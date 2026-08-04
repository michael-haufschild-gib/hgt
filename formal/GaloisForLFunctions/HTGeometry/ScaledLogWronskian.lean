import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic

/-!
# The scaled logarithmic derivative and its degeneracy

The leading behaviour of a product law's bordered determinant is governed by the *scaled logarithmic
derivative* `T = v·Q'/Q`, whose numerator-cleared derivative is

`Q²·T' = (v'Q' + v·Q'')·Q − v·(Q')²`.

Two facts make this the right object.  It is additive in `Q` — the Wronskian obeys a product rule
`W(P·R) = R²·W(P) + P²·W(R)`, because `T` is a logarithmic derivative — and it **vanishes exactly on
the powers of `v`**: for `Q = K·v^k` with `v` linear, `T = k·v'` is constant.

That is the degenerate locus of the general product law, and the exponential tower sits on it
(`Q = v = X`).  So the tower's determinant argument is the argument at the one place where the scaled
logarithmic derivative carries no information, which is why it does not generalise.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- The cleared derivative of the scaled logarithmic derivative `v·Q'/Q`. -/
noncomputable def scaledLogWronskian (Q v : Polynomial ℂ) : Polynomial ℂ :=
  (v.derivative * Q.derivative + v * Q.derivative.derivative) * Q - v * Q.derivative ^ 2

/-- **The product rule.**  The scaled logarithmic derivative is additive, so its Wronskian is a
weighted sum. -/
theorem scaledLogWronskian_mul (P R v : Polynomial ℂ) :
    scaledLogWronskian (P * R) v
      = R ^ 2 * scaledLogWronskian P v + P ^ 2 * scaledLogWronskian R v := by
  simp only [scaledLogWronskian, derivative_mul, derivative_add]
  ring

@[simp] theorem scaledLogWronskian_C (K : ℂ) (v : Polynomial ℂ) :
    scaledLogWronskian (Polynomial.C K) v = 0 := by
  simp [scaledLogWronskian]

/-- On `v` itself the Wronskian is the curvature of `v`. -/
theorem scaledLogWronskian_self (v : Polynomial ℂ) :
    scaledLogWronskian v v = v ^ 2 * v.derivative.derivative := by
  simp only [scaledLogWronskian]
  ring

/-- **The powers of a linear `v` are the degenerate locus.** -/
theorem scaledLogWronskian_pow {v : Polynomial ℂ} (hv : v.derivative.derivative = 0) (k : ℕ) :
    scaledLogWronskian (v ^ k) v = 0 := by
  induction k with
  | zero => simpa using scaledLogWronskian_C 1 v
  | succ k ih =>
      rw [pow_succ, scaledLogWronskian_mul, ih, scaledLogWronskian_self, hv]
      simp

theorem scaledLogWronskian_C_mul_pow {v : Polynomial ℂ} (hv : v.derivative.derivative = 0)
    (K : ℂ) (k : ℕ) : scaledLogWronskian (Polynomial.C K * v ^ k) v = 0 := by
  rw [scaledLogWronskian_mul, scaledLogWronskian_C, scaledLogWronskian_pow hv]
  simp

end GaloisForLFunctions.HTGeometry
