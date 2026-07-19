import GaloisForLFunctions.HTGeometry.RootCofactor
import GaloisForLFunctions.HTGeometry.ChristoffelKernel
import GaloisForLFunctions.HTGeometry.ChristoffelDarboux

/-!
# The confluent Christoffel--Darboux identity

At a root `ξ` of `Q_{n+1}`, writing `Q_{n+1} = (X − ξ) G`, the Christoffel--Darboux identity in the
first variable becomes `(x − ξ) Kₙ(x, ξ) hₙ = (x − ξ) G(x) Qₙ(ξ)`.  Both sides are polynomial
functions of `x`, so the common factor cancels — `ℝ` is infinite, so `Polynomial.funext` applies —
and evaluating the cancelled identity at `x = ξ` gives

`Kₙ(ξ, ξ) hₙ = G(ξ) Qₙ(ξ)`.

Since the kernel diagonal is strictly positive, `G(ξ)` and `Qₙ(ξ)` have the same sign.  This
replaces
the classical statement with `Q'_{n+1}(ξ)` and needs no differentiation.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Confluent Christoffel--Darboux.** -/
theorem cdKernel_diag_mul_eq (h : PositiveMomentForm s) (n : ℕ) {xi : ℝ} {G : Polynomial ℝ}
    (hG : monicOrtho s (n + 1) = (X - C xi) * G) :
    (cdKernel s n xi).eval xi * momentInner s (monicOrtho s n) (monicOrtho s n)
      = G.eval xi * (monicOrtho s n).eval xi := by
  have hn0 : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    (monicOrtho_inner_self_pos h n).ne'
  have hxi : (monicOrtho s (n + 1)).eval xi = 0 := by rw [hG]; simp
  have hpoly : (X - C xi) * (cdKernel s n xi * C (momentInner s (monicOrtho s n)
        (monicOrtho s n)))
      = (X - C xi) * (G * C ((monicOrtho s n).eval xi)) := by
    refine Polynomial.funext fun x => ?_
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    have hcd := christoffelDarboux h n x xi
    rw [hxi, mul_zero, sub_zero] at hcd
    have h1 : (cdKernel s n xi).eval x = ∑ k ∈ Finset.range (n + 1),
        (monicOrtho s k).eval x * (monicOrtho s k).eval xi /
          momentInner s (monicOrtho s k) (monicOrtho s k) := by
      rw [cdKernel_symm, cdKernel_eval]
    have hQ : (monicOrtho s (n + 1)).eval x = (x - xi) * G.eval x := by
      rw [hG]; simp
    rw [h1, ← mul_assoc, hcd, hQ]
    field_simp
  have hcancel := mul_left_cancel₀ (X_sub_C_ne_zero xi) hpoly
  have hev := congrArg (Polynomial.eval xi) hcancel
  simpa using hev

/-- **The cofactor and the previous polynomial agree in sign at every root.** -/
theorem cofactor_mul_monicOrtho_pos (h : PositiveMomentForm s) (n : ℕ) {xi : ℝ}
    {G : Polynomial ℝ} (hG : monicOrtho s (n + 1) = (X - C xi) * G) :
    0 < G.eval xi * (monicOrtho s n).eval xi := by
  rw [← cdKernel_diag_mul_eq h n hG]
  exact mul_pos (cdKernel_eval_self_pos h n xi) (monicOrtho_inner_self_pos h n)

end HTGeometry
