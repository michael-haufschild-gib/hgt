import Mathlib.Analysis.Complex.Poisson

/-!
# The Szegő (outer) function — foundation for the Szegő upper bound

The Szegő function of a weight `w` on the unit circle is the exponential of the Herglotz–Riesz
integral of `½ log w`.  On the open disk it is analytic and nowhere zero; its boundary modulus
recovers `w` almost everywhere (Fatou's theorem), and its value at the origin encodes the geometric
mean.  It is the extremal object of the Szegő upper bound `⨅ₙ ‖Φₙ‖² ≤ GM(w)` (the `≤` half of the
first Szegő limit theorem): the reversed Taylor polynomials of `D(0)/D` are the approximating
polynomials.

This module builds the Fatou-free foundation:

* `szegoOuter` — the outer function `D`;
* `normSq_szegoOuter_zero` — `‖D(0)‖² = exp((2π)⁻¹∫ log w) = GM(w)`.

The remaining inputs (analyticity on the disk, and the boundary identity `|D|² = w` a.e. — Fatou) are
the deep classical steps; `‖D(0)‖² = GM` already fixes the target value the construction must hit.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex intervalIntegral MeasureTheory
open scoped Real

/-- The Szegő (outer) function of a weight `w`: the exponential of the Herglotz–Riesz integral of
`½ log w`. -/
noncomputable def szegoOuter (w : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((1 / (4 * π) : ℂ) *
    ∫ θ in (0:ℝ)..(2 * π), -herglotzRieszKernel 0 (circleMap 0 1 θ) z * (Real.log (w θ) : ℂ))

/-- At the center the negated Herglotz–Riesz kernel is `1`. -/
theorem neg_herglotz_zero (θ : ℝ) :
    -herglotzRieszKernel 0 (circleMap 0 1 θ) 0 = 1 := by
  rw [herglotzRieszKernel_def]
  have hne : circleMap 0 1 θ ≠ 0 := by simp [circleMap, Complex.exp_ne_zero]
  field_simp
  ring

/-- The Szegő function is nowhere zero (it is an exponential). -/
theorem szegoOuter_ne_zero (w : ℝ → ℝ) (z : ℂ) : szegoOuter w z ≠ 0 :=
  Complex.exp_ne_zero _

/-- **The squared modulus of the Szegő function at the origin is the Szegő geometric mean of the
weight**: `‖D(0)‖² = exp((2π)⁻¹∫₀²π log w)`.  This is the exact value the boundary construction must
attain in the Szegő upper bound. -/
theorem normSq_szegoOuter_zero (w : ℝ → ℝ) :
    ‖szegoOuter w 0‖ ^ 2 = Real.exp ((1 / (2 * π)) * ∫ θ in (0:ℝ)..(2 * π), Real.log (w θ)) := by
  have hint :
      (∫ θ in (0:ℝ)..(2 * π), -herglotzRieszKernel 0 (circleMap 0 1 θ) 0 * (Real.log (w θ) : ℂ))
        = ((∫ θ in (0:ℝ)..(2 * π), Real.log (w θ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [neg_herglotz_zero, one_mul]
  rw [szegoOuter, hint,
    show ((1 / (4 * π) : ℂ) * ((∫ θ in (0:ℝ)..(2 * π), Real.log (w θ) : ℝ) : ℂ))
      = (((1 / (4 * π)) * ∫ θ in (0:ℝ)..(2 * π), Real.log (w θ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp, Complex.ofReal_re, ← Real.exp_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
