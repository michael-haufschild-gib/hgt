import GaloisForLFunctions.RHTower.HermiteGaussianEnvelope
import GaloisForLFunctions.RHTower.HermiteRungRayleighDefect

/-!
# The weighted square of a Hermite derivative is integrable

`exists_poly_hermiteFun` writes `h_n = p · e^{-x²/2}`, so `h_n' = (p' - x p) · e^{-x²/2}` and

```text
x² (h_n'(x))²  =  ( X² (p' - X p)² ).eval x · e^{-x²} ,
```

a polynomial against a Gaussian.  `integrable_polyEval_mul_gauss` then gives integrability on the
whole line.  This is the quantity whose finiteness turns the corpus's `integral_hermiteRungDefect`
into a *uniform* bound on the truncated Rayleigh defect, and hence the trial-space half of the
second-order oscillator law into a rate.
-/

noncomputable section

open MeasureTheory

namespace RHTower

/-- The Hermite derivative in polynomial-times-Gaussian form. -/
theorem deriv_hermiteFun_poly (n : ℕ) :
    ∃ q : Polynomial ℝ, ∀ x : ℝ,
      deriv (hermiteFun n) x = q.eval x * Real.exp (-(1 / 2 * x ^ (2 : ℕ))) := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun n
  refine ⟨Polynomial.derivative p - Polynomial.X * p, fun x => ?_⟩
  have hfun : hermiteFun n = fun y : ℝ => p.eval y * Real.exp (-(1 / 2 * y ^ (2 : ℕ))) := funext hp
  have hgauss : HasDerivAt (fun y : ℝ => Real.exp (-(1 / 2 * y ^ (2 : ℕ))))
      (-x * Real.exp (-(1 / 2 * x ^ (2 : ℕ)))) x := by
    have hinner : HasDerivAt (fun y : ℝ => -(1 / 2 * y ^ (2 : ℕ))) (-x) x := by
      have h := ((hasDerivAt_pow 2 x).const_mul (1 / 2 : ℝ)).neg
      refine h.congr_deriv ?_
      push_cast
      ring
    have h := hinner.exp
    refine h.congr_deriv ?_
    ring
  have hpoly : HasDerivAt (fun y : ℝ => p.eval y) ((Polynomial.derivative p).eval x) x :=
    p.hasDerivAt x
  have hprod : HasDerivAt (fun y : ℝ => p.eval y * Real.exp (-(1 / 2 * y ^ (2 : ℕ))))
      ((Polynomial.derivative p).eval x * Real.exp (-(1 / 2 * x ^ (2 : ℕ)))
        + p.eval x * (-x * Real.exp (-(1 / 2 * x ^ (2 : ℕ))))) x := hpoly.mul hgauss
  rw [hfun, hprod.deriv]
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-- **The weighted square of a Hermite derivative is integrable on the line.** -/
theorem integrable_sq_mul_deriv_hermiteFun_sq (n : ℕ) :
    Integrable (fun x : ℝ => x ^ (2 : ℕ) * deriv (hermiteFun n) x ^ (2 : ℕ)) := by
  obtain ⟨q, hq⟩ := deriv_hermiteFun_poly n
  refine (integrable_polyEval_mul_gauss (Polynomial.X ^ (2 : ℕ) * q ^ (2 : ℕ)) (b := 1)
    (by norm_num)).congr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  show Polynomial.eval x (Polynomial.X ^ (2 : ℕ) * q ^ (2 : ℕ)) * Real.exp (-(1 * x ^ (2 : ℕ)))
    = x ^ (2 : ℕ) * deriv (hermiteFun n) x ^ (2 : ℕ)
  rw [hq x, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_X]
  have hexp : Real.exp (-(1 / 2 * x ^ (2 : ℕ))) * Real.exp (-(1 / 2 * x ^ (2 : ℕ)))
      = Real.exp (-(1 * x ^ (2 : ℕ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc x ^ (2 : ℕ) * q.eval x ^ (2 : ℕ) * Real.exp (-(1 * x ^ (2 : ℕ)))
      = x ^ (2 : ℕ) * (q.eval x ^ (2 : ℕ) * (Real.exp (-(1 / 2 * x ^ (2 : ℕ)))
        * Real.exp (-(1 / 2 * x ^ (2 : ℕ))))) := by rw [hexp]; ring
    _ = x ^ (2 : ℕ) * (q.eval x * Real.exp (-(1 / 2 * x ^ (2 : ℕ)))) ^ (2 : ℕ) := by ring


/-- The truncated weighted square never exceeds its whole-line value. -/
theorem intervalIntegral_sq_mul_deriv_hermiteFun_sq_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in (-R)..R, x ^ (2 : ℕ) * deriv (hermiteFun n) x ^ (2 : ℕ))
      ≤ ∫ x, x ^ (2 : ℕ) * deriv (hermiteFun n) x ^ (2 : ℕ) := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  exact setIntegral_le_integral (integrable_sq_mul_deriv_hermiteFun_sq n)
    (Filter.Eventually.of_forall fun x => by positivity)

/-- **The truncated Rayleigh defect is bounded uniformly in the truncation.**  This is the
quantitative form of `eventually_hermiteRungDefect_pos`: not merely positive, but bounded above by a
constant of the rung. -/
theorem eventually_hermiteRungDefect_le (n : ℕ) :
    ∀ᶠ R : ℝ in Filter.atTop,
      (∫ ξ in (-R)..R, hermiteRungDefect n ξ)
        ≤ (∫ x, x ^ (2 : ℕ) * deriv (hermiteFun n) x ^ (2 : ℕ)) + 1 := by
  have hbd := (tendsto_hermiteRungBoundary n).eventually
    (eventually_abs_sub_lt (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hbd, Filter.eventually_ge_atTop (0 : ℝ)] with R hR hR0
  rw [integral_hermiteRungDefect n R]
  have hsq := intervalIntegral_sq_mul_deriv_hermiteFun_sq_le n hR0
  rw [sub_zero] at hR
  have habs := abs_lt.1 hR
  linarith [hsq, habs.1]

end RHTower

end
