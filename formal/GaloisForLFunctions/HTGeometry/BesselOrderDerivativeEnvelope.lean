import GaloisForLFunctions.HTGeometry.BesselOrderLaplaceAsymptotic

/-!
# The exterior envelope of the derivative of the order-one Schläfli integral

Differentiating `K₁(z) = ∫₀^∞ e^{-z cosh t} cosh t dt` under the integral sign gives

`K₁'(z) = -∫₀^∞ e^{-z cosh t} cosh² t dt`,

and the same Gaussian majorant as for `K₁` — now with `cosh² t ≤ e^{2t}` in place of
`cosh t ≤ e^t` — yields

`‖K₁'(z)‖ ≤ e^{-Re z}·e^{2/Re z}·√(2π/Re z)`.

The derivative therefore obeys the exponential decay with the same square-root gain: no derivative
loss occurs in the exterior region.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace HTGeometry

/-- The Gaussian integral of a shifted profile. -/
theorem integral_exp_neg_mul_sq_shift (c m : ℝ) :
    (∫ t : ℝ, Real.exp (-c * (t - m) ^ 2)) = Real.sqrt (Real.pi / c) := by
  have hshift : (∫ t : ℝ, Real.exp (-c * (t - m) ^ 2)) = ∫ t : ℝ, Real.exp (-c * t ^ 2) :=
    MeasureTheory.integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun s : ℝ => Real.exp (-c * s ^ 2)) m
  rw [hshift, integral_gaussian]

/-- The derivative of the order-one Schläfli integral. -/
def besselK1CDeriv (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), -(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ))

theorem hasDerivAt_besselK1C_deriv {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt besselK1C (besselK1CDeriv w) w :=
  hasDerivAt_besselK1C hw

theorem norm_besselK1CDeriv_integrand (z : ℂ) (t : ℝ) :
    ‖-(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ))‖
      = Real.cosh t ^ 2 * Real.exp (-(z.re * Real.cosh t)) := by
  rw [norm_mul, norm_neg, norm_pow, Complex.norm_exp, ← Complex.ofReal_cosh, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.cosh_pos t).le]
  congr 1
  simp [Complex.mul_re]

/-- On the positive axis `cosh²` against the decaying exponential of `cosh` is dominated by one
shifted Gaussian. -/
theorem cosh_sq_mul_exp_neg_mul_cosh_le_shift {X t : ℝ} (hX : 0 < X) (ht : 0 ≤ t) :
    Real.cosh t ^ 2 * Real.exp (-(X * Real.cosh t))
      ≤ Real.exp (-X) * Real.exp (2 / X) * Real.exp (-(X / 2) * (t - 2 / X) ^ 2) := by
  have hlow : 1 + t ^ 2 / 2 ≤ Real.cosh t := one_add_sq_div_two_le_cosh ht
  have hup : Real.cosh t ≤ Real.exp t := cosh_le_exp ht
  have hpos : 0 < Real.cosh t := Real.cosh_pos t
  have hsq : Real.cosh t ^ 2 ≤ Real.exp (2 * t) := by
    have hstep : Real.cosh t ^ 2 ≤ Real.exp t ^ 2 := by nlinarith [Real.exp_pos t]
    calc Real.cosh t ^ 2 ≤ Real.exp t ^ 2 := hstep
      _ = Real.exp (2 * t) := by rw [two_mul, Real.exp_add, sq]
  have hexp1 : Real.exp (-(X * Real.cosh t)) ≤ Real.exp (-(X * (1 + t ^ 2 / 2))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hstep : Real.cosh t ^ 2 * Real.exp (-(X * Real.cosh t))
      ≤ Real.exp (2 * t) * Real.exp (-(X * (1 + t ^ 2 / 2))) :=
    mul_le_mul hsq hexp1 (Real.exp_pos _).le (Real.exp_pos _).le
  refine hstep.trans (le_of_eq ?_)
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **The exterior envelope of the Bessel derivative.** -/
theorem norm_besselK1CDeriv_le {z : ℂ} (hz : 0 < z.re) :
    ‖besselK1CDeriv z‖
      ≤ Real.exp (-z.re) * Real.exp (2 / z.re) * Real.sqrt (2 * Real.pi / z.re) := by
  set X := z.re with hX
  have hXpos : 0 < X := hz
  have hX2 : (0 : ℝ) < X / 2 := by linarith
  have hnorm : ‖besselK1CDeriv z‖
      ≤ ∫ t in Ioi (0 : ℝ),
        ‖-(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ))‖ :=
    norm_integral_le_integral_norm _
  refine le_trans hnorm ?_
  have hmaj : ∀ t ∈ Ioi (0 : ℝ),
      ‖-(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ))‖
        ≤ Real.exp (-X) * Real.exp (2 / X) * Real.exp (-(X / 2) * (t - 2 / X) ^ 2) := by
    intro t ht
    rw [norm_besselK1CDeriv_integrand z t]
    exact cosh_sq_mul_exp_neg_mul_cosh_le_shift hXpos (le_of_lt ht)
  have hintmaj : IntegrableOn
      (fun t : ℝ => Real.exp (-X) * Real.exp (2 / X) * Real.exp (-(X / 2) * (t - 2 / X) ^ 2))
      (Ioi 0) :=
    ((integrable_exp_neg_mul_sq_shift hX2).const_mul _).integrableOn
  have hintf : IntegrableOn
      (fun t : ℝ => ‖-(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ))‖)
      (Ioi 0) := by
    refine Integrable.mono' hintmaj ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      have h1 : Measurable fun t : ℝ => Complex.exp (-z * Complex.cosh (t : ℂ)) := by fun_prop
      have h2 : Measurable fun t : ℝ => -(Complex.cosh (t : ℂ)) ^ 2 := by fun_prop
      exact (h2.mul h1).norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hmaj t ht
  have hcomp : (∫ t in Ioi (0 : ℝ),
        ‖-(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ))‖)
      ≤ ∫ t in Ioi (0 : ℝ),
        Real.exp (-X) * Real.exp (2 / X) * Real.exp (-(X / 2) * (t - 2 / X) ^ 2) :=
    setIntegral_mono_on hintf hintmaj measurableSet_Ioi hmaj
  refine le_trans hcomp ?_
  have hfull : (∫ t in Ioi (0 : ℝ),
        Real.exp (-X) * Real.exp (2 / X) * Real.exp (-(X / 2) * (t - 2 / X) ^ 2))
      ≤ ∫ t : ℝ, Real.exp (-X) * Real.exp (2 / X)
          * Real.exp (-(X / 2) * (t - 2 / X) ^ 2) := by
    refine setIntegral_le_integral ((integrable_exp_neg_mul_sq_shift hX2).const_mul _) ?_
    filter_upwards with t
    positivity
  refine le_trans hfull (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_mul_sq_shift]
  congr 2
  field_simp

end HTGeometry

end
