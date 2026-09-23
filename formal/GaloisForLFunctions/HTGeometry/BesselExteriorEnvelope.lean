import GaloisForLFunctions.HTGeometry.PrincipalSquareRoot
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The exterior envelope of the modified Bessel function of complex argument

For `Re z > 0` the Schläfli integral

`K₁(z) = ∫₀^∞ e^{-z cosh t} cosh t dt`

converges, and its modulus is bounded by the same integral with `z` replaced by `Re z`.  Using
`cosh t ≥ 1 + t²/2` and `cosh t ≤ e^t` the remaining real integral is a Gaussian, giving the
exterior envelope

`‖K₁(z)‖ ≤ e^{-Re z}·e^{1/(2 Re z)}·√(2π/Re z)`,

which is the exact exponential decay with the square-root gain.

The companion geometric fact concerns the principal square root `z_u(h) = √((σ+iu)² + h²)`.  Its
real part dominates `√(h² - u² + σ²)`, and outside a fixed cone `h ≥ κu` the ratio
`(σ+iu)/z_u(h)` is bounded — the two inputs of the exterior Bessel estimate.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace HTGeometry

/-! ## Elementary hyperbolic bounds -/

theorem one_add_sq_div_two_le_cosh {t : ℝ} (ht : 0 ≤ t) : 1 + t ^ (2 : ℕ) / 2 ≤ Real.cosh t := by
  have hhalf : (0 : ℝ) ≤ t / 2 := by linarith
  have hsinh : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.mpr hhalf
  have hsq : (t / 2) ^ (2 : ℕ) ≤ Real.sinh (t / 2) ^ (2 : ℕ) := by
    apply pow_le_pow_left₀ hhalf hsinh
  have hdouble : Real.cosh (2 * (t / 2)) = 2 * Real.sinh (t / 2) ^ (2 : ℕ) + 1 := by
    rw [Real.cosh_two_mul, Real.cosh_sq]
    ring
  have ht2 : (2 : ℝ) * (t / 2) = t := by ring
  rw [ht2] at hdouble
  rw [hdouble]
  nlinarith [hsq]

theorem cosh_le_exp {t : ℝ} (ht : 0 ≤ t) : Real.cosh t ≤ Real.exp t := by
  rw [Real.cosh_eq]
  have h : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.2 (by linarith)
  linarith

/-! ## The Gaussian majorant -/

theorem integrable_exp_quadratic {X : ℝ} (hX : 0 < X) :
    Integrable fun t : ℝ => Real.exp (-(X / 2) * (t - 1 / X) ^ (2 : ℕ)) := by
  have hbase : Integrable fun t : ℝ => Real.exp (-(X / 2) * t ^ (2 : ℕ)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have := hbase.comp_sub_right (1 / X)
  simpa using this

theorem integral_exp_quadratic {X : ℝ} (hX : 0 < X) :
    (∫ t : ℝ, Real.exp (-(X / 2) * (t - 1 / X) ^ (2 : ℕ))) = Real.sqrt (2 * Real.pi / X) := by
  have hshift : (∫ t : ℝ, Real.exp (-(X / 2) * (t - 1 / X) ^ (2 : ℕ)))
      = ∫ t : ℝ, Real.exp (-(X / 2) * t ^ (2 : ℕ)) :=
    MeasureTheory.integral_sub_right_eq_self
      (μ := (volume : Measure ℝ)) (fun s : ℝ => Real.exp (-(X / 2) * s ^ (2 : ℕ))) (1 / X)
  rw [hshift, integral_gaussian]
  congr 1
  field_simp

/-- The Gaussian completion of the square. -/
theorem exp_quadratic_eq {X : ℝ} (hX : 0 < X) (t : ℝ) :
    Real.exp (-(X * (1 + t ^ (2 : ℕ) / 2)) + t)
      = Real.exp (-X) * Real.exp (1 / (2 * X)) * Real.exp (-(X / 2) * (t - 1 / X) ^ (2 : ℕ)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-! ## The exterior envelope -/

/-- The modified Bessel function `K₁` of complex argument, by the Schläfli integral. -/
def besselK1C (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (-z * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ)

theorem norm_besselK1C_integrand (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-z * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ)‖
      = Real.exp (-(z.re * Real.cosh t)) * Real.cosh t := by
  rw [norm_mul, Complex.norm_exp, ← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.cosh_pos t).le]
  congr 1
  simp [Complex.mul_re]

/-- **The exterior Bessel envelope.**  On the right half plane the Schläfli integral is bounded by
the Gaussian majorant of its real part. -/
theorem norm_besselK1C_le {z : ℂ} (hz : 0 < z.re) :
    ‖besselK1C z‖
      ≤ Real.exp (-z.re) * Real.exp (1 / (2 * z.re)) * Real.sqrt (2 * Real.pi / z.re) := by
  set X := z.re with hX
  have hXpos : 0 < X := hz
  have hnorm : ‖besselK1C z‖
      ≤ ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-z * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ)‖ :=
    norm_integral_le_integral_norm _
  refine le_trans hnorm ?_
  have hmaj : ∀ t ∈ Ioi (0 : ℝ),
      ‖Complex.exp (-z * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ)‖
        ≤ Real.exp (-X) * Real.exp (1 / (2 * X)) * Real.exp (-(X / 2) * (t - 1 / X) ^ (2 : ℕ)) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [norm_besselK1C_integrand z t]
    have hlow : 1 + t ^ (2 : ℕ) / 2 ≤ Real.cosh t := one_add_sq_div_two_le_cosh ht0
    have hup : Real.cosh t ≤ Real.exp t := cosh_le_exp ht0
    have hexp1 : Real.exp (-(X * Real.cosh t)) ≤ Real.exp (-(X * (1 + t ^ (2 : ℕ) / 2))) := by
      apply Real.exp_le_exp.2
      nlinarith
    have hstep : Real.exp (-(X * Real.cosh t)) * Real.cosh t
        ≤ Real.exp (-(X * (1 + t ^ (2 : ℕ) / 2))) * Real.exp t := by
      apply mul_le_mul hexp1 hup (le_of_lt (Real.cosh_pos t)) (le_of_lt (Real.exp_pos _))
    refine le_trans hstep (le_of_eq ?_)
    rw [← Real.exp_add]
    exact exp_quadratic_eq hXpos t
  have hintmaj : IntegrableOn
      (fun t : ℝ => Real.exp (-X) * Real.exp (1 / (2 * X)) * Real.exp (-(X / 2) * (t - 1 / X) ^ (2 : ℕ)))
      (Ioi 0) :=
    ((integrable_exp_quadratic hXpos).const_mul _).integrableOn
  have hintf : IntegrableOn
      (fun t : ℝ => ‖Complex.exp (-z * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ)‖)
      (Ioi 0) := by
    refine Integrable.mono' hintmaj ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      have h1 : Measurable fun t : ℝ => Complex.exp (-z * Complex.cosh (t : ℂ)) := by
        fun_prop
      have h2 : Measurable fun t : ℝ => Complex.cosh (t : ℂ) := by fun_prop
      exact (h1.mul h2).norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hmaj t ht
  have hcomp : (∫ t in Ioi (0 : ℝ),
        ‖Complex.exp (-z * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ)‖)
      ≤ ∫ t in Ioi (0 : ℝ),
        Real.exp (-X) * Real.exp (1 / (2 * X)) * Real.exp (-(X / 2) * (t - 1 / X) ^ (2 : ℕ)) :=
    setIntegral_mono_on hintf hintmaj measurableSet_Ioi hmaj
  refine le_trans hcomp ?_
  have hfull : (∫ t in Ioi (0 : ℝ),
        Real.exp (-X) * Real.exp (1 / (2 * X)) * Real.exp (-(X / 2) * (t - 1 / X) ^ (2 : ℕ)))
      ≤ ∫ t : ℝ, Real.exp (-X) * Real.exp (1 / (2 * X))
          * Real.exp (-(X / 2) * (t - 1 / X) ^ (2 : ℕ)) := by
    refine setIntegral_le_integral ((integrable_exp_quadratic hXpos).const_mul _) ?_
    filter_upwards with t
    positivity
  refine le_trans hfull (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_quadratic hXpos]

/-! ## The exterior cone geometry -/

/-- **Lemma 17.1, first half.**  Outside the light cone the principal root has real part at least
the spacelike separation. -/
theorem sqrt_le_csqrtRe {σ u h : ℝ} (hσ : 0 < σ) (hu : 0 ≤ u) (huh : u ≤ h) :
    Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ) + σ ^ (2 : ℕ))
      ≤ csqrtRe (((σ : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)) := by
  have hre : ((((σ : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ))).re
      = σ ^ (2 : ℕ) - u ^ (2 : ℕ) + h ^ (2 : ℕ) := by
    simp [Complex.add_re, Complex.mul_re, pow_two]
  have hA : 0 < σ ^ (2 : ℕ) - u ^ (2 : ℕ) + h ^ (2 : ℕ) := by nlinarith
  have hrepos : 0 < ((((σ : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ))).re := by
    rw [hre]; exact hA
  have hsq := sq_csqrtRe hrepos
  have hnorm := re_le_norm ((((σ : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)))
  rw [hre] at hnorm
  have hbound : h ^ (2 : ℕ) - u ^ (2 : ℕ) + σ ^ (2 : ℕ)
      ≤ csqrtRe (((σ : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [hsq, hre]
    linarith
  have hnn : 0 ≤ csqrtRe (((σ : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)) :=
    csqrtRe_nonneg _
  calc Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ) + σ ^ (2 : ℕ))
      ≤ Real.sqrt (csqrtRe (((σ : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hbound
    _ = csqrtRe (((σ : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)) := Real.sqrt_sq hnn

/-- **Lemma 17.1, second half.**  Outside a fixed cone `h ≥ κu` the ratio of the rapidity to the
principal root is bounded by a constant depending only on `σ` and `κ`. -/
theorem normSq_ratio_le {σ u h κ : ℝ} (hu : 0 ≤ u) (hκ : 1 < κ)
    (huh : κ * u ≤ h) :
    σ ^ (2 : ℕ) + u ^ (2 : ℕ) ≤ max 1 (1 / (κ ^ (2 : ℕ) - 1)) * (σ ^ (2 : ℕ) + h ^ (2 : ℕ) - u ^ (2 : ℕ)) := by
  have hκ2 : 0 < κ ^ (2 : ℕ) - 1 := by nlinarith
  have hκ0 : (0 : ℝ) < κ := lt_trans zero_lt_one hκ
  have hku : 0 ≤ κ * u := mul_nonneg hκ0.le hu
  have hh : κ ^ (2 : ℕ) * u ^ (2 : ℕ) ≤ h ^ (2 : ℕ) := by nlinarith [hku, huh]
  have hlow : σ ^ (2 : ℕ) + (κ ^ (2 : ℕ) - 1) * u ^ (2 : ℕ) ≤ σ ^ (2 : ℕ) + h ^ (2 : ℕ) - u ^ (2 : ℕ) := by nlinarith
  have hone : (1 : ℝ) ≤ max 1 (1 / (κ ^ (2 : ℕ) - 1)) := le_max_left _ _
  have hinv : 1 / (κ ^ (2 : ℕ) - 1) ≤ max 1 (1 / (κ ^ (2 : ℕ) - 1)) := le_max_right _ _
  have hkey : σ ^ (2 : ℕ) + u ^ (2 : ℕ) ≤ max 1 (1 / (κ ^ (2 : ℕ) - 1)) * (σ ^ (2 : ℕ) + (κ ^ (2 : ℕ) - 1) * u ^ (2 : ℕ)) := by
    have h1 : σ ^ (2 : ℕ) ≤ max 1 (1 / (κ ^ (2 : ℕ) - 1)) * σ ^ (2 : ℕ) := by nlinarith [sq_nonneg σ]
    have h2 : u ^ (2 : ℕ) ≤ max 1 (1 / (κ ^ (2 : ℕ) - 1)) * ((κ ^ (2 : ℕ) - 1) * u ^ (2 : ℕ)) := by
      have hmul : 1 / (κ ^ (2 : ℕ) - 1) * ((κ ^ (2 : ℕ) - 1) * u ^ (2 : ℕ)) = u ^ (2 : ℕ) := by
        field_simp
      nlinarith [sq_nonneg u, mul_nonneg (le_of_lt hκ2) (sq_nonneg u)]
    linarith
  have hmax : 0 ≤ max 1 (1 / (κ ^ (2 : ℕ) - 1)) := le_trans zero_le_one hone
  nlinarith [hkey, hlow, hmax]

end HTGeometry
