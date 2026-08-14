import GaloisForLFunctions.RHTower.GammaVerticalRatioAsymptotic

/-!
# The vertical Gamma-ratio law with an explicit, parameter-uniform error

The log of the vertical Gamma ratio `‖Γ(a+iτ)‖/‖Γ((a+δ)+iτ)‖` compensates `-δ log τ` with an error
that is explicitly

```text
δ (1/τ² + π/(2τ) + (a+δ)²/(2τ²)),
```

because the log-difference is `∫_a^{a+δ}(log τ - Re ψ(x+iτ))dx` and the integrand carries the sharp
vertical digamma bound.  The error depends on the parameters only through `a+δ`, so it is uniform on
every parameter box, and exponentiating gives a **two-sided** bound

```text
c τ^{-δ} ≤ ‖Γ(a+iτ)‖/‖Γ((a+δ)+iτ)‖ ≤ C τ^{-δ},   τ ≥ 1,
```

with constants depending only on the box.  The Beta-integral method gives only the upper half,
because it needs a positive real part in the second Beta argument; the lower half is what controls
the *inverse* Gamma transport.
-/

open Complex Filter Topology intervalIntegral MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **Quantitative vertical Gamma-ratio law.**  The compensation error is explicit and depends on
the parameters only through `a + δ`. -/
theorem abs_gamma_vertical_ratio_log_le {a δ τ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hτ : 0 < τ) :
    |(Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
        - Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖) + δ * Real.log τ|
      ≤ δ * (1 / τ ^ 2 + Real.pi / (2 * τ) + (1 / 2) * ((a + δ) ^ 2 / τ ^ 2)) := by
  set M : ℝ := (a + δ) ^ 2 with hM
  set E : ℝ := (1 / τ ^ 2 + Real.pi / (2 * τ)) + (1 / 2) * (M / τ ^ 2) with hEdef
  have hFTC := _root_.RHTower.integral_re_digamma_vertical (a := a) (δ := δ) hτ
  have hconstint : ∫ _x in a..(a + δ), Real.log τ = δ * Real.log τ := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hsub : ∫ x in a..(a + δ),
      (Real.log τ - (Complex.digamma ((x : ℂ) + (τ : ℂ) * Complex.I)).re)
      = δ * Real.log τ - (Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
        - Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖) := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((_root_.RHTower.continuous_re_digamma_line hτ).intervalIntegrable _ _), hconstint, hFTC]
  have hgoaleq : (Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
      - Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖) + δ * Real.log τ
      = ∫ x in a..(a + δ),
        (Real.log τ - (Complex.digamma ((x : ℂ) + (τ : ℂ) * Complex.I)).re) := by
    rw [hsub]; ring
  rw [hgoaleq, ← Real.norm_eq_abs]
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := E) ?_) ?_
  · intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx0 : (0 : ℝ) ≤ x := le_trans ha (le_of_lt hx.1)
    have hxle : x ≤ a + δ := hx.2
    have hbnd := _root_.RHTower.re_digamma_vertical_bound_uncond hx0 hτ
    have hfac : x ^ 2 + τ ^ 2 = (1 + x ^ 2 / τ ^ 2) * τ ^ 2 := by field_simp; ring
    have hlog_gap : (1 / 2) * Real.log (x ^ 2 + τ ^ 2) - Real.log τ
        = (1 / 2) * Real.log (1 + x ^ 2 / τ ^ 2) := by
      rw [hfac, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hlt : Real.log τ = (2 : ℝ)⁻¹ * (2 * Real.log τ) := by ring
      rw [hlt]; push_cast; ring
    have hgap_le : (1 / 2) * Real.log (1 + x ^ 2 / τ ^ 2) ≤ (1 / 2) * (M / τ ^ 2) := by
      have hle1 : Real.log (1 + x ^ 2 / τ ^ 2) ≤ x ^ 2 / τ ^ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + x ^ 2 / τ ^ 2 by positivity)
        linarith
      have hxM : x ^ 2 / τ ^ 2 ≤ M / τ ^ 2 := by
        rw [hM]
        gcongr
      linarith [hle1, hxM]
    have hgap_nonneg : 0 ≤ (1 / 2) * Real.log (1 + x ^ 2 / τ ^ 2) := by
      have := Real.log_nonneg (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ x ^ 2 / τ ^ 2))
      linarith
    rw [Real.norm_eq_abs, abs_le, hEdef]
    constructor <;>
      nlinarith [(abs_le.mp hbnd).1, (abs_le.mp hbnd).2, hlog_gap, hgap_le, hgap_nonneg]
  · rw [show a + δ - a = δ from by ring, abs_of_nonneg hδ, hEdef, hM]
    exact le_of_eq (by ring)

/-- **Two-sided vertical Gamma-ratio bound, uniform on a parameter box.**  Above height one the
ratio is trapped between two fixed multiples of `τ^{-δ}`. -/
theorem exists_twoSided_gamma_vertical_ratio {a₁ δ₁ : ℝ} (ha₁ : 0 ≤ a₁) (hδ₁ : 0 ≤ δ₁) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a δ τ : ℝ, 0 ≤ a → a ≤ a₁ → 0 ≤ δ → δ ≤ δ₁ → 1 ≤ τ →
      c * τ ^ (-δ)
          ≤ ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
            / ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ∧
        ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
            / ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
          ≤ C * τ ^ (-δ) := by
  set R : ℝ := δ₁ * (1 + Real.pi / 2 + (1 / 2) * (a₁ + δ₁) ^ 2) with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    have : (0 : ℝ) ≤ 1 + Real.pi / 2 + (1 / 2) * (a₁ + δ₁) ^ 2 := by positivity
    exact mul_nonneg hδ₁ this
  refine ⟨Real.exp (-R), Real.exp R, Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro a δ τ ha haa hδ hδd hτ
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le zero_lt_one hτ
  have hnum : 0 < ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hτ0 a)
  have hden : 0 < ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hτ0 (a + δ))
  set L : ℝ := Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
    - Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ with hLdef
  have hratio : ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
      / ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ = Real.exp L := by
    rw [hLdef, Real.exp_sub, Real.exp_log hnum, Real.exp_log hden]
  have hpow : τ ^ (-δ) = Real.exp (-(δ * Real.log τ)) := by
    rw [Real.rpow_def_of_pos hτ0]
    congr 1
    ring
  have hquant := abs_gamma_vertical_ratio_log_le ha hδ hτ0
  rw [← hLdef] at hquant
  have herr : δ * (1 / τ ^ 2 + Real.pi / (2 * τ) + (1 / 2) * ((a + δ) ^ 2 / τ ^ 2)) ≤ R := by
    have h1 : 1 / τ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hτ]
    have h2 : Real.pi / (2 * τ) ≤ Real.pi / 2 := by
      refine div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) ?_
      linarith
    have h3 : (1 / 2) * ((a + δ) ^ 2 / τ ^ 2) ≤ (1 / 2) * (a₁ + δ₁) ^ 2 := by
      have hsq : (a + δ) ^ 2 ≤ (a₁ + δ₁) ^ 2 := by nlinarith
      have hτ2 : (1 : ℝ) ≤ τ ^ 2 := by nlinarith [hτ]
      have hdiv : (a + δ) ^ 2 / τ ^ 2 ≤ (a₁ + δ₁) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hsq, sq_nonneg (a₁ + δ₁), hτ2]
      linarith
    rw [hRdef]
    have hnn : (0 : ℝ) ≤ 1 + Real.pi / 2 + (1 / 2) * (a₁ + δ₁) ^ 2 := by positivity
    calc δ * (1 / τ ^ 2 + Real.pi / (2 * τ) + (1 / 2) * ((a + δ) ^ 2 / τ ^ 2))
        ≤ δ * (1 + Real.pi / 2 + (1 / 2) * (a₁ + δ₁) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hδ
          linarith
      _ ≤ δ₁ * (1 + Real.pi / 2 + (1 / 2) * (a₁ + δ₁) ^ 2) :=
          mul_le_mul_of_nonneg_right hδd hnn
  have hLbounds : -(δ * Real.log τ) - R ≤ L ∧ L ≤ -(δ * Real.log τ) + R := by
    have := abs_le.mp hquant
    constructor <;> linarith [this.1, this.2]
  rw [hratio, hpow]
  constructor
  · rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hLbounds.1])
  · rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hLbounds.2])

end GaloisForLFunctions.RHTower
