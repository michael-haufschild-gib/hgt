import GaloisForLFunctions.RHTower.DigammaVerticalLogAsymptotic
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE

/-!
# Vertical Gamma-ratio magnitude asymptotic

The magnitude of the vertical Gamma-ratio `‖Γ(a+iτ)/Γ((a+δ)+iτ)‖` decays exactly like `τ^{-δ}`:

`log‖Γ(a+iτ)‖ − log‖Γ((a+δ)+iτ)‖ + δ log τ → 0`  as  `τ → ∞`,  for  `a ≥ 0, δ ≥ 0`.

The real-part offset `a` (equivalently the Gauss-component index `k = m·a`) drops out entirely.  This
is the archimedean magnitude law behind the Gauss-component quasi-inner defect: with
`ρ_{m,k}(it) = (π/m)^{1/2m − it/m}·Γ(it/(2m)+k/m)/Γ((1−it)/(2m)+k/m)` one has
`|ρ_{m,k}(it)| = (2π/|t|)^{1/2m}(1+o(1))`, independent of `k`, and hence the singular values
`|d_n|^{2m} = L/|n|(1+o(1))` feeding the critical weak-Schatten residue.

Proof: the log-difference equals `∫_a^{a+δ} (log τ − Re ψ(x+iτ)) dx` by the fundamental theorem
(`hasDerivAt_log_norm_Gamma`), and the integrand is uniformly `O(1/τ)` on `[a,a+δ]` from the sharp
digamma vertical bound.
-/

open Complex Filter Topology intervalIntegral MeasureTheory

namespace RHTower

theorem gammaArg_ne_neg_nat {τ : ℝ} (hτ : 0 < τ) (x : ℝ) (m : ℕ) :
    (x : ℂ) + (τ : ℂ) * Complex.I ≠ -(m : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp [Complex.add_im, Complex.mul_im] at him
  linarith

theorem gammaArg_Gamma_ne_zero {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    Complex.Gamma ((x : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 :=
  Complex.Gamma_ne_zero (fun m => gammaArg_ne_neg_nat hτ x m)

theorem continuous_re_digamma_line {τ : ℝ} (hτ : 0 < τ) :
    Continuous (fun x : ℝ => (Complex.digamma ((x : ℂ) + (τ : ℂ) * Complex.I)).re) := by
  have hline : Continuous (fun x : ℝ => (x : ℂ) + (τ : ℂ) * Complex.I) := by
    exact (Complex.continuous_ofReal.add continuous_const)
  refine Complex.continuous_re.comp ?_
  rw [continuous_iff_continuousAt]
  intro x
  have hf : ContinuousAt (fun x : ℝ => (x : ℂ) + (τ : ℂ) * Complex.I) x := hline.continuousAt
  exact ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (τ : ℂ) * Complex.I)
    (GaloisForLFunctions.continuousAt_digamma ((x : ℂ) + (τ : ℂ) * Complex.I)
      (gammaArg_ne_neg_nat hτ x)) hf

theorem integral_re_digamma_vertical {a δ τ : ℝ} (hτ : 0 < τ) :
    ∫ x in a..(a + δ), (Complex.digamma ((x : ℂ) + (τ : ℂ) * Complex.I)).re
      = Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
        - Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖ := by
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + (τ : ℂ) * Complex.I)‖)
    (f' := fun x : ℝ => (Complex.digamma ((x : ℂ) + (τ : ℂ) * Complex.I)).re)
    (a := a) (b := a + δ)
    (fun x _ => hasDerivAt_log_norm_Gamma τ x (gammaArg_ne_neg_nat hτ x)
      (gammaArg_Gamma_ne_zero hτ x))
    ((continuous_re_digamma_line hτ).intervalIntegrable _ _)
  exact key

/-- **Gauss-component vertical magnitude law.**  For `a ≥ 0`, `δ ≥ 0`, the log of the vertical
Gamma-ratio `‖Γ(a+iτ)/Γ((a+δ)+iτ)‖` compensates exactly `−δ log τ`:
`log‖Γ(a+iτ)‖ − log‖Γ((a+δ)+iτ)‖ + δ log τ → 0`.  The real-part offset `a` (hence the Gauss index)
drops out.  Proof: the difference equals `∫_a^{a+δ}(log τ − Re ψ(x+iτ)) dx` by the fundamental
theorem, and the integrand is uniformly `O(1/τ)` on the bounded interval. -/
theorem gamma_vertical_ratio_log_tendsto {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    Tendsto (fun τ : ℝ =>
      (Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
        - Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖) + δ * Real.log τ)
      atTop (nhds 0) := by
  set M : ℝ := (a + δ) ^ 2 with hM
  set E : ℝ → ℝ := fun τ : ℝ => (1 / τ ^ 2 + Real.pi / (2 * τ)) + (1 / 2) * (M / τ ^ 2) with hEdef
  -- E τ → 0
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hd : Tendsto (fun t : ℝ => 1 / t) atTop (nhds 0) := by simpa [one_div] using hinv
  have h1 : Tendsto (fun t : ℝ => 1 / t ^ 2) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun t => by positivity)) ?_ hd
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact one_div_le_one_div_of_le (by linarith) (by nlinarith [ht])
  have h2 : Tendsto (fun t : ℝ => Real.pi / (2 * t)) atTop (nhds 0) := by
    have hcont : Continuous (fun x : ℝ => Real.pi / 2 * x) := continuous_const.mul continuous_id
    have hcomp := hcont.continuousAt.tendsto.comp hinv
    simp only [mul_zero, Function.comp_def] at hcomp
    refine hcomp.congr (fun t => ?_)
    rcases eq_or_ne t 0 with h | h
    · simp [h]
    · field_simp
  have hE : Tendsto E atTop (nhds 0) := by
    have h3 : Tendsto (fun t : ℝ => (1 / 2) * (M / t ^ 2)) atTop (nhds 0) := by
      have hh := h1.const_mul ((1 / 2) * M)
      simp only [mul_zero] at hh
      refine hh.congr (fun t => ?_)
      rw [mul_one_div, mul_div_assoc]
    simpa [hEdef] using (h1.add h2).add h3
  -- squeeze the goal by δ * E τ
  apply squeeze_zero_norm' ?_ (by simpa using hE.mul_const δ)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)] with τ hτ hτ1
  -- rewrite the goal expression as the integral
  have hτ2 : (0:ℝ) < τ ^ 2 := by positivity
  have hFTC := integral_re_digamma_vertical (a := a) (δ := δ) hτ
  have hconstint : ∫ _x in a..(a + δ), Real.log τ = δ * Real.log τ := by
    rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  have hsub : ∫ x in a..(a + δ),
      (Real.log τ - (Complex.digamma ((x : ℂ) + (τ : ℂ) * Complex.I)).re)
      = δ * Real.log τ - (Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
        - Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖) := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((continuous_re_digamma_line hτ).intervalIntegrable _ _), hconstint, hFTC]
  have hgoaleq : (Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
      - Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖) + δ * Real.log τ
      = ∫ x in a..(a + δ),
        (Real.log τ - (Complex.digamma ((x : ℂ) + (τ : ℂ) * Complex.I)).re) := by
    rw [hsub]; ring
  rw [Real.norm_eq_abs, hgoaleq]
  -- bound the integral by E τ * δ
  rw [← Real.norm_eq_abs]
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := E τ) ?_) ?_
  · intro x hx
    have hτne : τ ≠ 0 := ne_of_gt hτ
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx0 : (0:ℝ) ≤ x := le_trans ha (le_of_lt hx.1)
    have hxle : x ≤ a + δ := hx.2
    have hbnd := re_digamma_vertical_bound_uncond hx0 hτ
    have hfac : x ^ 2 + τ ^ 2 = (1 + x ^ 2 / τ ^ 2) * τ ^ 2 := by field_simp; ring
    have hlog_gap : (1 / 2) * Real.log (x ^ 2 + τ ^ 2) - Real.log τ
        = (1 / 2) * Real.log (1 + x ^ 2 / τ ^ 2) := by
      rw [hfac, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hlt : Real.log τ = (2 : ℝ)⁻¹ * (2 * Real.log τ) := by ring
      rw [hlt]; push_cast; ring
    have hgap_le : (1 / 2) * Real.log (1 + x ^ 2 / τ ^ 2) ≤ (1 / 2) * (M / τ ^ 2) := by
      have hle1 : Real.log (1 + x ^ 2 / τ ^ 2) ≤ x ^ 2 / τ ^ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + x ^ 2 / τ ^ 2 by positivity)
        linarith
      have hxM : x ^ 2 / τ ^ 2 ≤ M / τ ^ 2 := by rw [hM]; gcongr
      linarith [hle1, hxM]
    have hgap_nonneg : 0 ≤ (1 / 2) * Real.log (1 + x ^ 2 / τ ^ 2) := by
      have := Real.log_nonneg (le_add_of_nonneg_right (by positivity : (0:ℝ) ≤ x ^ 2 / τ ^ 2))
      linarith
    rw [Real.norm_eq_abs, abs_le, hEdef]
    simp only
    constructor <;>
      nlinarith [(abs_le.mp hbnd).1, (abs_le.mp hbnd).2, hlog_gap, hgap_le, hgap_nonneg]
  · exact le_of_eq (by rw [show a + δ - a = δ from by ring, abs_of_nonneg hδ, mul_comm])


theorem norm_Gamma_conj (z : ℂ) : ‖Complex.Gamma (starRingEnd ℂ z)‖ = ‖Complex.Gamma z‖ := by
  rw [Complex.Gamma_conj, norm_conj]

/-- Conjugate-denominator form of the vertical Gamma-ratio law, matching the denominator
`Γ((a+δ) − iτ)` appearing in a Gauss-component quasi-inner factor. -/
theorem gamma_vertical_ratio_conj_log_tendsto {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    Tendsto (fun τ : ℝ =>
      (Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
        - Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) - (τ : ℂ) * Complex.I)‖) + δ * Real.log τ)
      atTop (nhds 0) := by
  refine (gamma_vertical_ratio_log_tendsto ha hδ).congr (fun τ => ?_)
  have hconj : ((a + δ : ℝ) : ℂ) - (τ : ℂ) * Complex.I
      = starRingEnd ℂ (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I) := by
    simp [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj, norm_Gamma_conj]

/-- Multiplicative form: `(‖Γ(a+iτ)‖/‖Γ((a+δ)+iτ)‖)·τ^δ → 1` — the directly-usable magnitude
ratio behind `|ρ|=(2π/|t|)^{1/2m}`. -/
theorem gamma_vertical_ratio_norm_rpow_tendsto {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    Tendsto (fun τ : ℝ =>
      (Real.exp (Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
        - Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖)) * τ ^ δ)
      atTop (nhds 1) := by
  have hmain := gamma_vertical_ratio_log_tendsto ha hδ
  have hexp : Tendsto (fun τ : ℝ =>
      Real.exp ((Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
        - Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖) + δ * Real.log τ))
      atTop (nhds 1) := by
    have := (Real.continuous_exp.continuousAt (x := 0)).tendsto.comp hmain
    simpa using! this
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  rw [Real.exp_add, Real.rpow_def_of_pos hτ]
  ring_nf

end RHTower
