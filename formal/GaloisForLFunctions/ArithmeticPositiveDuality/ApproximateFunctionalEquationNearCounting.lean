import GaloisForLFunctions.ArithmeticPositiveDuality.ApproximateFunctionalEquationNearIntegers

/-!
# Quantitative Hamburger stability: the weights

`ApproximateFunctionalEquationNearIntegers` bounds the off-lattice mass of a nonnegative measure `ν`
on `[1, ∞)` whose functional equation fails on the critical line by `Γ_ℝ(s) g(Im s / 2)`:
`∫ sinc²(π u) dν(u) ≤ (6/π) ‖g‖₁`. This module bounds the weights: every unit tent mass of `ν`
is within `O(‖g‖₁)` of the constant `2 Re β` forced by the pole.

**Theorem** (`abs_integral_unitTent_sub_le_of_critical_line_defect`). Under the hypotheses of
`integral_sinc_sq_le_of_critical_line_defect`, for every real `n ≥ 1`,

`|∫ (1 - |u - n|)⁺ dν(u) - 2 Re β| ≤ (18/π + 4κ/π²) ‖g‖₁`, `κ = 4^{-1/4} π^{-1/4} Γ(1/4)`.

Since the unit tents form a partition of unity, `ν` is within `O(‖g‖₁)` of `2 Re β · Σ_{k ≥ 1} δ_k`
at every height, in addition to lying within `O(‖g‖₁)` of integer support.

**Proof.** Pair the defective Laplace identity `L_ν = F_ν - β/(πt) + β + J` on `t = ε + i(n + s)`
with the window `1 - |s|` on `[-1, 1]`, and let `ε → 0⁺`.
* Series side: `Re L_ν(t) = (1/2π) ∫ (P_ε(n + s - u) + P_ε(n + s + u)) dν(u)` with the Poisson
  kernel `P_ε(x) = ε/(ε² + x²)`; Poisson smoothing of the tent turns it into `(1/2) ∫ tent_n dν`.
* Dual side: the window maps `Re e^{-2πut}` to `e^{-2πuε} cos(2πun) sinc²(πu)`, so the dual side is
  at most the off-lattice mass.
* Polar side: `Re β - Re β · (Poisson mass at -n) - (Im β/π) q_ε` with `0 ≤ q_ε ≤ 2`.
* Defect side: `‖J(t)‖ ≤ (3/2π) ‖t‖^{-1/2} ‖g‖₁` and `(1 - |s|)² ≤ ‖t‖` give `(3/π) ‖g‖₁`.
* `Im β = 2 Im K(4)` from the theta law at `x = 4`, and `‖K(4)‖ ≤ (κ/2π) ‖g‖₁`.
-/

open Complex MeasureTheory Filter Topology Set Function
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open GaloisForLFunctions.HTGeometry

/-! ## 1. The unit tent -/

/-- The unit tent `(1 - |u - n|)⁺` at `n`. -/
def unitTent (n u : ℝ) : ℝ := max 0 (1 - |u - n|)

theorem continuous_unitTent (n : ℝ) : Continuous (unitTent n) := by
  unfold unitTent; fun_prop

theorem unitTent_nonneg (n u : ℝ) : 0 ≤ unitTent n u := le_max_left _ _

theorem unitTent_le_one (n u : ℝ) : unitTent n u ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg (u - n)])

theorem unitTent_eq_zero {n u : ℝ} (h : 1 ≤ |u - n|) : unitTent n u = 0 :=
  max_eq_left (by linarith)

theorem unitTent_zero_sub (n u : ℝ) : unitTent 0 (u - n) = unitTent n u := by
  simp only [unitTent, sub_zero]

/-- `∫_{-1}^{1} (1 - |s|) f(s) ds = ∫ tent₀(s) f(s) ds`. -/
theorem intervalIntegral_window_eq_integral_unitTent (f : ℝ → ℝ) :
    ∫ s in (-1 : ℝ)..1, (1 - |s|) * f s = ∫ s, unitTent 0 s * f s := by
  have hzero : ∀ s ∉ Ioc (-1 : ℝ) 1, unitTent 0 s * f s = 0 := by
    intro s hs
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
    rw [unitTent_eq_zero, zero_mul]
    rw [sub_zero]
    rcases hs with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
  simp only [unitTent, sub_zero]
  rw [max_eq_right (by linarith [abs_le.mpr ⟨hs.1, hs.2⟩])]

/-! ## 2. Poisson smoothing -/

/-- `∫ K(τ) ε/(ε² + (τ - u)²) dτ = ∫ K(u + εs)/(1 + s²) ds` for `ε > 0`. -/
theorem integral_mul_poisson_eq (K : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    ∫ τ, K τ * (ε / (ε ^ 2 + (τ - u) ^ 2)) = ∫ s, K (u + ε * s) * (1 + s ^ 2)⁻¹ := by
  have h1 : (fun s => K (u + ε * s) * (1 + s ^ 2)⁻¹) =
      fun s => (fun y => K (u + y) * (ε / (ε ^ 2 + y ^ 2)) * ε) (ε * s) := by
    funext s
    have hd : ε ^ 2 + (ε * s) ^ 2 = ε ^ 2 * (1 + s ^ 2) := by ring
    simp only
    rw [hd]
    field_simp
  rw [h1, Measure.integral_comp_mul_left (fun y => K (u + y) * (ε / (ε ^ 2 + y ^ 2)) * ε) ε,
    abs_inv, abs_of_pos hε, smul_eq_mul, integral_mul_const,
    ← integral_add_left_eq_self (fun τ => K τ * (ε / (ε ^ 2 + (τ - u) ^ 2))) u]
  simp only [add_sub_cancel_left]
  generalize (∫ x : ℝ, K (u + x) * (ε / (ε ^ 2 + x ^ 2))) = J
  field_simp

theorem poissonSmoothing_le_one {K : ℝ → ℝ} (hK0 : ∀ x, 0 ≤ K x) (hK1 : ∀ x, K x ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    (1 / Real.pi) * ∫ τ, K τ * (ε / (ε ^ 2 + (τ - u) ^ 2)) ≤ 1 := by
  rw [integral_mul_poisson_eq K hε u]
  have h : (∫ s, K (u + ε * s) * (1 + s ^ 2)⁻¹) ≤ ∫ s : ℝ, (1 + s ^ 2)⁻¹ := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => ?_) integrable_inv_one_add_sq
      (Eventually.of_forall fun s => ?_)
    · exact mul_nonneg (hK0 _) (by positivity)
    · exact mul_le_of_le_one_left (by positivity) (hK1 _)
  rw [integral_univ_inv_one_add_sq] at h
  rw [div_mul_eq_mul_div, one_mul, div_le_one Real.pi_pos]
  exact h

/-- **Poisson smoothing.** For continuous `K` with `0 ≤ K ≤ 1`,
`(1/π) ∫ K(τ) P_ε(τ - u) dτ → K(u)` as `ε → 0⁺`. -/
theorem tendsto_poissonSmoothing {K : ℝ → ℝ} (hK : Continuous K) (hK0 : ∀ x, 0 ≤ K x)
    (hK1 : ∀ x, K x ≤ 1) (u : ℝ) :
    Tendsto (fun ε => (1 / Real.pi) * ∫ τ, K τ * (ε / (ε ^ 2 + (τ - u) ^ 2)))
      (𝓝[>] 0) (𝓝 (K u)) := by
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 / Real.pi) * ∫ s, K (u + ε * s) * (1 + s ^ 2)⁻¹ =
      (1 / Real.pi) * ∫ τ, K τ * (ε / (ε ^ 2 + (τ - u) ^ 2)) :=
    eventually_nhdsWithin_of_forall fun ε hε => by rw [integral_mul_poisson_eq K hε u]
  refine Tendsto.congr' heq ?_
  have hlim : Tendsto (fun ε => ∫ s, K (u + ε * s) * (1 + s ^ 2)⁻¹) (𝓝[>] 0)
      (𝓝 (∫ s : ℝ, K u * (1 + s ^ 2)⁻¹)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => (1 + s ^ 2)⁻¹)
      (Eventually.of_forall fun ε => (show Continuous fun s : ℝ =>
        K (u + ε * s) * (1 + s ^ 2)⁻¹ from (hK.comp (by fun_prop : Continuous fun s : ℝ =>
          u + ε * s)).mul ((by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2).inv₀
            fun s => by positivity)).aestronglyMeasurable)
      (Eventually.of_forall fun ε => Eventually.of_forall fun s => ?_)
      integrable_inv_one_add_sq (Eventually.of_forall fun s => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK0 _) (by positivity))]
      exact mul_le_of_le_one_left (by positivity) (hK1 _)
    · have hc : Tendsto (fun ε : ℝ => u + ε * s) (𝓝[>] 0) (𝓝 (u + 0 * s)) :=
        ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0).mono_left
          nhdsWithin_le_nhds
      rw [zero_mul, add_zero] at hc
      exact ((hK.tendsto u).comp hc).mul_const _
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hlim
  have := hlim.const_mul (1 / Real.pi)
  rwa [show 1 / Real.pi * (K u * Real.pi) = K u by field_simp] at this

/-- The window Poisson mass `(1/π) ∫_{-1}^{1} (1 - |s|) P_ε(s - v) ds`. -/
def windowPoisson (ε v : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ s in (-1 : ℝ)..1, (1 - |s|) * (ε / (ε ^ 2 + (s - v) ^ 2))

theorem continuous_window_poisson {ε : ℝ} (hε : 0 < ε) (v : ℝ) :
    Continuous fun s : ℝ => (1 - |s|) * (ε / (ε ^ 2 + (s - v) ^ 2)) :=
  (continuous_const.sub continuous_abs).mul
    (continuous_const.div (by fun_prop) fun s => by positivity)

theorem windowPoisson_eq (ε v : ℝ) :
    windowPoisson ε v = (1 / Real.pi) * ∫ s, unitTent 0 s * (ε / (ε ^ 2 + (s - v) ^ 2)) := by
  rw [windowPoisson, intervalIntegral_window_eq_integral_unitTent]

theorem windowPoisson_nonneg {ε : ℝ} (hε : 0 < ε) (v : ℝ) : 0 ≤ windowPoisson ε v :=
  mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by norm_num) fun s hs =>
    mul_nonneg (by linarith [abs_le.mpr ⟨hs.1, hs.2⟩]) (by positivity))

theorem windowPoisson_le_one {ε : ℝ} (hε : 0 < ε) (v : ℝ) : windowPoisson ε v ≤ 1 := by
  rw [windowPoisson_eq]
  exact poissonSmoothing_le_one (unitTent_nonneg 0) (unitTent_le_one 0) hε v

theorem tendsto_windowPoisson (v : ℝ) :
    Tendsto (fun ε => windowPoisson ε v) (𝓝[>] 0) (𝓝 (unitTent 0 v)) := by
  simp_rw [windowPoisson_eq]
  exact tendsto_poissonSmoothing (continuous_unitTent 0) (unitTent_nonneg 0) (unitTent_le_one 0) v

/-- Far from the window, `windowPoisson ε v ≤ 4/v²` (`|v| ≥ 2`, `ε ≤ 1`). -/
theorem windowPoisson_le_of_two_le {ε v : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hv : 2 ≤ |v|) :
    windowPoisson ε v ≤ 4 / v ^ 2 := by
  have hpi := Real.pi_pos
  have hv2 : 0 < v ^ 2 := by
    have : v ≠ 0 := fun h => by rw [h, abs_zero] at hv; linarith
    positivity
  have hpt : ∀ s ∈ Icc (-1 : ℝ) 1,
      (1 - |s|) * (ε / (ε ^ 2 + (s - v) ^ 2)) ≤ (1 - |s|) * (4 / v ^ 2) := by
    intro s hs
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
    have hfar : |v| / 2 ≤ |s - v| := by
      have := abs_sub_abs_le_abs_sub v s
      rw [abs_sub_comm v s] at this
      linarith
    have hsq : v ^ 2 / 4 ≤ (s - v) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hfar 2
      rw [div_pow, sq_abs, sq_abs] at h
      linarith
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [div_le_div_iff₀ (by positivity) hv2]
    nlinarith [sq_nonneg ε]
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
    ((continuous_window_poisson hε0 v).intervalIntegrable (μ := volume) _ _)
    ((show Continuous fun s : ℝ => (1 - |s|) * (4 / v ^ 2) by fun_prop).intervalIntegrable
      (μ := volume) _ _) hpt
  rw [intervalIntegral.integral_mul_const, fejer_triangle_integral_one, one_mul] at hmono
  unfold windowPoisson
  calc (1 / Real.pi) * ∫ s in (-1 : ℝ)..1, (1 - |s|) * (ε / (ε ^ 2 + (s - v) ^ 2))
      ≤ 1 * (4 / v ^ 2) :=
        mul_le_mul (by rw [div_le_one hpi]; linarith [Real.pi_gt_three]) hmono
          (intervalIntegral.integral_nonneg (by norm_num) fun s hs =>
            mul_nonneg (by linarith [abs_le.mpr ⟨hs.1, hs.2⟩]) (by positivity)) zero_le_one
    _ = 4 / v ^ 2 := one_mul _

/-! ## 3. Kernels on `t = ε + i(n + s)` -/

/-- Window-weighted real part `(1 - |s|) Re[t/(π(u² + t²))]` at `t = ε + i(n + s)`. -/
def tentSeriesKernel (n ε s u : ℝ) : ℝ :=
  (1 - |s|) * ((((ε : ℂ) + ((n + s : ℝ) : ℂ) * I) /
    ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I) ^ 2)))).re

/-- Window-weighted real part `(1 - |s|) Re e^{-2πut}` at `t = ε + i(n + s)`. -/
def tentDualKernel (n ε s u : ℝ) : ℝ :=
  (1 - |s|) * (cexp (-(2 * Real.pi * (u : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)))).re

/-- Window-weighted real part `(1 - |s|) Re(-β/(πt) + β)` at `t = ε + i(n + s)`. -/
def tentPolarKernel (β : ℂ) (n ε s : ℝ) : ℝ :=
  (1 - |s|) * (-β / ((Real.pi : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)) + β).re

/-- Window-weighted real part `(1 - |s|) Re J(t)` at `t = ε + i(n + s)`. -/
def tentDefectKernel (g : ℝ → ℂ) (n ε s : ℝ) : ℝ :=
  (1 - |s|) * (RHTower.HamburgerStability.defectLaplace g
    ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)).re

/-- The series kernel is a window-weighted pair of Poisson kernels centred at `s = u - n` and
`s = -u - n`. -/
theorem tentSeriesKernel_eq {ε : ℝ} (hε : 0 < ε) (n s u : ℝ) :
    tentSeriesKernel n ε s u = (1 / 2) * ((1 / Real.pi) * ((1 - |s|) *
      (ε / (ε ^ 2 + (s - (u - n)) ^ 2))) + (1 / Real.pi) * ((1 - |s|) *
        (ε / (ε ^ 2 + (s - (-u - n)) ^ 2)))) := by
  have h := two_re_series_term_eq (u := u) (τ := n + s) hε
  have e1 : n + s - u = s - (u - n) := by ring
  have e2 : n + s + u = s - (-u - n) := by ring
  rw [e1, e2] at h
  unfold tentSeriesKernel
  linear_combination (1 - |s|) / 2 * h

theorem tentSeriesKernel_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℝ) {s : ℝ} (hs : |s| ≤ 1) (u : ℝ) :
    0 ≤ tentSeriesKernel n ε s u := by
  rw [tentSeriesKernel_eq hε]
  have : 0 ≤ 1 - |s| := by linarith
  positivity

theorem intervalIntegral_tentSeriesKernel {ε : ℝ} (hε : 0 < ε) (n u : ℝ) :
    ∫ s in (-1 : ℝ)..1, tentSeriesKernel n ε s u =
      (1 / 2) * (windowPoisson ε (u - n) + windowPoisson ε (-u - n)) := by
  have hi : ∀ v, IntervalIntegrable
      (fun s : ℝ => (1 / Real.pi) * ((1 - |s|) * (ε / (ε ^ 2 + (s - v) ^ 2)))) volume (-1) 1 :=
    fun v => ((continuous_window_poisson hε v).intervalIntegrable _ _).const_mul _
  rw [intervalIntegral.integral_congr fun s _ => tentSeriesKernel_eq hε n s u,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi _) (hi _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rfl

private theorem poisson_le_inv_sq {ε x c : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c)
    (hx : c ≤ x ^ 2) : ε / (ε ^ 2 + x ^ 2) ≤ 1 / c := by
  rw [div_le_div_iff₀ (by positivity) hc]
  nlinarith [mul_le_mul_of_nonneg_right hε1 hc.le, sq_nonneg ε]

/-- Uniform-in-`ε` domination: `∫_{-1}^{1}` of the series kernel is at most `(n + 2)²/u²`. -/
theorem intervalIntegral_tentSeriesKernel_le {n ε u : ℝ} (hn : 1 ≤ n) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hu : 1 ≤ u) :
    ∫ s in (-1 : ℝ)..1, tentSeriesKernel n ε s u ≤ (n + 2) ^ 2 * (1 / u ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hu2 : 0 < u ^ 2 := by positivity
  rw [intervalIntegral_tentSeriesKernel hε0]
  have h1 : windowPoisson ε (u - n) ≤ (n + 2) ^ 2 * (1 / u ^ 2) := by
    rcases lt_or_ge u (n + 2) with hlt | hge
    · refine (windowPoisson_le_one hε0 _).trans ?_
      rw [mul_one_div, le_div_iff₀ hu2, one_mul]
      nlinarith
    · have habs : 2 ≤ |u - n| := by rw [abs_of_pos (by linarith)]; linarith
      refine (windowPoisson_le_of_two_le hε0 hε1 habs).trans ?_
      rw [mul_one_div, div_le_div_iff₀ (by nlinarith) hu2]
      have h2u : 2 * u ≤ (n + 2) * (u - n) := by nlinarith
      nlinarith
  have h2 : windowPoisson ε (-u - n) ≤ (n + 2) ^ 2 * (1 / u ^ 2) := by
    have habs : 2 ≤ |-u - n| := by rw [abs_of_neg (by linarith)]; linarith
    refine (windowPoisson_le_of_two_le hε0 hε1 habs).trans ?_
    rw [mul_one_div, div_le_div_iff₀ (by nlinarith) hu2]
    nlinarith [mul_le_mul (show (4 : ℝ) ≤ (n + 2) ^ 2 by nlinarith)
      (show u ^ 2 ≤ (-u - n) ^ 2 by nlinarith) (by positivity) (by positivity)]
  linarith

/-- Pointwise domination for Fubini at fixed `ε`. -/
private theorem poisson_le_window {n ε s u : ℝ} (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hs : |s| ≤ 1) (hu : 1 ≤ u) {v : ℝ} (hv : v = u - n ∨ v = -u - n) :
    ε / (ε ^ 2 + (s - v) ^ 2) ≤ 4 * (n + 1) ^ 2 / ε * (1 / u ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hu2 : 0 < u ^ 2 := by positivity
  have hs' := abs_le.mp hs
  have hK : 4 * (1 / u ^ 2) ≤ 4 * (n + 1) ^ 2 / ε * (1 / u ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [le_div_iff₀ hε0]; nlinarith
  rcases hv with rfl | rfl
  · rcases le_or_gt u (2 * (n + 1)) with hnear | hfar
    · have hP : ε / (ε ^ 2 + (s - (u - n)) ^ 2) ≤ 1 / ε := by
        rw [div_le_div_iff₀ (by positivity) hε0]; nlinarith [sq_nonneg (s - (u - n))]
      refine hP.trans ?_
      rw [show 4 * (n + 1) ^ 2 / ε * (1 / u ^ 2) = 1 / ε * (4 * (n + 1) ^ 2 / u ^ 2) by ring]
      refine le_mul_of_one_le_right (by positivity) ?_
      rw [one_le_div hu2]; nlinarith
    · have hsq : u ^ 2 / 4 ≤ (s - (u - n)) ^ 2 := by nlinarith
      refine (poisson_le_inv_sq hε0 hε1 (by positivity) hsq).trans ?_
      rw [one_div_div, ← mul_one_div]
      exact hK
  · have hsq : u ^ 2 ≤ (s - (-u - n)) ^ 2 := by nlinarith
    refine (poisson_le_inv_sq hε0 hε1 hu2 hsq).trans ?_
    linarith [show 0 ≤ 1 / u ^ 2 by positivity]

theorem abs_tentSeriesKernel_le {n ε s u : ℝ} (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hs : |s| ≤ 1) (hu : 1 ≤ u) :
    |tentSeriesKernel n ε s u| ≤ 4 * (n + 1) ^ 2 / (Real.pi * ε) * (1 / u ^ 2) := by
  have hpi := Real.pi_pos
  rw [abs_of_nonneg (tentSeriesKernel_nonneg hε0 n hs u), tentSeriesKernel_eq hε0]
  have hw0 : 0 ≤ 1 - |s| := by linarith
  have hw1 : 1 - |s| ≤ 1 := by linarith [abs_nonneg s]
  have h1 := poisson_le_window hn hε0 hε1 hs hu (v := u - n) (Or.inl rfl)
  have h2 := poisson_le_window hn hε0 hε1 hs hu (v := -u - n) (Or.inr rfl)
  set B : ℝ := 4 * (n + 1) ^ 2 / ε * (1 / u ^ 2)
  have hB : 0 ≤ B := by positivity
  have h1' : (1 - |s|) * (ε / (ε ^ 2 + (s - (u - n)) ^ 2)) ≤ B :=
    (mul_le_mul hw1 h1 (by positivity) zero_le_one).trans_eq (one_mul _)
  have h2' : (1 - |s|) * (ε / (ε ^ 2 + (s - (-u - n)) ^ 2)) ≤ B :=
    (mul_le_mul hw1 h2 (by positivity) zero_le_one).trans_eq (one_mul _)
  have e : 4 * (n + 1) ^ 2 / (Real.pi * ε) * (1 / u ^ 2) = (1 / 2) *
      ((1 / Real.pi) * B + (1 / Real.pi) * B) := by
    simp only [B]; field_simp; ring
  rw [e]
  gcongr

theorem measurable_uncurry_tentSeriesKernel (n ε : ℝ) :
    Measurable (uncurry (tentSeriesKernel n ε)) := by
  show Measurable fun p : ℝ × ℝ => (1 - |p.1|) * ((((ε : ℂ) + ((n + p.1 : ℝ) : ℂ) * I) /
    ((Real.pi : ℂ) * ((p.2 : ℂ) ^ 2 + ((ε : ℂ) + ((n + p.1 : ℝ) : ℂ) * I) ^ 2)))).re
  fun_prop

theorem continuous_uncurry_tentDualKernel (n ε : ℝ) :
    Continuous (uncurry (tentDualKernel n ε)) := by
  show Continuous fun p : ℝ × ℝ =>
    (1 - |p.1|) * (cexp (-(2 * Real.pi * (p.2 : ℂ) * ((ε : ℂ) + ((n + p.1 : ℝ) : ℂ) * I)))).re
  fun_prop

/-- The dual kernel is a damped window-weighted cosine. -/
theorem tentDualKernel_eq (n ε s u : ℝ) :
    tentDualKernel n ε s u = Real.exp (-2 * Real.pi * u * ε) *
      ((1 - |s|) * Real.cos (2 * Real.pi * u * (n + s))) := by
  have hexp : -(2 * (Real.pi : ℂ) * (u : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)) =
      ((-2 * Real.pi * u * ε : ℝ) : ℂ) + ((-(2 * Real.pi * u * (n + s)) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [tentDualKernel, hexp, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.re_ofReal_mul, add_re, ofReal_re, mul_re, ofReal_re, ofReal_im,
    I_re, I_im, Real.cos_neg]
  ring

theorem abs_tentDualKernel_le {n ε s u : ℝ} (hε : 0 < ε) (hs : |s| ≤ 1) (hu : 0 < u) :
    |tentDualKernel n ε s u| ≤ (1 / (2 * Real.pi ^ 2 * ε ^ 2)) * (1 / u ^ 2) := by
  rw [tentDualKernel_eq, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - |s|)]
  have hy : 0 < 2 * Real.pi * u * ε := by positivity
  have hexp : Real.exp (-2 * Real.pi * u * ε) ≤ 2 / (2 * Real.pi * u * ε) ^ 2 := by
    rw [show -2 * Real.pi * u * ε = -(2 * Real.pi * u * ε) by ring]
    exact exp_neg_le_two_div_sq hy
  have hcos : (1 - |s|) * |Real.cos (2 * Real.pi * u * (n + s))| ≤ 1 := by
    have h1 := Real.abs_cos_le_one (2 * Real.pi * u * (n + s))
    have h0 := abs_nonneg (Real.cos (2 * Real.pi * u * (n + s)))
    nlinarith [abs_nonneg s]
  calc Real.exp (-2 * Real.pi * u * ε) * ((1 - |s|) * |Real.cos (2 * Real.pi * u * (n + s))|)
      ≤ (2 / (2 * Real.pi * u * ε) ^ 2) * 1 :=
        mul_le_mul hexp hcos (by positivity) (by positivity)
    _ = (1 / (2 * Real.pi ^ 2 * ε ^ 2)) * (1 / u ^ 2) := by field_simp

theorem integrable_tentSeriesKernel {ν : Measure ℝ} [SFinite ν] (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {n ε : ℝ} (hn : 1 ≤ n) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    Integrable (uncurry (tentSeriesKernel n ε))
      ((volume.restrict (uIoc (-1 : ℝ) 1)).prod ν) := by
  refine integrable_prod_uIoc_of_inv_sq_bound hmom (measurable_uncurry_tentSeriesKernel n ε)
    (C := 4 * (n + 1) ^ 2 / (Real.pi * ε)) fun s hs => ?_
  rw [uIoc_of_le (by norm_num)] at hs
  have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2⟩
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  rw [Real.norm_eq_abs]
  exact abs_tentSeriesKernel_le hn hε0 hε1 hs1 hu

theorem integrable_tentDualKernel {ν : Measure ℝ} [SFinite ν] (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) (n : ℝ) {ε : ℝ} (hε0 : 0 < ε) :
    Integrable (uncurry (tentDualKernel n ε)) ((volume.restrict (uIoc (-1 : ℝ) 1)).prod ν) := by
  refine integrable_prod_uIoc_of_inv_sq_bound hmom
    (continuous_uncurry_tentDualKernel n ε).measurable
    (C := 1 / (2 * Real.pi ^ 2 * ε ^ 2)) fun s hs => ?_
  rw [uIoc_of_le (by norm_num)] at hs
  have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2⟩
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  rw [Real.norm_eq_abs]
  exact abs_tentDualKernel_le hε0 hs1 (lt_of_lt_of_le zero_lt_one hu)

theorem integrable_intervalIntegral_tentSeriesKernel {ν : Measure ℝ} [SFinite ν]
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {n ε : ℝ}
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun u : ℝ => ∫ s in (-1 : ℝ)..1, tentSeriesKernel n ε s u) ν := by
  refine (integrable_tentSeriesKernel hsupp hmom hn hε0 hε1).integral_prod_right.congr
    (Eventually.of_forall fun u => ?_)
  show (∫ s in uIoc (-1 : ℝ) 1, tentSeriesKernel n ε s u) =
    ∫ s in (-1 : ℝ)..1, tentSeriesKernel n ε s u
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

/-! ## 4. The window integrals -/

/-- The window turns the shifted cosine into `cos(2πun) sinc²(πu)`. -/
theorem integral_window_cos_shift {u : ℝ} (hu : u ≠ 0) (n : ℝ) :
    ∫ s in (-1 : ℝ)..1, (1 - |s|) * Real.cos (2 * Real.pi * u * (n + s)) =
      Real.cos (2 * Real.pi * u * n) * (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 := by
  have hcc : Continuous fun s : ℝ => (1 - |s|) * Real.cos (2 * Real.pi * u * s) := by fun_prop
  have hsc : Continuous fun s : ℝ => (1 - |s|) * Real.sin (2 * Real.pi * u * s) := by fun_prop
  have hodd : ∫ s in (-1 : ℝ)..1, (1 - |s|) * Real.sin (2 * Real.pi * u * s) = 0 := by
    rw [intervalIntegral_neg_one_one_eq hsc]
    refine (intervalIntegral.integral_congr fun s _ => ?_).trans intervalIntegral.integral_zero
    simp only [abs_neg, mul_neg, Real.sin_neg]
    ring
  rw [intervalIntegral.integral_congr (g := fun s => Real.cos (2 * Real.pi * u * n) *
      ((1 - |s|) * Real.cos (2 * Real.pi * u * s)) - Real.sin (2 * Real.pi * u * n) *
        ((1 - |s|) * Real.sin (2 * Real.pi * u * s))) fun s _ => by
      simp only
      rw [show 2 * Real.pi * u * (n + s) = 2 * Real.pi * u * n + 2 * Real.pi * u * s by ring,
        Real.cos_add]
      ring,
    intervalIntegral.integral_sub ((hcc.intervalIntegrable _ _).const_mul _)
      ((hsc.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    fejer_cos_integral hu, hodd, mul_zero, sub_zero]

theorem intervalIntegral_tentDualKernel {u : ℝ} (hu : u ≠ 0) (n ε : ℝ) :
    ∫ s in (-1 : ℝ)..1, tentDualKernel n ε s u = Real.exp (-2 * Real.pi * u * ε) *
      (Real.cos (2 * Real.pi * u * n) * (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2) := by
  rw [intervalIntegral.integral_congr fun s _ => tentDualKernel_eq n ε s u,
    intervalIntegral.integral_const_mul, integral_window_cos_shift hu]

/-- `Re(α/(πt) + β)` at `t = ε + iτ` in real coordinates. -/
theorem re_polar_eq (α β : ℂ) {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    (α / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) + β).re =
      (α.re * ε + α.im * τ) / (Real.pi * (ε ^ 2 + τ ^ 2)) + β.re := by
  have hpi := Real.pi_pos
  have hden : 0 < ε ^ 2 + τ ^ 2 := by positivity
  have hw : (Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I) =
      ((Real.pi * ε : ℝ) : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * I := by push_cast; ring
  rw [Complex.add_re, hw, Complex.div_re, Complex.normSq_add_mul_I]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, zero_add, add_zero]
  have h1 : (Real.pi * ε) ^ 2 + (Real.pi * τ) ^ 2 = Real.pi ^ 2 * (ε ^ 2 + τ ^ 2) := by ring
  rw [h1]
  field_simp

/-- The window weight of the imaginary polar part, `∫_{-1}^{1} (1 - |s|)(n+s)/(ε² + (n+s)²) ds`. -/
def tentPolarOdd (n ε : ℝ) : ℝ :=
  ∫ s in (-1 : ℝ)..1, (1 - |s|) * ((n + s) / (ε ^ 2 + (n + s) ^ 2))

theorem continuous_tentPolarOdd_integrand {ε : ℝ} (hε : 0 < ε) (n : ℝ) :
    Continuous fun s : ℝ => (1 - |s|) * ((n + s) / (ε ^ 2 + (n + s) ^ 2)) :=
  (continuous_const.sub continuous_abs).mul
    ((continuous_const.add continuous_id).div (by fun_prop) fun s => by positivity)

theorem tentPolarOdd_mem_Icc {n ε : ℝ} (hn : 1 ≤ n) (hε : 0 < ε) :
    0 ≤ tentPolarOdd n ε ∧ tentPolarOdd n ε ≤ 2 := by
  have hpt : ∀ s ∈ Icc (-1 : ℝ) 1,
      0 ≤ (1 - |s|) * ((n + s) / (ε ^ 2 + (n + s) ^ 2)) ∧
        (1 - |s|) * ((n + s) / (ε ^ 2 + (n + s) ^ 2)) ≤ 1 := by
    intro s hs
    have hs1 := abs_le.mpr ⟨hs.1, hs.2⟩
    have hns : 0 ≤ n + s := by linarith [hs.1]
    have hw0 : 0 ≤ 1 - |s| := by linarith
    have hwn : 1 - |s| ≤ n + s := by linarith [neg_abs_le s]
    have hd : 0 < ε ^ 2 + (n + s) ^ 2 := by positivity
    refine ⟨by positivity, ?_⟩
    rw [mul_div_assoc', div_le_one hd]
    nlinarith [sq_nonneg ε]
  have hc := continuous_tentPolarOdd_integrand hε n
  refine ⟨intervalIntegral.integral_nonneg (by norm_num) fun s hs => (hpt s hs).1, ?_⟩
  have h := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
    (hc.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable (μ := volume) (-1) 1 :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-1) 1)
    fun s hs => (hpt s hs).2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  unfold tentPolarOdd
  linarith

/-- **The polar side.** `∫_{-1}^{1} (1 - |s|) Re(-β/(πt) + β) = Re β - Re β · P_ε(-n) - (Im β/π) q_ε`. -/
theorem intervalIntegral_tentPolarKernel (β : ℂ) {ε : ℝ} (hε : 0 < ε) (n : ℝ) :
    ∫ s in (-1 : ℝ)..1, tentPolarKernel β n ε s =
      β.re - β.re * windowPoisson ε (-n) - β.im / Real.pi * tentPolarOdd n ε := by
  have hpi := Real.pi_pos
  have hpt : ∀ s : ℝ, tentPolarKernel β n ε s = β.re * (1 - |s|) -
      β.re * ((1 / Real.pi) * ((1 - |s|) * (ε / (ε ^ 2 + (s - -n) ^ 2)))) -
        β.im / Real.pi * ((1 - |s|) * ((n + s) / (ε ^ 2 + (n + s) ^ 2))) := by
    intro s
    have hd : 0 < ε ^ 2 + (n + s) ^ 2 := by positivity
    rw [tentPolarKernel, re_polar_eq _ _ hε, show s - -n = n + s by ring]
    simp only [Complex.neg_re, Complex.neg_im]
    field_simp
    ring
  have hw : IntervalIntegrable (fun s : ℝ => β.re * (1 - |s|)) volume (-1) 1 :=
    ((continuous_const.sub continuous_abs).intervalIntegrable _ _).const_mul _
  have hp : IntervalIntegrable (fun s : ℝ => β.re * ((1 / Real.pi) *
      ((1 - |s|) * (ε / (ε ^ 2 + (s - -n) ^ 2))))) volume (-1) 1 :=
    (((continuous_window_poisson hε (-n)).intervalIntegrable _ _).const_mul _).const_mul _
  have ho : IntervalIntegrable (fun s : ℝ => β.im / Real.pi *
      ((1 - |s|) * ((n + s) / (ε ^ 2 + (n + s) ^ 2)))) volume (-1) 1 :=
    ((continuous_tentPolarOdd_integrand hε n).intervalIntegrable _ _).const_mul _
  rw [intervalIntegral.integral_congr fun s _ => hpt s,
    intervalIntegral.integral_sub (hw.sub hp) ho, intervalIntegral.integral_sub hw hp,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    fejer_triangle_integral_one, mul_one]
  rfl

/-- **The defect side.** `|∫_{-1}^{1} (1 - |s|) Re J(ε + i(n + s)) ds| ≤ (3/π) ‖g‖₁`. -/
theorem abs_intervalIntegral_tentDefectKernel_le {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    {n ε : ℝ} (hn : 1 ≤ n) (hε : 0 < ε) :
    |∫ s in (-1 : ℝ)..1, tentDefectKernel g n ε s| ≤ 3 / Real.pi * ∫ t, ‖g t‖ := by
  have hpi := Real.pi_pos
  set M : ℝ := ∫ t, ‖g t‖ with hM
  have hpt : ∀ s : ℝ, |s| ≤ 1 → ‖tentDefectKernel g n ε s‖ ≤ 3 / (2 * Real.pi) * M := by
    intro s hs
    set t : ℂ := (ε : ℂ) + ((n + s : ℝ) : ℂ) * I with ht
    have hre : 0 < t.re := by simp [ht, hε]
    have hT : 0 < ‖t‖ := norm_pos_iff.mpr fun h => by rw [h, zero_re] at hre; exact lt_irrefl _ hre
    have hJ := RHTower.HamburgerStability.norm_defectLaplace_le hgm.aestronglyMeasurable hgb hre
    have habel : RHTower.HamburgerStability.abelMass g (2 * (t.re / ‖t‖)) ≤ M := by
      have hδ : 0 < 2 * (t.re / ‖t‖) :=
        mul_pos two_pos (RHTower.HamburgerStability.pos_re_div_norm hre)
      unfold RHTower.HamburgerStability.abelMass
      refine integral_mono
        (RHTower.HamburgerStability.integrable_abelMass hgm.aestronglyMeasurable hgb hδ)
        hgi.norm fun x => ?_
      refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
      have := mul_nonneg hδ.le (abs_nonneg x)
      linarith
    have hw0 : 0 ≤ 1 - |s| := by linarith
    have hw1 : 1 - |s| ≤ 1 := by linarith [abs_nonneg s]
    -- `(1 - |s|)² ≤ n + s ≤ ‖t‖`, so the window absorbs `‖t‖^{-1/2}`.
    have hwt : (1 - |s|) ^ 2 ≤ ‖t‖ := by
      have him : |n + s| ≤ ‖t‖ := by
        have h := Complex.abs_im_le_norm t
        simpa [ht] using h
      have : 1 - |s| ≤ n + s := by linarith [neg_abs_le s]
      nlinarith [le_abs_self (n + s)]
    have hwin : (1 - |s|) * ‖t‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hT.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv,
        div_le_one (Real.sqrt_pos.mpr hT)]
      calc 1 - |s| = Real.sqrt ((1 - |s|) ^ 2) := (Real.sqrt_sq hw0).symm
        _ ≤ Real.sqrt ‖t‖ := Real.sqrt_le_sqrt hwt
    have hJ' : ‖RHTower.HamburgerStability.defectLaplace g t‖ ≤
        3 / (2 * Real.pi) * ‖t‖ ^ (-(1 / 2 : ℝ)) * M :=
      hJ.trans (mul_le_mul_of_nonneg_left habel (by positivity))
    rw [Real.norm_eq_abs, tentDefectKernel, abs_mul, abs_of_nonneg hw0]
    calc (1 - |s|) * |(RHTower.HamburgerStability.defectLaplace g t).re|
        ≤ (1 - |s|) * (3 / (2 * Real.pi) * ‖t‖ ^ (-(1 / 2 : ℝ)) * M) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hJ') hw0
      _ = 3 / (2 * Real.pi) * M * ((1 - |s|) * ‖t‖ ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ 3 / (2 * Real.pi) * M * 1 :=
          mul_le_mul_of_nonneg_left hwin
            (mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _))
      _ = 3 / (2 * Real.pi) * M := mul_one _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := 1)
    (f := tentDefectKernel g n ε) fun s hs => by
      rw [uIoc_of_le (by norm_num)] at hs
      exact hpt s (abs_le.mpr ⟨hs.1.le, hs.2⟩)
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [show |(1 : ℝ) - -1| = 2 by norm_num]
  ring

/-! ## 5. The tent pairing -/

theorem continuous_tentDefectKernel {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (n : ℝ) {ε : ℝ} (hε : 0 < ε) : Continuous (tentDefectKernel g n ε) :=
  (continuous_const.sub continuous_abs).mul (Complex.continuous_re.comp
    ((continuous_defectLaplace_line hgm hgb hε).comp (continuous_const.add continuous_id)))

theorem continuous_tentPolarKernel (β : ℂ) (n : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (tentPolarKernel β n ε) := by
  have hpi := Real.pi_pos
  have h : tentPolarKernel β n ε = fun s => (1 - |s|) *
      ((-β.re * ε + -β.im * (n + s)) / (Real.pi * (ε ^ 2 + (n + s) ^ 2)) + β.re) := by
    funext s
    rw [tentPolarKernel, re_polar_eq _ _ hε]
    simp only [Complex.neg_re, Complex.neg_im]
  rw [h]
  exact (continuous_const.sub continuous_abs).mul
    (((continuous_const.add (continuous_const.mul (continuous_const.add continuous_id))).div
      (by fun_prop) fun s => by positivity).add continuous_const)

/-- The real, window-weighted form of the defective Laplace identity on `t = ε + i(n + s)`. -/
theorem integral_tentSeriesKernel_eq_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x)
    {ε : ℝ} (hε : 0 < ε) (n s : ℝ) :
    ∫ u, tentSeriesKernel n ε s u ∂ν =
      ∫ u, tentDualKernel n ε s u ∂ν + tentPolarKernel β n ε s + tentDefectKernel g n ε s := by
  have ht : 0 < ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I).re := by simp [hε]
  have hser : ∫ u, tentSeriesKernel n ε s u ∂ν =
      (1 - |s|) * (measureSeries ν ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)).re := by
    have h : ∫ u : ℝ, ((((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)) /
        ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I) ^ 2))).re ∂ν =
        (measureSeries ν ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)).re :=
      integral_re (integrable_measureSeries_integrand hsupp hmom ht)
    rw [← h, ← integral_const_mul]
    rfl
  have hdual : ∫ u, tentDualKernel n ε s u ∂ν =
      (1 - |s|) * (measureDual ν ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)).re := by
    have h : ∫ u : ℝ, (cexp (-(2 * Real.pi * (u : ℂ) *
        ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)))).re ∂ν =
        (measureDual ν ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)).re :=
      integral_re (integrable_measureDual_integrand hsupp hmom ht)
    rw [← h, ← integral_const_mul]
    rfl
  rw [hser, hdual, measureSeries_eq_of_theta_defect hsupp hmom hgm hgb htheta ht,
    tentPolarKernel, tentDefectKernel]
  simp only [add_re]
  ring

/-- **Tent pairing with a defect.** -/
theorem tent_pairing_identity_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x)
    {n ε : ℝ} (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ u, (∫ s in (-1 : ℝ)..1, tentSeriesKernel n ε s u) ∂ν =
      ∫ u, (∫ s in (-1 : ℝ)..1, tentDualKernel n ε s u) ∂ν +
        (∫ s in (-1 : ℝ)..1, tentPolarKernel β n ε s) +
          ∫ s in (-1 : ℝ)..1, tentDefectKernel g n ε s := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hL := integrable_tentSeriesKernel hsupp hmom hn hε0 hε1
  have hD := integrable_tentDualKernel hsupp hmom n hε0
  have hD_ii : IntervalIntegrable (fun s : ℝ => ∫ u, tentDualKernel n ε s u ∂ν) volume (-1) 1 :=
    intervalIntegrable_iff.mpr hD.integral_prod_left
  have hP_ii : IntervalIntegrable (tentPolarKernel β n ε) volume (-1) 1 :=
    (continuous_tentPolarKernel β n hε0).intervalIntegrable _ _
  have hJ_ii : IntervalIntegrable (tentDefectKernel g n ε) volume (-1) 1 :=
    (continuous_tentDefectKernel hgm.aestronglyMeasurable hgb n hε0).intervalIntegrable _ _
  have hint : ∫ s in (-1 : ℝ)..1, ∫ u, tentSeriesKernel n ε s u ∂ν =
      (∫ s in (-1 : ℝ)..1, ∫ u, tentDualKernel n ε s u ∂ν) +
        (∫ s in (-1 : ℝ)..1, tentPolarKernel β n ε s) +
          ∫ s in (-1 : ℝ)..1, tentDefectKernel g n ε s := by
    calc ∫ s in (-1 : ℝ)..1, ∫ u, tentSeriesKernel n ε s u ∂ν
        = ∫ s in (-1 : ℝ)..1, ((∫ u, tentDualKernel n ε s u ∂ν) + tentPolarKernel β n ε s +
            tentDefectKernel g n ε s) :=
          intervalIntegral.integral_congr fun s _ =>
            integral_tentSeriesKernel_eq_of_theta_defect hsupp hmom hgm hgb htheta hε0 n s
      _ = (∫ s in (-1 : ℝ)..1, ((∫ u, tentDualKernel n ε s u ∂ν) +
            tentPolarKernel β n ε s)) + ∫ s in (-1 : ℝ)..1, tentDefectKernel g n ε s :=
          intervalIntegral.integral_add (hD_ii.add hP_ii) hJ_ii
      _ = _ := by rw [intervalIntegral.integral_add hD_ii hP_ii]
  rwa [intervalIntegral_integral_swap hL, intervalIntegral_integral_swap hD] at hint

/-! ## 6. The weights -/

/-- **Tent masses from the theta law with a defect.** If the off-lattice mass is at most `S`, then
`|(1/2) ∫ tent_n dν - Re β| ≤ S + (3/π) ‖g‖₁ + (2/π) |Im β|` for every real `n ≥ 1`. -/
theorem abs_half_integral_unitTent_sub_le_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x)
    {S : ℝ} (hS : ∫ u : ℝ, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν ≤ S)
    {n : ℝ} (hn : 1 ≤ n) :
    |(1 / 2) * ∫ u, unitTent n u ∂ν - β.re| ≤
      S + 3 / Real.pi * (∫ t, ‖g t‖) + 2 / Real.pi * |β.im| := by
  have hpi := Real.pi_pos
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  -- Series side: dominated convergence to `(1/2) ∫ tent_n dν`.
  have hlimA : Tendsto (fun ε => ∫ u, (∫ s in (-1 : ℝ)..1, tentSeriesKernel n ε s u) ∂ν)
      (𝓝[>] 0) (𝓝 ((1 / 2) * ∫ u, unitTent n u ∂ν)) := by
    rw [← integral_const_mul]
    refine tendsto_integral_filter_of_dominated_convergence (fun u => (n + 2) ^ 2 * (1 / u ^ 2))
      (hev.mono fun ε hε =>
        (integrable_intervalIntegral_tentSeriesKernel hsupp hmom hn hε.1 hε.2.le).1)
      (hev.mono fun ε hε => ?_) (hmom.const_mul _) ?_
    · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg (by norm_num)
        fun s hs => tentSeriesKernel_nonneg hε.1 n (abs_le.mpr hs) u)]
      exact intervalIntegral_tentSeriesKernel_le hn hε.1 hε.2.le hu
    · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have h0 : unitTent 0 (-u - n) = 0 :=
        unitTent_eq_zero (by rw [sub_zero, abs_of_neg (by linarith)]; linarith)
      have hlim := ((tendsto_windowPoisson (u - n)).add (tendsto_windowPoisson (-u - n))).const_mul
        (1 / 2 : ℝ)
      rw [h0, add_zero, unitTent_zero_sub] at hlim
      exact hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε =>
        (intervalIntegral_tentSeriesKernel hε n u).symm)
  -- Polar side: the real Poisson mass at `-n` vanishes in the limit.
  have hlimP : Tendsto (fun ε => windowPoisson ε (-n)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_windowPoisson (-n)
    rwa [unitTent_eq_zero (by rw [sub_zero, abs_neg, abs_of_pos (by linarith)]; exact hn)] at h
  -- Integrability of the off-lattice weight.
  have hsinc : Integrable (fun u : ℝ => (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2) ν := by
    refine (hmom.const_mul (1 / Real.pi ^ 2)).mono' (Measurable.aestronglyMeasurable
      (by fun_prop)) ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, mul_pow, one_div_mul_one_div]
    exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (by positivity)
  -- Uniform bound on `(0, 1)`.
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      |(∫ u, (∫ s in (-1 : ℝ)..1, tentSeriesKernel n ε s u) ∂ν) - β.re +
        β.re * windowPoisson ε (-n)| ≤ S + 3 / Real.pi * (∫ t, ‖g t‖) + 2 / Real.pi * |β.im| := by
    filter_upwards [hev] with ε hε
    have hε0 := hε.1
    rw [tent_pairing_identity_of_theta_defect hsupp hmom hgm hgb htheta hn hε0 hε.2.le,
      intervalIntegral_tentPolarKernel β hε0 n]
    have hB : |∫ u, (∫ s in (-1 : ℝ)..1, tentDualKernel n ε s u) ∂ν| ≤ S := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hsinc ?_).trans hS
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : u ≠ 0 := (lt_of_lt_of_le zero_lt_one hu).ne'
      rw [intervalIntegral_tentDualKernel hu0, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (sq_nonneg (Real.sin (Real.pi * u) / (Real.pi * u)))]
      have he : Real.exp (-2 * Real.pi * u * ε) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 < 2 * Real.pi * u * ε := by
          have := lt_of_lt_of_le zero_lt_one hu; positivity
        linarith
      have hc := Real.abs_cos_le_one (2 * Real.pi * u * n)
      calc Real.exp (-2 * Real.pi * u * ε) * (|Real.cos (2 * Real.pi * u * n)| *
            (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2)
          ≤ 1 * (1 * (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2) :=
            mul_le_mul he (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (by positivity)
              zero_le_one
        _ = (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 := by ring
    have hD := abs_intervalIntegral_tentDefectKernel_le hgm hgb hgi hn hε0
    have hq := tentPolarOdd_mem_Icc hn hε0
    have hQ : |β.im / Real.pi * tentPolarOdd n ε| ≤ 2 / Real.pi * |β.im| := by
      rw [abs_mul, abs_div, abs_of_pos hpi, abs_of_nonneg hq.1]
      calc |β.im| / Real.pi * tentPolarOdd n ε ≤ |β.im| / Real.pi * 2 :=
            mul_le_mul_of_nonneg_left hq.2 (by positivity)
        _ = 2 / Real.pi * |β.im| := by ring
    have e : (∫ u, (∫ s in (-1 : ℝ)..1, tentDualKernel n ε s u) ∂ν) +
        (β.re - β.re * windowPoisson ε (-n) - β.im / Real.pi * tentPolarOdd n ε) +
          (∫ s in (-1 : ℝ)..1, tentDefectKernel g n ε s) - β.re + β.re * windowPoisson ε (-n) =
        (∫ u, (∫ s in (-1 : ℝ)..1, tentDualKernel n ε s u) ∂ν) +
          (∫ s in (-1 : ℝ)..1, tentDefectKernel g n ε s) -
            β.im / Real.pi * tentPolarOdd n ε := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    linarith [abs_add_le (∫ u, (∫ s in (-1 : ℝ)..1, tentDualKernel n ε s u) ∂ν)
      (∫ s in (-1 : ℝ)..1, tentDefectKernel g n ε s)]
  have hlim := ((hlimA.sub_const β.re).add (hlimP.const_mul β.re)).abs
  rw [mul_zero, add_zero] at hlim
  exact le_of_tendsto hlim hbound

/-! ## 7. The imaginary part of the pole coefficient -/

/-- The defective theta law of a positive measure from its critical-line defect. -/
theorem measureTheta_defect_relation {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) ν)
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * measureDirichlet ν s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) :
    ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x := by
  have hmom2 : Integrable (fun u : ℝ => 1 / u ^ 2) ν :=
    integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom
  have hθm : MellinConvergent (measureTheta ν) (3 / 4) := by
    have h := hasMellin_measureTheta hsupp (s := (3 / 2 : ℂ)) (by norm_num)
      (by simpa using hmom) hmom2
    simpa [show ((3 / 2 : ℂ) / 2) = (3 / 4 : ℂ) by ring] using h.1
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      mellin (measureTheta ν) (s / 2) = E s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    have hm := hasMellin_measureTheta hsupp (s := s) (by linarith)
      (by rw [hs]; exact hmom) hmom2
    rw [hm.2]; exact hR s hs
  have him : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2 = t := fun t => by simp
  have hdint : Integrable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) *
      g ((2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2) := by
    simp only [him]
    exact RHTower.HamburgerStability.integrable_Gammaℝ_mul hgm.aestronglyMeasurable hgb
  intro x hx
  have h := critical_line_even_theta_relation_defect
    (d := fun s => Complex.Gammaℝ s * g (s.im / 2))
    (continuousOn_measureTheta hsupp hmom2) hθm hEc hEd hdecay hR' hC hdint hx
  simp only [him] at h
  unfold RHTower.HamburgerStability.defectKernel
  linear_combination h

/-- `Im β = 2 Im K(4)`: the theta law at `x = 4` has real theta values. -/
theorem im_eq_of_theta_defect {ν : Measure ℝ} {β : ℂ} {g : ℝ → ℂ}
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x) :
    β.im = 2 * (RHTower.HamburgerStability.defectKernel g 4).im := by
  have h4pow : ((4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = ((2⁻¹ : ℝ) : ℂ) := by
    have h := ofReal_sq_cpow_neg_half (c := 2) (by norm_num)
    rwa [show (2 : ℝ) ^ 2 = 4 by norm_num] at h
  have h := htheta 4 (by norm_num)
  rw [h4pow] at h
  have him := congrArg Complex.im h
  simp only [add_im, neg_im, mul_im, ofReal_re, ofReal_im, measureTheta_im_eq_zero, zero_mul,
    mul_zero, add_zero, zero_add] at him
  linarith

/-- The constant `κ = 4^{-1/4} π^{-1/4} Γ(1/4)` bounding the defect kernel at `x = 4`. -/
def defectKernelConst : ℝ :=
  (4 : ℝ) ^ (-(1 / 4 : ℝ)) * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4))

/-- `‖K(4)‖ ≤ (κ/2π) ‖g‖₁`, from `‖Γ_ℝ(1/2 + 2it)‖ ≤ π^{-1/4} Γ(1/4)`. -/
theorem norm_defectKernel_four_le {g : ℝ → ℂ} (hgi : Integrable g) :
    ‖RHTower.HamburgerStability.defectKernel g 4‖ ≤
      1 / (2 * Real.pi) * (defectKernelConst * ∫ t, ‖g t‖) := by
  have hpi := Real.pi_pos
  have hpt : ∀ t : ℝ, ‖((4 : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * g t)‖ ≤
        defectKernelConst * ‖g t‖ := by
    intro t
    have h4 : ‖((4 : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I))‖ = (4 : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      simp
    have hG : ‖Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I))‖ ≤
        Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) := by
      rw [RHTower.HamburgerStability.Gammaℝ_quarter_line, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hpi]
      have hre : (-(2 * (((1 / 4 : ℝ) : ℂ) + t * I)) / 2).re = -(1 / 4) := by simp; norm_num
      have hΓ := norm_Gamma_le_Gamma_re (s := ((1 / 4 : ℝ) : ℂ) + t * I) (by simp)
      have hre' : (((1 / 4 : ℝ) : ℂ) + t * I).re = 1 / 4 := by simp
      rw [hre'] at hΓ
      rw [hre]
      exact mul_le_mul_of_nonneg_left hΓ (by positivity)
    rw [norm_mul, norm_mul, h4, defectKernelConst, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
      (by positivity)
  unfold RHTower.HamburgerStability.defectKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (hgi.norm.const_mul _) (Eventually.of_forall hpt)

theorem abs_im_le_of_theta_defect {ν : Measure ℝ} {β : ℂ} {g : ℝ → ℂ}
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        RHTower.HamburgerStability.defectKernel g x) (hgi : Integrable g) :
    |β.im| ≤ defectKernelConst / Real.pi * ∫ t, ‖g t‖ := by
  have hpi := Real.pi_pos
  rw [im_eq_of_theta_defect htheta, abs_mul, abs_two]
  have h := (Complex.abs_im_le_norm _).trans (norm_defectKernel_four_le (g := g) hgi)
  calc 2 * |(RHTower.HamburgerStability.defectKernel g 4).im|
      ≤ 2 * (1 / (2 * Real.pi) * (defectKernelConst * ∫ t, ‖g t‖)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = defectKernelConst / Real.pi * ∫ t, ‖g t‖ := by field_simp

/-! ## 8. Quantitative stability of the weights -/

/-- **The weights of a positive measure with an approximate functional equation.** Let `ν ≥ 0`
vanish on `(-∞, 1)` with `∫ u^{-3/2} dν < ∞`, and let `E` be continuous on `1/2 ≤ Re s ≤ 3/2`,
holomorphic inside and `O(1/(1 + t²))`, with `Γ_ℝ(s) D_ν(s) = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2`
and `E(s) - E(1 - s) = -β (Γ_ℝ(s - 1) - Γ_ℝ(-s)) + Γ_ℝ(s) g(Im s / 2)` on `Re s = 1/2`, with `g`
measurable, polynomially bounded and integrable. Then for every real `n ≥ 1` the unit tent mass of
`ν` at `n` is `2 Re β` up to `(18/π + 4κ/π²) ‖g‖₁`. -/
theorem abs_integral_unitTent_sub_le_of_critical_line_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) ν)
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * measureDirichlet ν s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    {n : ℝ} (hn : 1 ≤ n) :
    |∫ u, unitTent n u ∂ν - 2 * β.re| ≤
      (18 / Real.pi + 4 * defectKernelConst / Real.pi ^ 2) * ∫ t, ‖g t‖ := by
  have hpi := Real.pi_pos
  have hmom2 : Integrable (fun u : ℝ => 1 / u ^ 2) ν :=
    integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom
  have htheta := measureTheta_defect_relation hsupp hmom hEc hEd hdecay hR hC hgm hgb
  have hS := integral_sinc_sq_le_of_critical_line_defect hsupp hmom hEc hEd hdecay hR hC hgm hgb
    hgi
  have hIm := abs_im_le_of_theta_defect htheta hgi
  have h := abs_half_integral_unitTent_sub_le_of_theta_defect hsupp hmom2 hgm hgb hgi htheta hS hn
  have e : ∫ u, unitTent n u ∂ν - 2 * β.re = 2 * ((1 / 2) * ∫ u, unitTent n u ∂ν - β.re) := by
    ring
  rw [e, abs_mul, abs_two]
  have hIm' : 2 / Real.pi * |β.im| ≤ 2 / Real.pi * (defectKernelConst / Real.pi * ∫ t, ‖g t‖) :=
    mul_le_mul_of_nonneg_left hIm (by positivity)
  have e2 : 2 * (6 / Real.pi * (∫ t, ‖g t‖) + 3 / Real.pi * (∫ t, ‖g t‖) +
      2 / Real.pi * (defectKernelConst / Real.pi * ∫ t, ‖g t‖)) =
      (18 / Real.pi + 4 * defectKernelConst / Real.pi ^ 2) * ∫ t, ‖g t‖ := by
    field_simp; ring
  rw [← e2]
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hIm') (by norm_num))

end GaloisForLFunctions.ArithmeticPositiveDuality
