import GaloisForLFunctions.RHTower.WeilFullConePoissonRepresentation
import GaloisForLFunctions.RHTower.WeilPositiveShortIntervalSupport

/-!
# Full-cone Weil positivity is Herglotz positivity on `Re s > ½`

**Theorem** (`herglotzWeilPositive_of_weilPositiveFull`).  If `lam` is full-cone Weil-positive,
then the weights `lam(n)1_{n≥2}` are Herglotz–Weil positive for `ζ`'s archimedean datum: the Weil
function `Φ_lam(s) = ½ψ(s/2) − ½ log π + 1/s + 1/(s−1) − Σ_{n≥2} lam(n)n^{−s}` continues
holomorphically from `Re s > 1` to `Re s > ½` with nonnegative real part.

This discharges the hypothesis `HerglotzWeilPositive` of the corpus for the whole Weil cone.  For
example, a prime-supported full-cone Weil-positive system meets every interval
`(x, x + x^{1/2+ε})`, `x` large, in a prime (`exists_prime_mem_Ioo_of_weilPositiveFull`).

**Proof.**  With the boundary measure `μ_lam` (`WeilFullConeBoundaryMeasure`) put

`H(z) = ∫ (1/(z − ir) − ir/(1 + r²)) dμ_lam(r)`,  `Re z > 0`.

The kernel is `O((1 + r²)⁻¹)` locally uniformly in `z`, and `∫ dμ_lam/(1 + r²) < ∞`, so `H` is
holomorphic on `Re z > 0` and `Re H(z) = Re z ∫ |z − ir|⁻² dμ_lam ≥ 0`.  By the Poisson
representation, `Re H(s − ½) = Re Φ_lam(s)` on `Re s > 1`.  A holomorphic function on the convex
set `Re s > 1` with vanishing real part is constant, so `Φ_lam(s) = H(s − ½) + iC` there, and
`H(s − ½) + iC` is the required continuation.
-/

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real ComplexConjugate NNReal ENNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-! ## The Herglotz kernel -/

/-- The Herglotz kernel `1/(z − ir) − ir/(1 + r²)`. -/
def herglotzKernel (z : ℂ) (r : ℝ) : ℂ := 1 / (z - I * r) - I * r / (1 + (r : ℂ) ^ 2)

theorem sub_I_mul_ne_zero {z : ℂ} (hz : 0 < z.re) (r : ℝ) : z - I * (r : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_sub_I_mul_ofReal] at this
  simp at this
  linarith

theorem one_add_sq_ne_zero (r : ℝ) : (1 + (r : ℂ) ^ 2) ≠ 0 := by
  have : (1 + (r : ℂ) ^ 2) = ((1 + r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this]
  exact_mod_cast (by positivity : (1 + r ^ 2 : ℝ) ≠ 0)

theorem herglotzKernel_eq {z : ℂ} (hz : 0 < z.re) (r : ℝ) :
    herglotzKernel z r = (1 - I * r * z) / ((z - I * r) * (1 + (r : ℂ) ^ 2)) := by
  unfold herglotzKernel
  have h1 := sub_I_mul_ne_zero hz r
  have h2 := one_add_sq_ne_zero r
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_sub_I_mul_ge_re {z : ℂ} (r : ℝ) : z.re ≤ ‖z - I * (r : ℂ)‖ := by
  have := Complex.abs_re_le_norm (z - I * (r : ℂ))
  rw [re_sub_I_mul_ofReal] at this
  linarith [le_abs_self z.re]

theorem norm_sub_I_mul_ge_abs (z : ℂ) (r : ℝ) : |r| - ‖z‖ ≤ ‖z - I * (r : ℂ)‖ := by
  have h := norm_sub_norm_le (I * (r : ℂ)) z
  rw [norm_sub_rev, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
  linarith

theorem norm_one_add_sq (r : ℝ) : ‖(1 + (r : ℂ) ^ 2)‖ = 1 + r ^ 2 := by
  have : (1 + (r : ℂ) ^ 2) = ((1 + r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- `|1 − irz| ≤ M |z − ir|` with `M` depending only on lower and upper bounds for `z`. -/
theorem norm_one_sub_le {z : ℂ} {c R : ℝ} (hc : 0 < c) (hzc : c ≤ z.re) (hzR : ‖z‖ ≤ R) (r : ℝ) :
    ‖1 - I * (r : ℂ) * z‖ ≤ ((1 + (2 * R + 1) * R) / c + 2 * (1 + R)) * ‖z - I * (r : ℂ)‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hzR
  have hnum : ‖1 - I * (r : ℂ) * z‖ ≤ 1 + |r| * R := by
    calc ‖1 - I * (r : ℂ) * z‖ ≤ ‖(1 : ℂ)‖ + ‖I * (r : ℂ) * z‖ := norm_sub_le _ _
      _ = 1 + |r| * ‖z‖ := by
        rw [norm_one, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs]
      _ ≤ 1 + |r| * R := by gcongr
  have hden1 := norm_sub_I_mul_ge_re (z := z) r
  have hden2 := norm_sub_I_mul_ge_abs z r
  have hpos : 0 ≤ ‖z - I * (r : ℂ)‖ := norm_nonneg _
  have hM1 : 0 ≤ (1 + (2 * R + 1) * R) / c := by positivity
  rcases le_or_gt |r| (2 * R + 1) with hr | hr
  · have h1 : 1 + |r| * R ≤ 1 + (2 * R + 1) * R := by nlinarith [abs_nonneg r]
    have h2 : 1 + (2 * R + 1) * R ≤ (1 + (2 * R + 1) * R) / c * ‖z - I * (r : ℂ)‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have : 0 ≤ 1 + (2 * R + 1) * R := by positivity
      nlinarith
    nlinarith
  · have hr1 : 1 ≤ |r| := by linarith
    have hden3 : |r| / 2 ≤ ‖z - I * (r : ℂ)‖ := by linarith
    have h1 : 1 + |r| * R ≤ |r| * (1 + R) := by nlinarith
    nlinarith

/-- `|1/(z − ir)|² ≤ N/(1 + r²)`. -/
theorem inv_norm_sq_le {z : ℂ} {c R : ℝ} (hc : 0 < c) (hzc : c ≤ z.re) (hzR : ‖z‖ ≤ R) (r : ℝ) :
    1 / ‖z - I * (r : ℂ)‖ ^ 2 ≤ ((1 + (2 * R + 1) ^ 2) / c ^ 2 + 8) / (1 + r ^ 2) := by
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hzR
  have hden1 := norm_sub_I_mul_ge_re (z := z) r
  have hden2 := norm_sub_I_mul_ge_abs z r
  have hpos : 0 < ‖z - I * (r : ℂ)‖ := lt_of_lt_of_le hc (hzc.trans hden1)
  have hq : 0 < 1 + r ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hq, one_mul]
  have hN1 : 0 ≤ (1 + (2 * R + 1) ^ 2) / c ^ 2 := by positivity
  rcases le_or_gt |r| (2 * R + 1) with hr | hr
  · have hsq : r ^ 2 ≤ (2 * R + 1) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg r) hr 2
    have hc2 : c ^ 2 ≤ ‖z - I * (r : ℂ)‖ ^ 2 := pow_le_pow_left₀ hc.le (hzc.trans hden1) 2
    have : 1 + r ^ 2 ≤ (1 + (2 * R + 1) ^ 2) / c ^ 2 * ‖z - I * (r : ℂ)‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith [sq_nonneg ‖z - I * (r : ℂ)‖]
  · have hr1 : 1 ≤ |r| := by linarith
    have hden3 : |r| / 2 ≤ ‖z - I * (r : ℂ)‖ := by linarith
    have h4 : r ^ 2 / 4 ≤ ‖z - I * (r : ℂ)‖ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hden3 2
      rw [div_pow, sq_abs] at this
      linarith
    have h5 : 1 ≤ r ^ 2 := by rw [← sq_abs]; nlinarith
    nlinarith [sq_nonneg ‖z - I * (r : ℂ)‖]

theorem norm_herglotzKernel_le {z : ℂ} {c R : ℝ} (hc : 0 < c) (hzc : c ≤ z.re) (hzR : ‖z‖ ≤ R)
    (r : ℝ) : ‖herglotzKernel z r‖ ≤
      ((1 + (2 * R + 1) * R) / c + 2 * (1 + R)) * (1 + r ^ 2)⁻¹ := by
  have hz : 0 < z.re := lt_of_lt_of_le hc hzc
  rw [herglotzKernel_eq hz, norm_div, norm_mul, norm_one_add_sq]
  have hpos : 0 < ‖z - I * (r : ℂ)‖ := norm_pos_iff.mpr (sub_I_mul_ne_zero hz r)
  have hq : 0 < 1 + r ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  have := norm_one_sub_le hc hzc hzR r
  calc ‖1 - I * (r : ℂ) * z‖ ≤ ((1 + (2 * R + 1) * R) / c + 2 * (1 + R)) * ‖z - I * (r : ℂ)‖ :=
        this
    _ = ((1 + (2 * R + 1) * R) / c + 2 * (1 + R)) * (1 + r ^ 2)⁻¹ *
          (‖z - I * (r : ℂ)‖ * (1 + r ^ 2)) := by
        field_simp

theorem hasDerivAt_herglotzKernel {z : ℂ} (hz : 0 < z.re) (r : ℝ) :
    HasDerivAt (fun x => herglotzKernel x r) (-(1 / (z - I * r) ^ 2)) z := by
  have h1 := sub_I_mul_ne_zero hz r
  have hd : HasDerivAt (fun x : ℂ => x - I * (r : ℂ)) 1 z := (hasDerivAt_id z).sub_const _
  have hinv := (hd.inv h1).sub_const (I * r / (1 + (r : ℂ) ^ 2))
  have e : (fun x => herglotzKernel x r) =
      fun y => (y - I * (r : ℂ))⁻¹ - I * r / (1 + (r : ℂ) ^ 2) := by
    funext x
    simp [herglotzKernel, one_div]
  rw [e, show -(1 / (z - I * (r : ℂ)) ^ 2) = -1 / (z - I * (r : ℂ)) ^ 2 by ring]
  exact hinv

/-! ## Integrability against the boundary measure -/

theorem integrable_inv_one_add_sq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) (boundaryMeasure hW) := by
  have h := integrable_toReal_of_lintegral_ne_top (measurable_poissonDensity 1).aemeasurable
    (lintegral_poissonDensity_three_halves_lt_top hW).ne
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only [poissonDensity, ENNReal.coe_toReal, NNReal.coe_pow, coe_nnnorm]
  rw [norm_div, norm_one, div_pow, one_pow]
  have hn : ‖(1 : ℂ) - I * (r : ℂ)‖ ^ 2 = 1 + r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hn, one_div]

theorem measurable_herglotzKernel (z : ℂ) : Measurable (herglotzKernel z) := by
  unfold herglotzKernel
  fun_prop

theorem integrable_herglotzKernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z : ℂ}
    (hz : 0 < z.re) : Integrable (herglotzKernel z) (boundaryMeasure hW) := by
  refine ((integrable_inv_one_add_sq hW).const_mul
    ((1 + (2 * ‖z‖ + 1) * ‖z‖) / z.re + 2 * (1 + ‖z‖))).mono'
    (measurable_herglotzKernel z).aestronglyMeasurable
    (Eventually.of_forall fun r => norm_herglotzKernel_le hz le_rfl le_rfl r)

/-! ## The Herglotz function -/

/-- The Herglotz function `H(z) = ∫ (1/(z − ir) − ir/(1 + r²)) dμ_lam(r)`. -/
def herglotzFunction {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (z : ℂ) : ℂ :=
  ∫ r, herglotzKernel z r ∂boundaryMeasure hW

theorem hasDerivAt_herglotzFunction {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z₀ : ℂ}
    (hz₀ : 0 < z₀.re) :
    HasDerivAt (herglotzFunction hW)
      (∫ r, -(1 / (z₀ - I * r) ^ 2) ∂boundaryMeasure hW) z₀ := by
  set c : ℝ := z₀.re / 2 with hcdef
  set R : ℝ := ‖z₀‖ + z₀.re / 2 with hRdef
  have hc : 0 < c := by positivity
  have hball : ∀ x ∈ ball z₀ c, c ≤ x.re ∧ ‖x‖ ≤ R := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    constructor
    · have := Complex.abs_re_le_norm (x - z₀)
      rw [Complex.sub_re] at this
      have := neg_abs_le (x.re - z₀.re)
      linarith
    · have := norm_le_norm_add_norm_sub' x z₀
      have h2 : ‖x - z₀‖ = ‖z₀ - x‖ := norm_sub_rev _ _
      linarith
  set N : ℝ := (1 + (2 * R + 1) ^ 2) / c ^ 2 + 8 with hN
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := boundaryMeasure hW)
    (F := fun x r => herglotzKernel x r) (x₀ := z₀) (s := ball z₀ c)
    (F' := fun x r => -(1 / (x - I * r) ^ 2)) (bound := fun r => N * (1 + r ^ 2)⁻¹)
    (ball_mem_nhds z₀ hc)
    (Eventually.of_forall fun x => (measurable_herglotzKernel x).aestronglyMeasurable)
    (integrable_herglotzKernel hW hz₀)
    (by fun_prop : Measurable fun r : ℝ => -(1 / (z₀ - I * (r : ℂ)) ^ 2)).aestronglyMeasurable
    (Eventually.of_forall fun r x hx => by
      obtain ⟨hxc, hxR⟩ := hball x hx
      rw [norm_neg, norm_div, norm_one, norm_pow]
      have := inv_norm_sq_le hc hxc hxR r
      rw [div_eq_mul_inv] at this
      exact this)
    ((integrable_inv_one_add_sq hW).const_mul N)
    (Eventually.of_forall fun r x hx =>
      hasDerivAt_herglotzKernel (lt_of_lt_of_le hc (hball x hx).1) r)
  exact key.2

theorem differentiableOn_herglotzFunction {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    DifferentiableOn ℂ (herglotzFunction hW) {z | 0 < z.re} := fun _ hz =>
  (hasDerivAt_herglotzFunction hW hz).differentiableAt.differentiableWithinAt

theorem re_herglotzKernel {z : ℂ} (hz : 0 < z.re) (r : ℝ) :
    (herglotzKernel z r).re = z.re * ‖1 / (z - I * (r : ℂ))‖ ^ 2 := by
  have h1 := sub_I_mul_ne_zero hz r
  unfold herglotzKernel
  have hq : (1 + (r : ℂ) ^ 2) = ((1 + r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.sub_re, hq, Complex.div_ofReal_re]
  have him : (I * (r : ℂ)).re = 0 := by simp
  rw [him, zero_div, sub_zero, one_div, Complex.inv_re, norm_inv, inv_pow, Complex.sq_norm,
    re_sub_I_mul_ofReal]
  ring

theorem re_herglotzFunction {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z : ℂ} (hz : 0 < z.re) :
    (herglotzFunction hW z).re = z.re * (∫⁻ r, poissonDensity z r ∂boundaryMeasure hW).toReal := by
  unfold herglotzFunction
  rw [← RCLike.re_eq_complex_re, ← integral_re (integrable_herglotzKernel hW hz)]
  simp only [RCLike.re_eq_complex_re]
  simp_rw [re_herglotzKernel hz]
  rw [integral_const_mul]
  congr 1
  rw [← integral_toReal (measurable_poissonDensity z).aemeasurable
    (Eventually.of_forall fun r => ENNReal.coe_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp [poissonDensity]

theorem re_herglotzFunction_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z : ℂ}
    (hz : 0 < z.re) : 0 ≤ (herglotzFunction hW z).re := by
  rw [re_herglotzFunction hW hz]
  exact mul_nonneg hz.le ENNReal.toReal_nonneg

/-- On `Re s > 1` the real parts of `Φ_lam(s)` and `H(s − ½)` agree. -/
theorem re_herglotzFunction_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    (herglotzFunction hW (s - 1 / 2)).re = (weilFunction lam s).re := by
  have hw0 : 0 < (s - 1 / 2).re := by norm_num; linarith
  rw [re_herglotzFunction hW hw0, lintegral_poissonDensity_eq hW hs,
    ENNReal.toReal_ofReal (div_nonneg (re_weilFunction_nonneg hW hs) hw0.le)]
  have hne : (s - 1 / 2).re ≠ 0 := hw0.ne'
  rw [mul_div_assoc']
  exact mul_div_cancel_left₀ _ hne

/-! ## A holomorphic function with vanishing real part is constant -/

theorem deriv_eq_zero_of_re_eq_zero {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hre : ∀ z ∈ U, (g z).re = 0) {x : ℂ} (hx : x ∈ U) {g' : ℂ} (hg : HasDerivAt g g' x) :
    g' = 0 := by
  -- the real direction
  have h1 : HasDerivAt (fun w : ℂ => g (x + w)) g' ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact HasDerivAt.comp_const_add x 0 (by simpa using hg)
  have h1r := h1.real_of_complex
  have hev1 : (fun t : ℝ => (g (x + (t : ℂ))).re) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    have hcont : Continuous fun t : ℝ => x + (t : ℂ) := by fun_prop
    have hmem : (fun t : ℝ => x + (t : ℂ)) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
    filter_upwards [hmem] with t ht
    exact hre _ ht
  have hre0 : g'.re = 0 :=
    h1r.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev1)
  -- the imaginary direction
  have h2 : HasDerivAt (fun w : ℂ => g (x + I * w)) (g' * I) ((0 : ℝ) : ℂ) := by
    have hlin : HasDerivAt (fun w : ℂ => x + I * w) I ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul I).const_add x
    have hg' : HasDerivAt g g' ((fun w : ℂ => x + I * w) ((0 : ℝ) : ℂ)) := by simpa using hg
    exact HasDerivAt.comp (h := fun w : ℂ => x + I * w) ((0 : ℝ) : ℂ) hg' hlin
  have h2r := h2.real_of_complex
  have hev2 : (fun t : ℝ => (g (x + I * (t : ℂ))).re) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    have hcont : Continuous fun t : ℝ => x + I * (t : ℂ) := by fun_prop
    have hmem : (fun t : ℝ => x + I * (t : ℂ)) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
    filter_upwards [hmem] with t ht
    exact hre _ ht
  have him0 : (g' * I).re = 0 :=
    h2r.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev2)
  rw [Complex.mul_re, Complex.I_re, Complex.I_im] at him0
  apply Complex.ext
  · simpa using hre0
  · simp at him0
    simpa using him0

theorem eq_of_re_eq_zero {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hg : DifferentiableOn ℂ g U) (hre : ∀ z ∈ U, (g z).re = 0) {x y : ℂ} (hx : x ∈ U)
    (hy : y ∈ U) : g x = g y := by
  refine hUc.is_const_of_fderivWithin_eq_zero hg (fun z hz => ?_) hx hy
  rw [fderivWithin_of_isOpen hU hz]
  have hd := (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have h0 := deriv_eq_zero_of_re_eq_zero hU hre hz hd
  rw [hd.hasFDerivAt.fderiv, h0]
  ext
  simp

/-! ## Holomorphy of the Weil function on `Re s > 1` -/

theorem differentiableAt_weilFunction {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 < s.re) : DifferentiableAt ℂ (weilFunction lam) s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hdig : DifferentiableAt ℂ (fun s : ℂ => Complex.digamma (s / 2)) s := by
    have h2 : 0 < (s / 2).re := by
      rw [Complex.div_ofNat_re]
      linarith
    exact (differentiableAt_digamma_of_re_pos h2).comp s
      ((differentiableAt_id).div_const 2)
  have habs : LSeries.abscissaOfAbsConv (lamC lam) < s.re := by
    refine lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (x := 1) fun y hy => ?_) (by exact_mod_cast hs)
    exact summable_term_lamC hW (by simpa using hy)
  have hL := (LSeries_hasDerivAt habs).differentiableAt
  unfold weilFunction
  refine ((((hdig.div_const 2).sub (differentiableAt_const _)).add
    ((differentiableAt_const _).div differentiableAt_id hs0)).add
    ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) hs1)).sub hL

/-! ## The continuation -/

/-- The continuation `s ↦ H(s − ½) + (Φ_lam(2) − H(3/2))`. -/
def weilContinuation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  herglotzFunction hW (s - 1 / 2) + (weilFunction lam 2 - herglotzFunction hW (2 - 1 / 2))

theorem weilContinuation_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    weilContinuation hW s = weilFunction lam s := by
  set U : Set ℂ := {z | 1 < z.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ U := convex_halfSpace_re_gt 1
  set g : ℂ → ℂ := fun z => weilFunction lam z - herglotzFunction hW (z - 1 / 2) with hg
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hz' : 1 < z.re := hz
    have hh : DifferentiableAt ℂ (fun z => herglotzFunction hW (z - 1 / 2)) z := by
      have hpos : 0 < (z - 1 / 2).re := by norm_num; linarith
      have hH : DifferentiableAt ℂ (herglotzFunction hW) (z - 1 / 2) :=
        (hasDerivAt_herglotzFunction hW hpos).differentiableAt
      exact DifferentiableAt.comp (g := herglotzFunction hW) (f := fun z : ℂ => z - 1 / 2) z hH
        (by fun_prop)
    exact ((differentiableAt_weilFunction hW hz').sub hh).differentiableWithinAt
  have hgre : ∀ z ∈ U, (g z).re = 0 := by
    intro z hz
    simp only [hg, Complex.sub_re]
    rw [re_herglotzFunction_eq hW hz]
    ring
  have h2 : (2 : ℂ) ∈ U := by
    show 1 < (2 : ℂ).re
    norm_num
  have hconst := eq_of_re_eq_zero hU hUc hgd hgre hs h2
  simp only [hg] at hconst
  unfold weilContinuation
  linear_combination -hconst

theorem re_weilContinuation_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 / 2 < s.re) : 0 ≤ (weilContinuation hW s).re := by
  have h2 : (weilFunction lam 2 - herglotzFunction hW (2 - 1 / 2)).re = 0 := by
    rw [Complex.sub_re, re_herglotzFunction_eq hW (by norm_num)]
    ring
  unfold weilContinuation
  rw [Complex.add_re, h2, add_zero]
  exact re_herglotzFunction_nonneg hW (by norm_num; linarith)

theorem differentiableOn_weilContinuation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    DifferentiableOn ℂ (weilContinuation hW) {s | 1 / 2 < s.re} := by
  intro s hs
  have hs' : 1 / 2 < s.re := hs
  have hpos : 0 < (s - 1 / 2).re := by norm_num; linarith
  have hH : DifferentiableAt ℂ (herglotzFunction hW) (s - 1 / 2) :=
    (hasDerivAt_herglotzFunction hW hpos).differentiableAt
  exact ((DifferentiableAt.comp (g := herglotzFunction hW) (f := fun z : ℂ => z - 1 / 2) s hH
    (by fun_prop)).add_const _).differentiableWithinAt

/-! ## The bridge -/

/-- **Full-cone Weil positivity implies Herglotz–Weil positivity for ζ's datum.** -/
theorem herglotzWeilPositive_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    HerglotzWeilPositive (fun n => if 2 ≤ n then lam n else 0) zetaArchimedeanDatum where
  summable σ hσ := by
    refine (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ).of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    split_ifs
    · exact le_rfl
    · simp only [abs_zero, zero_div]
      positivity
  herglotz := by
    refine ⟨weilContinuation hW, differentiableOn_weilContinuation hW,
      fun s hs => re_weilContinuation_nonneg hW hs, fun s hs => ?_⟩
    rw [weilContinuation_eq hW hs, weilFunction, zetaArchimedeanDatum]
    rfl

/-- **Prime-supported Weil-positive systems force primes in short intervals.**  If `lam` is
full-cone Weil-positive and vanishes off the primes, then every interval `(x, x + x^{1/2+ε})`
with `x` large contains a prime. -/
theorem exists_prime_mem_Ioo_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hsupp : ∀ n : ℕ, lam n ≠ 0 → n.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < x + x ^ (1 / 2 + ε) := by
  refine exists_prime_mem_Ioo_of_zetaWeilPositive (herglotzWeilPositive_of_weilPositiveFull hW)
    (fun n hn => ?_) hε
  split_ifs at hn with h
  · exact hsupp n hn
  · exact absurd rfl hn

end RHTower.WeilSpectral

end
