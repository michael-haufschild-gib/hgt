import Mathlib

open Real Complex MeasureTheory Filter Topology Asymptotics
open scoped FourierTransform

/-!
# The Poincaré kernel on a horizontal line and its Poisson summation

For `β ≥ 0`, `y > 0` and `s ∈ ℂ` let `w = x + iy` and
`ker(x) = (y/(x² + y²))^s · exp(-2πiβ/w)`. The phase has modulus at most one, so
`|ker| ≤ (y/(x²+y²))^σ` (`norm_ker_le`), `σ = Re s`. With `g = s log(y/(x²+y²)) - 2πiβ/w`,
`ker' = g' ker` and `ker'' = (g'' + g'²) ker`, where `|g'| ≤ |s|/y + 2πβ/y²` and
`|g''| ≤ 2|s|/y² + 4πβ/y³` (`norm_deriv_ker_le`, `norm_deriv2_ker_le`).

For `σ > 1/2`, `∫ (y/(x²+y²))^σ dx = y^{1-σ} C_σ` with `C_σ = ∫ (1+t²)^{-σ}` (`integral_wt_rpow`), so
`|𝓕 ker(ξ)| ≤ y^{1-σ} C_σ` and `|𝓕 ker(ξ)| ≤ D y^{-1-σ} C_σ / (2πξ)²` (`norm_fourier_ker_le`,
`norm_fourier_ker_le_sq`). For `σ ≥ 3/4` Poisson summation holds pointwise
(`tsum_ker_eq_tsum_fourier`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPoincareKernel

noncomputable section

/-- `w = x + iy`. -/
def wz (y x : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

/-- The hyperbolic weight `y/(x² + y²)`. -/
def wt (y x : ℝ) : ℝ := y / (x ^ 2 + y ^ 2)

/-- The kernel `(y/(x²+y²))^s · exp(-2πiβ/(x+iy))`. -/
def ker (β y : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  cexp (s * (Real.log (wt y x) : ℂ) - 2 * π * I * β * (wz y x)⁻¹)

variable {β y : ℝ} {s : ℂ}

theorem wz_im (y x : ℝ) : (wz y x).im = y := by simp [wz]

theorem wz_ne_zero (hy : 0 < y) (x : ℝ) : wz y x ≠ 0 := by
  intro h; have := wz_im y x; rw [h] at this; simp at this; linarith

theorem normSq_wz (y x : ℝ) : Complex.normSq (wz y x) = x ^ 2 + y ^ 2 := by
  simp [wz, Complex.normSq_apply]; ring

theorem norm_wz_ge (hy : 0 < y) (x : ℝ) : y ≤ ‖wz y x‖ := by
  have h := normSq_wz y x
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (wz y x), sq_nonneg x]

theorem wt_pos (hy : 0 < y) (x : ℝ) : 0 < wt y x := by unfold wt; positivity

theorem wt_le (hy : 0 < y) (x : ℝ) : wt y x ≤ 1 / y := by
  unfold wt
  rw [div_le_div_iff₀ (by positivity) hy]
  nlinarith [sq_nonneg x]

theorem re_phase_nonpos (hβ : 0 ≤ β) (hy : 0 < y) (x : ℝ) :
    (-(2 * π * I * β * (wz y x)⁻¹)).re ≤ 0 := by
  have e : (-(2 * π * I * β * (wz y x)⁻¹)).re = 2 * π * β * ((wz y x)⁻¹).im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [e, Complex.inv_im, wz_im, normSq_wz]
  have : 0 ≤ y / (x ^ 2 + y ^ 2) := by positivity
  have : 0 ≤ 2 * π * β := by positivity
  rw [neg_div]; nlinarith

/-- `|ker| ≤ (y/(x²+y²))^σ`. -/
theorem norm_ker_le (hβ : 0 ≤ β) (hy : 0 < y) (s : ℂ) (x : ℝ) : ‖ker β y s x‖ ≤ wt y x ^ s.re := by
  unfold ker
  rw [Complex.norm_exp, Real.rpow_def_of_pos (wt_pos hy x)]
  apply Real.exp_le_exp.mpr
  have h := re_phase_nonpos hβ hy x
  rw [sub_eq_add_neg, Complex.add_re]
  have : (s * (Real.log (wt y x) : ℂ)).re = Real.log (wt y x) * s.re := by
    rw [Complex.mul_re]; simp; ring
  linarith

/-! ### Derivatives -/

/-- `L' = d/dx log(y/(x²+y²)) = -2x/(x²+y²)`. -/
def L1 (y x : ℝ) : ℝ := -(2 * x) / (x ^ 2 + y ^ 2)

/-- `L'' = 2(x² - y²)/(x²+y²)²`. -/
def L2 (y x : ℝ) : ℝ := 2 * (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2

/-- `g' = s L' + 2πiβ/w²`. -/
def g1 (β y : ℝ) (s : ℂ) (x : ℝ) : ℂ := s * (L1 y x : ℂ) + 2 * π * I * β * ((wz y x) ^ 2)⁻¹

/-- `g'' = s L'' - 4πiβ/w³`. -/
def g2 (β y : ℝ) (s : ℂ) (x : ℝ) : ℂ := s * (L2 y x : ℂ) - 4 * π * I * β * ((wz y x) ^ 3)⁻¹

theorem hasDerivAt_wz (y x : ℝ) : HasDerivAt (wz y) 1 x := by
  have h := ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
  exact h.congr_deriv (by simp)

theorem hasDerivAt_log_wt (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => Real.log (wt y t)) (L1 y x) x := by
  have hq : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
  have hne : x ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hw : HasDerivAt (wt y) ((0 * (x ^ 2 + y ^ 2) - y * (2 * x)) / (x ^ 2 + y ^ 2) ^ 2) x :=
    (hasDerivAt_const x y).div hq hne
  exact (hw.log (wt_pos hy x).ne').congr_deriv (by unfold L1 wt; field_simp; ring)

theorem hasDerivAt_L1 (hy : 0 < y) (x : ℝ) : HasDerivAt (L1 y) (L2 y x) x := by
  have hq : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
  have hne : x ^ 2 + y ^ 2 ≠ 0 := by positivity
  have h2 : HasDerivAt (fun t : ℝ => -(2 * t)) (-(2 * 1)) x := ((hasDerivAt_id' x).const_mul 2).neg
  exact (h2.div hq hne).congr_deriv (by unfold L2; field_simp; ring)

theorem hasDerivAt_ker (hy : 0 < y) (x : ℝ) :
    HasDerivAt (ker β y s) (g1 β y s x * ker β y s x) x := by
  have hw := hasDerivAt_wz y x
  have hinv := hw.inv (wz_ne_zero hy x)
  have hL := (hasDerivAt_log_wt hy x).ofReal_comp
  have hg := (hL.const_mul s).sub (hinv.const_mul (2 * π * I * β))
  refine hg.cexp.congr_deriv ?_
  simp only [g1, ker, Pi.sub_apply, Pi.inv_apply]
  rw [neg_div, one_div]
  ring

theorem hasDerivAt_g1 (hy : 0 < y) (x : ℝ) : HasDerivAt (g1 β y s) (g2 β y s x) x := by
  have hw := hasDerivAt_wz y x
  have hw2 := (hw.pow 2).inv (pow_ne_zero 2 (wz_ne_zero hy x))
  have hL := (hasDerivAt_L1 hy x).ofReal_comp
  refine ((hL.const_mul s).add (hw2.const_mul (2 * π * I * β))).congr_deriv ?_
  have hz := wz_ne_zero hy x
  simp only [g2, Pi.pow_apply]
  field_simp
  ring

theorem hasDerivAt_g1_ker (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => g1 β y s t * ker β y s t)
      ((g2 β y s x + g1 β y s x ^ 2) * ker β y s x) x := by
  exact ((hasDerivAt_g1 (β := β) (s := s) hy x).mul (hasDerivAt_ker (β := β) (s := s) hy x)).congr_deriv
    (by ring)

theorem deriv_ker (hy : 0 < y) : deriv (ker β y s) = fun x => g1 β y s x * ker β y s x :=
  funext fun x => (hasDerivAt_ker hy x).deriv

theorem deriv2_ker (hy : 0 < y) :
    deriv (deriv (ker β y s)) = fun x => (g2 β y s x + g1 β y s x ^ 2) * ker β y s x := by
  rw [deriv_ker hy]
  exact funext fun x => (hasDerivAt_g1_ker hy x).deriv

theorem abs_L1_le (hy : 0 < y) (x : ℝ) : |L1 y x| ≤ 1 / y := by
  unfold L1
  rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < x ^ 2 + y ^ 2), div_le_div_iff₀ (by positivity) hy]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sq_nonneg (|x| - y), sq_abs x, abs_nonneg x]

theorem abs_L2_le (hy : 0 < y) (x : ℝ) : |L2 y x| ≤ 2 / y ^ 2 := by
  unfold L2
  have hp : 0 < x ^ 2 + y ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : 0 < (x ^ 2 + y ^ 2) ^ 2), div_le_div_iff₀ (by positivity) (by positivity)]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 : |x ^ 2 - y ^ 2| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  have h2 : y ^ 2 ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg x]
  calc 2 * |x ^ 2 - y ^ 2| * y ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) * (x ^ 2 + y ^ 2) := by
        gcongr
    _ = 2 * (x ^ 2 + y ^ 2) ^ 2 := by ring

theorem norm_inv_wz_pow_le (hy : 0 < y) (x : ℝ) (k : ℕ) : ‖((wz y x) ^ k)⁻¹‖ ≤ 1 / y ^ k := by
  rw [norm_inv, norm_pow, one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hy.le (norm_wz_ge hy x) k)

/-- `|g'| ≤ |s|/y + 2πβ/y²`. -/
theorem norm_g1_le (hβ : 0 ≤ β) (hy : 0 < y) (x : ℝ) :
    ‖g1 β y s x‖ ≤ ‖s‖ / y + 2 * π * β / y ^ 2 := by
  unfold g1
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s‖ * |L1 y x| ≤ ‖s‖ * (1 / y) := mul_le_mul_of_nonneg_left (abs_L1_le hy x) (norm_nonneg _)
      _ = ‖s‖ / y := by ring
  · have h := norm_inv_wz_pow_le hy x 2
    have : ‖2 * (π : ℂ) * I * (β : ℂ)‖ = 2 * π * β := by
      simp [abs_of_nonneg hβ, abs_of_pos Real.pi_pos]
    rw [norm_mul, this]
    calc 2 * π * β * ‖(wz y x ^ 2)⁻¹‖ ≤ 2 * π * β * (1 / y ^ 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * π * β / y ^ 2 := by ring

/-- `|g''| ≤ 2|s|/y² + 4πβ/y³`. -/
theorem norm_g2_le (hβ : 0 ≤ β) (hy : 0 < y) (x : ℝ) :
    ‖g2 β y s x‖ ≤ 2 * ‖s‖ / y ^ 2 + 4 * π * β / y ^ 3 := by
  unfold g2
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s‖ * |L2 y x| ≤ ‖s‖ * (2 / y ^ 2) := mul_le_mul_of_nonneg_left (abs_L2_le hy x) (norm_nonneg _)
      _ = 2 * ‖s‖ / y ^ 2 := by ring
  · have h := norm_inv_wz_pow_le hy x 3
    have : ‖4 * (π : ℂ) * I * (β : ℂ)‖ = 4 * π * β := by
      simp [abs_of_nonneg hβ, abs_of_pos Real.pi_pos]
    rw [norm_mul, this]
    calc 4 * π * β * ‖(wz y x ^ 3)⁻¹‖ ≤ 4 * π * β * (1 / y ^ 3) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 4 * π * β / y ^ 3 := by ring

/-- The second-derivative constant `D = (|s|/y + 2πβ/y²)² + 2|s|/y² + 4πβ/y³`. -/
def dconst (β y : ℝ) (s : ℂ) : ℝ := (‖s‖ / y + 2 * π * β / y ^ 2) ^ 2 + (2 * ‖s‖ / y ^ 2 + 4 * π * β / y ^ 3)

theorem norm_deriv_ker_le (hβ : 0 ≤ β) (hy : 0 < y) (x : ℝ) :
    ‖deriv (ker β y s) x‖ ≤ (‖s‖ / y + 2 * π * β / y ^ 2) * wt y x ^ s.re := by
  rw [deriv_ker hy, norm_mul]
  exact mul_le_mul (norm_g1_le hβ hy x) (norm_ker_le hβ hy s x) (norm_nonneg _) (by positivity)

theorem norm_deriv2_ker_le (hβ : 0 ≤ β) (hy : 0 < y) (x : ℝ) :
    ‖deriv (deriv (ker β y s)) x‖ ≤ dconst β y s * wt y x ^ s.re := by
  rw [deriv2_ker hy, norm_mul]
  apply mul_le_mul _ (norm_ker_le hβ hy s x) (norm_nonneg _) (by unfold dconst; positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_pow]
  unfold dconst
  have h1 := norm_g1_le (s := s) hβ hy x
  have h2 := norm_g2_le (s := s) hβ hy x
  nlinarith [norm_nonneg (g1 β y s x), pow_le_pow_left₀ (norm_nonneg _) h1 2]

/-! ### Integrals -/

/-- `C_σ = ∫ (1 + t²)^{-σ}`. -/
def cst (σ : ℝ) : ℝ := ∫ t : ℝ, (1 + t ^ 2) ^ (-σ)

theorem integrable_one_add_sq {σ : ℝ} (hσ : 1 / 2 < σ) : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-σ)) := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * σ) (by simp; linarith)
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1; ring

theorem wt_rpow_eq (hy : 0 < y) (σ x : ℝ) : wt y x ^ σ = y ^ (-σ) * (1 + (x / y) ^ 2) ^ (-σ) := by
  have h : wt y x = (y * (1 + (x / y) ^ 2))⁻¹ := by
    unfold wt; field_simp; ring
  rw [h, Real.inv_rpow (by positivity), Real.mul_rpow hy.le (by positivity), Real.rpow_neg hy.le,
    Real.rpow_neg (by positivity)]
  rw [mul_inv]

theorem integrable_wt_rpow (hy : 0 < y) {σ : ℝ} (hσ : 1 / 2 < σ) : Integrable (fun x => wt y x ^ σ) := by
  have := ((integrable_one_add_sq hσ).comp_div hy.ne').const_mul (y ^ (-σ))
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [wt_rpow_eq hy]

theorem integral_wt_rpow (hy : 0 < y) (σ : ℝ) : ∫ x, wt y x ^ σ = y ^ (1 - σ) * cst σ := by
  simp only [wt_rpow_eq hy]
  rw [integral_const_mul, Measure.integral_comp_div (fun t => (1 + t ^ 2) ^ (-σ)) y, abs_of_pos hy, smul_eq_mul,
    ← mul_assoc, cst]
  congr 1
  rw [Real.rpow_sub hy, Real.rpow_one, Real.rpow_neg hy.le]
  field_simp

theorem cst_nonneg (σ : ℝ) : 0 ≤ cst σ := integral_nonneg fun t => by positivity

/-! ### Fourier transform -/

theorem continuous_ker (hy : 0 < y) : Continuous (ker β y s) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_ker hy x).continuousAt

theorem integrable_ker (hβ : 0 ≤ β) (hy : 0 < y) (hs : 1 / 2 < s.re) : Integrable (ker β y s) :=
  (integrable_wt_rpow hy hs).mono' (continuous_ker hy).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_ker_le hβ hy s x)

theorem integrable_deriv_ker (hβ : 0 ≤ β) (hy : 0 < y) (hs : 1 / 2 < s.re) :
    Integrable (deriv (ker β y s)) := by
  refine ((integrable_wt_rpow hy hs).const_mul (‖s‖ / y + 2 * π * β / y ^ 2)).mono' ?_
    (Eventually.of_forall fun x => norm_deriv_ker_le hβ hy x)
  rw [deriv_ker hy]
  exact (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_g1_ker hy x).continuousAt).aestronglyMeasurable

theorem integrable_deriv2_ker (hβ : 0 ≤ β) (hy : 0 < y) (hs : 1 / 2 < s.re) :
    Integrable (deriv (deriv (ker β y s))) := by
  refine ((integrable_wt_rpow hy hs).const_mul (dconst β y s)).mono' ?_
    (Eventually.of_forall fun x => norm_deriv2_ker_le hβ hy x)
  rw [deriv2_ker hy]
  have hc1 : Continuous (g1 β y s) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_g1 hy x).continuousAt
  have hcw : Continuous (wz y) := by unfold wz; fun_prop
  have hc2 : Continuous (g2 β y s) := by
    have hL : Continuous (L2 y) := by
      unfold L2
      exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
    have hi : Continuous (fun x => ((wz y x) ^ 3)⁻¹) :=
      (hcw.pow 3).inv₀ (fun x => pow_ne_zero 3 (wz_ne_zero hy x))
    unfold g2
    exact (continuous_const.mul (Complex.continuous_ofReal.comp hL)).sub (continuous_const.mul hi)
  exact ((hc2.add (hc1.pow 2)).mul (continuous_ker hy)).aestronglyMeasurable

theorem norm_fourier_le_integral {f : ℝ → ℂ} (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext x
  rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

/-- `|𝓕 ker(ξ)| ≤ y^{1-σ} C_σ`. -/
theorem norm_fourier_ker_le (hβ : 0 ≤ β) (hy : 0 < y) (hs : 1 / 2 < s.re) (ξ : ℝ) :
    ‖𝓕 (ker β y s) ξ‖ ≤ y ^ (1 - s.re) * cst s.re := by
  refine (norm_fourier_le_integral ξ).trans ?_
  rw [← integral_wt_rpow hy]
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) (integrable_wt_rpow hy hs)
    (Eventually.of_forall fun x => norm_ker_le hβ hy s x)

/-- `(2πξ)² |𝓕 ker(ξ)| ≤ D y^{1-σ} C_σ`. -/
theorem norm_fourier_ker_le_sq (hβ : 0 ≤ β) (hy : 0 < y) (hs : 1 / 2 < s.re) (ξ : ℝ) :
    (2 * π * |ξ|) ^ 2 * ‖𝓕 (ker β y s) ξ‖ ≤ dconst β y s * (y ^ (1 - s.re) * cst s.re) := by
  have hd1 := Real.fourier_deriv (integrable_ker hβ hy hs)
    (fun x => (hasDerivAt_ker hy x).differentiableAt) (integrable_deriv_ker hβ hy hs)
  have hd2 := Real.fourier_deriv (integrable_deriv_ker hβ hy hs)
    (fun x => by rw [deriv_ker hy]; exact (hasDerivAt_g1_ker hy x).differentiableAt)
    (integrable_deriv2_ker hβ hy hs)
  have h : 𝓕 (deriv (deriv (ker β y s))) ξ = (2 * π * I * ξ) ^ 2 * 𝓕 (ker β y s) ξ := by
    rw [hd2, hd1]; simp only [smul_eq_mul]; ring
  have hn : ‖(2 * (π : ℂ) * I * ξ) ^ 2‖ = (2 * π * |ξ|) ^ 2 := by
    rw [norm_pow]; simp [abs_of_pos Real.pi_pos]
  rw [← hn, ← norm_mul, ← h]
  refine (norm_fourier_le_integral ξ).trans ?_
  rw [← integral_wt_rpow hy, ← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
    ((integrable_wt_rpow hy hs).const_mul _) (Eventually.of_forall fun x => norm_deriv2_ker_le hβ hy x)

/-! ### Poisson summation -/

theorem mem_cocompact_one : {x : ℝ | 1 ≤ |x|} ∈ cocompact ℝ :=
  Filter.mem_of_superset (isCompact_closedBall (0 : ℝ) 1).compl_mem_cocompact (fun x hx => by
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    exact hx.le)

theorem ker_isBigO (hβ : 0 ≤ β) (hy : 0 < y) (hs : 3 / 4 ≤ s.re) :
    ker β y s =O[cocompact ℝ] fun x => |x| ^ (-(3 / 2 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨y ^ s.re, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{x | 1 ≤ |x|}, mem_cocompact_one, fun x hx => ?_⟩
  · simp only [Set.mem_setOf_eq] at hx
    have hx0 : 0 < |x| := lt_of_lt_of_le one_pos hx
    refine (norm_ker_le hβ hy s x).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hw : wt y x ≤ y / |x| ^ 2 := by
      unfold wt
      exact div_le_div_of_nonneg_left hy.le (by positivity) (by rw [sq_abs]; nlinarith [sq_nonneg y])
    calc wt y x ^ s.re ≤ (y / |x| ^ 2) ^ s.re := Real.rpow_le_rpow (wt_pos hy x).le hw (by linarith)
      _ = y ^ s.re * |x| ^ (-(2 * s.re)) := by
          rw [Real.div_rpow hy.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
            Real.rpow_neg (abs_nonneg _), div_eq_mul_inv]
          norm_num
      _ ≤ y ^ s.re * |x| ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by positivity)

theorem fourier_ker_isBigO (hβ : 0 ≤ β) (hy : 0 < y) (hs : 3 / 4 ≤ s.re) :
    𝓕 (ker β y s) =O[cocompact ℝ] fun x => |x| ^ (-(3 / 2 : ℝ)) := by
  have hs' : 1 / 2 < s.re := by linarith
  rw [Asymptotics.isBigO_iff]
  refine ⟨dconst β y s * (y ^ (1 - s.re) * cst s.re) / (2 * π) ^ 2, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{x | 1 ≤ |x|}, mem_cocompact_one, fun x hx => ?_⟩
  · simp only [Set.mem_setOf_eq] at hx
    have hx0 : 0 < |x| := lt_of_lt_of_le one_pos hx
    have h := norm_fourier_ker_le_sq hβ hy hs' x
    have hD : 0 ≤ dconst β y s * (y ^ (1 - s.re) * cst s.re) := by
      unfold dconst; have := cst_nonneg s.re; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hsq : |x| ^ (-(3 / 2 : ℝ)) ≥ (|x| ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (abs_nonneg _)]
      exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have hpi : 0 < (2 * π) ^ 2 := by positivity
    have hF : ‖𝓕 (ker β y s) x‖ ≤ dconst β y s * (y ^ (1 - s.re) * cst s.re) / (2 * π) ^ 2 * (|x| ^ 2)⁻¹ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖𝓕 (ker β y s) x‖ * (2 * π) ^ 2 * |x| ^ 2 = (2 * π * |x|) ^ 2 * ‖𝓕 (ker β y s) x‖ := by ring
        _ ≤ _ := h
    exact hF.trans (mul_le_mul_of_nonneg_left hsq (by positivity))

/-- **Poisson summation** for the kernel, `Re s ≥ 3/4`. -/
theorem tsum_ker_eq_tsum_fourier (hβ : 0 ≤ β) (hy : 0 < y) (hs : 3 / 4 ≤ s.re) (x : ℝ) :
    ∑' n : ℤ, ker β y s (x + n) = ∑' n : ℤ, 𝓕 (ker β y s) n * fourier n (x : UnitAddCircle) :=
  Real.tsum_eq_tsum_fourier_of_rpow_decay (continuous_ker hy) (by norm_num) (ker_isBigO hβ hy hs)
    (fourier_ker_isBigO hβ hy hs) x

end

end GaloisForLFunctions.RHTower.SelbergPoincareKernel
