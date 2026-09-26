import GaloisForLFunctions.RHTower.SelbergPoincareKernel

/-!
# The weight-½ Eisenstein kernel on a horizontal line

For `y > 0` and `s ∈ ℂ` the kernel of the weight-½ Eisenstein series along `Im = y` is
`kerH(x) = e^{-i arg(x+iy)/2} (y/(x²+y²))^s`, the value of `\overline{j(γ, ·)} Im(γ ·)^s` on a
translate (with `arg(x+iy) = Im log(x+iy)`, derivative `-y/(x²+y²)`).

* `norm_kerH`: `|kerH(x)| = (y/(x²+y²))^{Re s}` exactly (the phase is unimodular).
* `hasDerivAt_kerH`, `deriv2_kerH`: `kerH' = g' kerH`, `kerH'' = (g'' + g'²) kerH` with
  `|g'| ≤ |s|/y + 1/(2y)` and `|g''| ≤ 2|s|/y² + 1/(2y²)`.
* `norm_fourier_kerH_le`, `norm_fourier_kerH_le_sq`: `|𝓕 kerH(ξ)| ≤ y^{1-σ} C_σ` and
  `(2πξ)² |𝓕 kerH(ξ)| ≤ D y^{1-σ} C_σ` for `σ = Re s > 1/2`.
* `tsum_kerH_eq_tsum_fourier`: Poisson summation pointwise for `Re s ≥ 3/4`.

The weight-0 analogues (`wt`, `L1`, `L2`, `C_σ`) are reused from `SelbergPoincareKernel`.
-/

open Real Complex MeasureTheory Filter Topology Asymptotics
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.SelbergPoincareKernel

noncomputable section

variable {y : ℝ} {s : ℂ}

/-- The argument `arg(x + iy)` as a real function of `x`. -/
def argW (y x : ℝ) : ℝ := (Complex.log (wz y x)).im

/-- The weight-½ kernel `e^{-i arg(x+iy)/2} (y/(x²+y²))^s`. -/
def kerH (y : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  cexp (s * (Real.log (wt y x) : ℂ) - I / 2 * (argW y x : ℂ))

/-- `d/dx arg(x+iy) = -y/(x²+y²)`. -/
def A1 (y x : ℝ) : ℝ := -y / (x ^ 2 + y ^ 2)

/-- `d²/dx² arg(x+iy) = 2xy/(x²+y²)²`. -/
def A2 (y x : ℝ) : ℝ := 2 * x * y / (x ^ 2 + y ^ 2) ^ 2

theorem wz_mem_slitPlane (hy : 0 < y) (x : ℝ) : wz y x ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr (by rw [wz_im]; exact hy.ne'))

theorem hasDerivAt_argW (hy : 0 < y) (x : ℝ) : HasDerivAt (argW y) (A1 y x) x := by
  have hl := (hasDerivAt_wz y x).clog_real (wz_mem_slitPlane hy x)
  have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hl)
  refine him.congr_deriv ?_
  simp only [Complex.imCLM_apply, A1]
  rw [one_div, Complex.inv_im, wz_im, normSq_wz]

theorem hasDerivAt_A1 (hy : 0 < y) (x : ℝ) : HasDerivAt (A1 y) (A2 y x) x := by
  have hq : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
  have hne : x ^ 2 + y ^ 2 ≠ 0 := by positivity
  exact ((hasDerivAt_const x (-y)).div hq hne).congr_deriv (by unfold A2; field_simp; ring)

/-- `g' = s L' - (i/2) A'`. -/
def gH1 (y : ℝ) (s : ℂ) (x : ℝ) : ℂ := s * (L1 y x : ℂ) - I / 2 * (A1 y x : ℂ)

/-- `g'' = s L'' - (i/2) A''`. -/
def gH2 (y : ℝ) (s : ℂ) (x : ℝ) : ℂ := s * (L2 y x : ℂ) - I / 2 * (A2 y x : ℂ)

theorem hasDerivAt_kerH (hy : 0 < y) (x : ℝ) :
    HasDerivAt (kerH y s) (gH1 y s x * kerH y s x) x := by
  have hL := (hasDerivAt_log_wt hy x).ofReal_comp
  have hA := (hasDerivAt_argW hy x).ofReal_comp
  have hg := (hL.const_mul s).sub (hA.const_mul (I / 2))
  refine hg.cexp.congr_deriv ?_
  simp only [gH1, kerH, Pi.sub_apply]
  ring

theorem hasDerivAt_gH1 (hy : 0 < y) (x : ℝ) : HasDerivAt (gH1 y s) (gH2 y s x) x := by
  have hL := (hasDerivAt_L1 hy x).ofReal_comp
  have hA := (hasDerivAt_A1 hy x).ofReal_comp
  exact ((hL.const_mul s).sub (hA.const_mul (I / 2))).congr_deriv (by simp only [gH2])

theorem hasDerivAt_gH1_kerH (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => gH1 y s t * kerH y s t) ((gH2 y s x + gH1 y s x ^ 2) * kerH y s x) x :=
  ((hasDerivAt_gH1 (s := s) hy x).mul (hasDerivAt_kerH (s := s) hy x)).congr_deriv (by ring)

theorem deriv_kerH (hy : 0 < y) : deriv (kerH y s) = fun x => gH1 y s x * kerH y s x :=
  funext fun x => (hasDerivAt_kerH hy x).deriv

theorem deriv2_kerH (hy : 0 < y) :
    deriv (deriv (kerH y s)) = fun x => (gH2 y s x + gH1 y s x ^ 2) * kerH y s x := by
  rw [deriv_kerH hy]
  exact funext fun x => (hasDerivAt_gH1_kerH hy x).deriv

/-- `|kerH| = (y/(x²+y²))^σ`. -/
theorem norm_kerH (hy : 0 < y) (s : ℂ) (x : ℝ) : ‖kerH y s x‖ = wt y x ^ s.re := by
  unfold kerH
  rw [Complex.norm_exp, Real.rpow_def_of_pos (wt_pos hy x)]
  congr 1
  simp [Complex.mul_re, Complex.sub_re]
  ring

theorem abs_A1_le (hy : 0 < y) (x : ℝ) : |A1 y x| ≤ 1 / y := by
  unfold A1
  rw [abs_div, abs_neg, abs_of_pos hy, abs_of_pos (by positivity : 0 < x ^ 2 + y ^ 2),
    div_le_div_iff₀ (by positivity) hy]
  nlinarith [sq_nonneg x]

theorem abs_A2_le (hy : 0 < y) (x : ℝ) : |A2 y x| ≤ 1 / y ^ 2 := by
  unfold A2
  have hp : 0 < x ^ 2 + y ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : 0 < (x ^ 2 + y ^ 2) ^ 2),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |2 * x * y| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
  have h2 : y ^ 2 ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg x]
  calc |2 * x * y| * y ^ 2 ≤ (x ^ 2 + y ^ 2) * (x ^ 2 + y ^ 2) := by gcongr
    _ = 1 * (x ^ 2 + y ^ 2) ^ 2 := by ring

theorem norm_gH1_le (hy : 0 < y) (x : ℝ) : ‖gH1 y s x‖ ≤ ‖s‖ / y + 1 / (2 * y) := by
  unfold gH1
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s‖ * |L1 y x| ≤ ‖s‖ * (1 / y) := mul_le_mul_of_nonneg_left (abs_L1_le hy x) (norm_nonneg _)
      _ = ‖s‖ / y := by ring
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖I / 2‖ = 1 / 2 := by simp
    rw [this]
    calc 1 / 2 * |A1 y x| ≤ 1 / 2 * (1 / y) := by
          have := abs_A1_le hy x; nlinarith
      _ = 1 / (2 * y) := by field_simp

theorem norm_gH2_le (hy : 0 < y) (x : ℝ) : ‖gH2 y s x‖ ≤ 2 * ‖s‖ / y ^ 2 + 1 / (2 * y ^ 2) := by
  unfold gH2
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s‖ * |L2 y x| ≤ ‖s‖ * (2 / y ^ 2) := mul_le_mul_of_nonneg_left (abs_L2_le hy x) (norm_nonneg _)
      _ = 2 * ‖s‖ / y ^ 2 := by ring
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖I / 2‖ = 1 / 2 := by simp
    rw [this]
    calc 1 / 2 * |A2 y x| ≤ 1 / 2 * (1 / y ^ 2) := by
          have := abs_A2_le hy x; nlinarith
      _ = 1 / (2 * y ^ 2) := by field_simp

/-- The second-derivative constant. -/
def dconstH (y : ℝ) (s : ℂ) : ℝ := (‖s‖ / y + 1 / (2 * y)) ^ 2 + (2 * ‖s‖ / y ^ 2 + 1 / (2 * y ^ 2))

theorem norm_deriv_kerH_le (hy : 0 < y) (x : ℝ) :
    ‖deriv (kerH y s) x‖ ≤ (‖s‖ / y + 1 / (2 * y)) * wt y x ^ s.re := by
  rw [deriv_kerH hy, norm_mul, norm_kerH hy]
  exact mul_le_mul_of_nonneg_right (norm_gH1_le hy x) (by have := wt_pos hy x; positivity)

theorem norm_deriv2_kerH_le (hy : 0 < y) (x : ℝ) :
    ‖deriv (deriv (kerH y s)) x‖ ≤ dconstH y s * wt y x ^ s.re := by
  rw [deriv2_kerH hy, norm_mul, norm_kerH hy]
  apply mul_le_mul_of_nonneg_right _ (by have := wt_pos hy x; positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_pow]
  unfold dconstH
  have h1 := norm_gH1_le (s := s) hy x
  have h2 := norm_gH2_le (s := s) hy x
  nlinarith [norm_nonneg (gH1 y s x), pow_le_pow_left₀ (norm_nonneg _) h1 2]

/-! ### Fourier transform and Poisson summation -/

theorem continuous_argW (hy : 0 < y) : Continuous (argW y) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_argW hy x).continuousAt

theorem continuous_kerH (hy : 0 < y) : Continuous (kerH y s) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_kerH hy x).continuousAt

theorem integrable_kerH (hy : 0 < y) (hs : 1 / 2 < s.re) : Integrable (kerH y s) :=
  (integrable_wt_rpow hy hs).mono' (continuous_kerH hy).aestronglyMeasurable
    (Eventually.of_forall fun x => (norm_kerH hy s x).le)

theorem integrable_deriv_kerH (hy : 0 < y) (hs : 1 / 2 < s.re) :
    Integrable (deriv (kerH y s)) := by
  refine ((integrable_wt_rpow hy hs).const_mul (‖s‖ / y + 1 / (2 * y))).mono' ?_
    (Eventually.of_forall fun x => norm_deriv_kerH_le hy x)
  rw [deriv_kerH hy]
  exact (continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_gH1_kerH hy x).continuousAt).aestronglyMeasurable

theorem integrable_deriv2_kerH (hy : 0 < y) (hs : 1 / 2 < s.re) :
    Integrable (deriv (deriv (kerH y s))) := by
  refine ((integrable_wt_rpow hy hs).const_mul (dconstH y s)).mono' ?_
    (Eventually.of_forall fun x => norm_deriv2_kerH_le hy x)
  rw [deriv2_kerH hy]
  have hc1 : Continuous (gH1 y s) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gH1 hy x).continuousAt
  have hc2 : Continuous (gH2 y s) := by
    have hL : Continuous (L2 y) := by
      unfold L2
      exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
    have hA : Continuous (A2 y) := by
      unfold A2
      exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
    unfold gH2
    exact (continuous_const.mul (Complex.continuous_ofReal.comp hL)).sub
      (continuous_const.mul (Complex.continuous_ofReal.comp hA))
  exact ((hc2.add (hc1.pow 2)).mul (continuous_kerH hy)).aestronglyMeasurable

/-- `|𝓕 kerH(ξ)| ≤ y^{1-σ} C_σ`. -/
theorem norm_fourier_kerH_le (hy : 0 < y) (hs : 1 / 2 < s.re) (ξ : ℝ) :
    ‖𝓕 (kerH y s) ξ‖ ≤ y ^ (1 - s.re) * cst s.re := by
  refine (norm_fourier_le_integral ξ).trans ?_
  rw [← integral_wt_rpow hy]
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) (integrable_wt_rpow hy hs)
    (Eventually.of_forall fun x => (norm_kerH hy s x).le)

/-- `(2πξ)² |𝓕 kerH(ξ)| ≤ D y^{1-σ} C_σ`. -/
theorem norm_fourier_kerH_le_sq (hy : 0 < y) (hs : 1 / 2 < s.re) (ξ : ℝ) :
    (2 * π * |ξ|) ^ 2 * ‖𝓕 (kerH y s) ξ‖ ≤ dconstH y s * (y ^ (1 - s.re) * cst s.re) := by
  have hd1 := Real.fourier_deriv (integrable_kerH hy hs)
    (fun x => (hasDerivAt_kerH hy x).differentiableAt) (integrable_deriv_kerH hy hs)
  have hd2 := Real.fourier_deriv (integrable_deriv_kerH hy hs)
    (fun x => by rw [deriv_kerH hy]; exact (hasDerivAt_gH1_kerH hy x).differentiableAt)
    (integrable_deriv2_kerH hy hs)
  have h : 𝓕 (deriv (deriv (kerH y s))) ξ = (2 * π * I * ξ) ^ 2 * 𝓕 (kerH y s) ξ := by
    rw [hd2, hd1]; simp only [smul_eq_mul]; ring
  have hn : ‖(2 * (π : ℂ) * I * ξ) ^ 2‖ = (2 * π * |ξ|) ^ 2 := by
    rw [norm_pow]; simp [abs_of_pos Real.pi_pos]
  rw [← hn, ← norm_mul, ← h]
  refine (norm_fourier_le_integral ξ).trans ?_
  rw [← integral_wt_rpow hy, ← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
    ((integrable_wt_rpow hy hs).const_mul _) (Eventually.of_forall fun x => norm_deriv2_kerH_le hy x)

theorem kerH_isBigO (hy : 0 < y) (hs : 3 / 4 ≤ s.re) :
    kerH y s =O[cocompact ℝ] fun x => |x| ^ (-(3 / 2 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨y ^ s.re, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{x | 1 ≤ |x|}, mem_cocompact_one, fun x hx => ?_⟩
  · simp only [Set.mem_setOf_eq] at hx
    have hx0 : 0 < |x| := lt_of_lt_of_le one_pos hx
    rw [norm_kerH hy]
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

theorem fourier_kerH_isBigO (hy : 0 < y) (hs : 3 / 4 ≤ s.re) :
    𝓕 (kerH y s) =O[cocompact ℝ] fun x => |x| ^ (-(3 / 2 : ℝ)) := by
  have hs' : 1 / 2 < s.re := by linarith
  rw [Asymptotics.isBigO_iff]
  refine ⟨dconstH y s * (y ^ (1 - s.re) * cst s.re) / (2 * π) ^ 2, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{x | 1 ≤ |x|}, mem_cocompact_one, fun x hx => ?_⟩
  · simp only [Set.mem_setOf_eq] at hx
    have hx0 : 0 < |x| := lt_of_lt_of_le one_pos hx
    have h := norm_fourier_kerH_le_sq hy hs' x
    have hD : 0 ≤ dconstH y s * (y ^ (1 - s.re) * cst s.re) := by
      unfold dconstH; have := cst_nonneg s.re; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hsq : |x| ^ (-(3 / 2 : ℝ)) ≥ (|x| ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (abs_nonneg _)]
      exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have hpi : 0 < (2 * π) ^ 2 := by positivity
    have hF : ‖𝓕 (kerH y s) x‖ ≤ dconstH y s * (y ^ (1 - s.re) * cst s.re) / (2 * π) ^ 2 *
        (|x| ^ 2)⁻¹ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖𝓕 (kerH y s) x‖ * (2 * π) ^ 2 * |x| ^ 2 = (2 * π * |x|) ^ 2 * ‖𝓕 (kerH y s) x‖ := by ring
        _ ≤ _ := h
    exact hF.trans (mul_le_mul_of_nonneg_left hsq (by positivity))

/-- **Poisson summation** for the weight-½ kernel, `Re s ≥ 3/4`. -/
theorem tsum_kerH_eq_tsum_fourier (hy : 0 < y) (hs : 3 / 4 ≤ s.re) (x : ℝ) :
    ∑' n : ℤ, kerH y s (x + n) = ∑' n : ℤ, 𝓕 (kerH y s) n * fourier n (x : UnitAddCircle) :=
  Real.tsum_eq_tsum_fourier_of_rpow_decay (continuous_kerH hy) (by norm_num) (kerH_isBigO hy hs)
    (fourier_kerH_isBigO hy hs) x

end

end GaloisForLFunctions.RHTower.HalfWeight
