import GaloisForLFunctions.RHTower.ZetaTwistedFirstMomentContour
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The first moment of `ζ` twisted by `n/d` against a Gaussian window

Put `G(s) = exp((2/H²)(s − σ − iτ)²)`; on `Re s = σ` it is the Gaussian window
`w_τ(t) = exp(−2(t−τ)²/H²)` of mass `√(πH²/2)`. For integers `d, n ≥ 1`, `1/2 ≤ σ ≤ 2`, and a
window `[τ−R, τ+R] ⊆ [T, 2T]`,

`‖∫_{τ−R}^{τ+R} ζ(σ+it) d^{-σ-it} n^{-σ+it} w_τ(t) dt − [d ∣ n] n^{-2σ} √(πH²/2)‖`
`  ≤ 27√T n e^{1−R²/H²} + 2n (√(πH²/2) e^{1−H²/(128n²)} + e^{1−R²/H²} √(πH²))`
(`norm_integral_twistedZeta_gauss_sub_diag_le`).

The proof moves the integral of `ζ(s) d^{-s} n^{s-2σ} G(s)` to `Re s = 2`. The horizontal edges are
Gaussian-small (`e^{−R²/H²}`). On `Re s = 2` each Dirichlet term is a Gaussian Fourier integral
computed in closed form (`integral_gaussFourier`): the diagonal `dm = n` has mass exactly
`√(πH²/2)`, and an off-diagonal frequency `|log(n/dm)| ≥ 1/(2n)` is damped by `e^{−H²/(128n²)}`.
Unlike the sharp cutoff, no error term grows like `√T` relative to the window mass.
-/

noncomputable section

open Complex MeasureTheory Set

namespace RHTower

/-- The Gaussian window `G(s) = exp((2/H²)(s − σ − iτ)²)`. -/
def verticalGaussWindow (σ τ H : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (((2 / H ^ 2 : ℝ) : ℂ) * (s - (σ : ℂ) - (τ : ℂ) * I) ^ 2)

theorem differentiable_verticalGaussWindow (σ τ H : ℝ) : Differentiable ℂ (verticalGaussWindow σ τ H) := by
  unfold verticalGaussWindow
  fun_prop

theorem verticalGaussWindow_line (σ τ H t : ℝ) :
    verticalGaussWindow σ τ H ((σ : ℂ) + (t : ℂ) * I) =
      ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ) := by
  unfold verticalGaussWindow
  rw [Complex.ofReal_exp]
  congr 1
  have h : (σ : ℂ) + (t : ℂ) * I - (σ : ℂ) - (τ : ℂ) * I = ((t - τ : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h, mul_pow, Complex.I_sq]
  push_cast
  ring

theorem norm_verticalGaussWindow (σ τ H : ℝ) (s : ℂ) :
    ‖verticalGaussWindow σ τ H s‖ = Real.exp (2 / H ^ 2 * ((s.re - σ) ^ 2 - (s.im - τ) ^ 2)) := by
  unfold verticalGaussWindow
  rw [Complex.norm_exp, Complex.re_ofReal_mul]
  congr 1
  simp [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im]

/-! ## The Gaussian Fourier integral -/

/-- The integrand `e^{iωt} exp((2/H²)(c₀ + i(t−τ))²)`. -/
def gaussFourier (H c₀ ω τ t : ℝ) : ℂ :=
  Complex.exp (I * ((t * ω : ℝ) : ℂ)) *
    Complex.exp (((2 / H ^ 2 : ℝ) : ℂ) * ((c₀ : ℂ) + ((t - τ : ℝ) : ℂ) * I) ^ 2)

theorem gaussFourier_eq_quadratic (H c₀ ω τ t : ℝ) :
    gaussFourier H c₀ ω τ t = Complex.exp ((((-(2 / H ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 2 +
      (I * (ω : ℂ) + ((2 / H ^ 2 : ℝ) : ℂ) * (2 * (τ : ℂ) + 2 * (c₀ : ℂ) * I)) * (t : ℂ) +
      ((2 / H ^ 2 : ℝ) : ℂ) * ((c₀ : ℂ) ^ 2 - (τ : ℂ) ^ 2 - 2 * (c₀ : ℂ) * (τ : ℂ) * I)) := by
  unfold gaussFourier
  rw [← Complex.exp_add]
  congr 1
  have hI : I ^ 2 = -1 := Complex.I_sq
  push_cast
  linear_combination (2 / (H : ℂ) ^ 2 * ((t : ℂ) - τ) ^ 2) * hI

theorem continuous_gaussFourier (H c₀ ω τ : ℝ) : Continuous (gaussFourier H c₀ ω τ) := by
  unfold gaussFourier
  fun_prop

theorem integrable_gaussFourier {H : ℝ} (hH : 0 < H) (c₀ ω τ : ℝ) :
    Integrable (gaussFourier H c₀ ω τ) := by
  have hb : ((((-(2 / H ^ 2)) : ℝ) : ℂ)).re < 0 := by
    rw [Complex.ofReal_re]; have : 0 < 2 / H ^ 2 := by positivity
    linarith
  have h := integrable_cexp_quadratic' hb
    (I * (ω : ℂ) + ((2 / H ^ 2 : ℝ) : ℂ) * (2 * (τ : ℂ) + 2 * (c₀ : ℂ) * I))
    (((2 / H ^ 2 : ℝ) : ℂ) * ((c₀ : ℂ) ^ 2 - (τ : ℂ) ^ 2 - 2 * (c₀ : ℂ) * (τ : ℂ) * I))
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  exact (gaussFourier_eq_quadratic H c₀ ω τ t).symm

/-- **The Gaussian Fourier integral in closed form.** -/
theorem integral_gaussFourier {H : ℝ} (hH : 0 < H) (c₀ ω τ : ℝ) :
    ∫ t : ℝ, gaussFourier H c₀ ω τ t =
      ((Real.sqrt (Real.pi * H ^ 2 / 2) : ℝ) : ℂ) *
        Complex.exp (((2 / H ^ 2 * c₀ ^ 2 - (ω + 4 * c₀ / H ^ 2) ^ 2 * H ^ 2 / 8 : ℝ) : ℂ) +
          I * ((ω * τ : ℝ) : ℂ)) := by
  have hb : ((((-(2 / H ^ 2)) : ℝ) : ℂ)).re < 0 := by
    rw [Complex.ofReal_re]; have : 0 < 2 / H ^ 2 := by positivity
    linarith
  simp_rw [gaussFourier_eq_quadratic]
  rw [integral_cexp_quadratic hb]
  have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  congr 1
  · rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    congr 1
    · push_cast; field_simp
    · push_cast; ring
  · congr 1
    have hI : I ^ 2 = -1 := Complex.I_sq
    push_cast
    field_simp
    linear_combination (8 * ((H : ℂ) ^ 2 * ω + 4 * c₀) ^ 2) * hI

theorem norm_integral_gaussFourier {H : ℝ} (hH : 0 < H) (c₀ ω τ : ℝ) :
    ‖∫ t : ℝ, gaussFourier H c₀ ω τ t‖ =
      Real.sqrt (Real.pi * H ^ 2 / 2) *
        Real.exp (2 / H ^ 2 * c₀ ^ 2 - (ω + 4 * c₀ / H ^ 2) ^ 2 * H ^ 2 / 8) := by
  rw [integral_gaussFourier hH, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  congr 2
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero, mul_zero]

/-- At frequency `0` the Gaussian has mass exactly `√(πH²/2)`, whatever the shift `c₀`. -/
theorem integral_gaussFourier_zero {H : ℝ} (hH : 0 < H) (c₀ τ : ℝ) :
    ∫ t : ℝ, gaussFourier H c₀ 0 τ t = ((Real.sqrt (Real.pi * H ^ 2 / 2) : ℝ) : ℂ) := by
  rw [integral_gaussFourier hH]
  have h : (2 / H ^ 2 * c₀ ^ 2 - (0 + 4 * c₀ / H ^ 2) ^ 2 * H ^ 2 / 8 : ℝ) = 0 := by
    field_simp; ring
  rw [h]
  simp

theorem norm_gaussFourier (H c₀ ω τ t : ℝ) :
    ‖gaussFourier H c₀ ω τ t‖ = Real.exp (2 / H ^ 2 * (c₀ ^ 2 - (t - τ) ^ 2)) := by
  unfold gaussFourier
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.re_ofReal_mul]
  have h0 : (I * ((t * ω : ℝ) : ℂ)).re = 0 := by simp
  rw [h0, Real.exp_zero, one_mul]
  congr 1
  simp [sq, Complex.mul_re]

/-- **Gaussian tail.** Truncating to `[τ−R, τ+R]` costs at most `e^{2c₀²/H² − R²/H²} √(πH²)`. -/
theorem norm_integral_gaussFourier_sub_interval_le {H : ℝ} (hH : 0 < H) (c₀ ω τ : ℝ) {R : ℝ}
    (hR : 0 ≤ R) :
    ‖(∫ t : ℝ, gaussFourier H c₀ ω τ t) - ∫ t in (τ - R)..(τ + R), gaussFourier H c₀ ω τ t‖ ≤
      Real.exp (2 / H ^ 2 * c₀ ^ 2 - R ^ 2 / H ^ 2) * Real.sqrt (Real.pi * H ^ 2) := by
  have hint := integrable_gaussFourier hH c₀ ω τ
  rw [intervalIntegral.integral_of_le (by linarith),
    ← integral_add_compl (measurableSet_Ioc (a := τ - R) (b := τ + R)) hint, add_sub_cancel_left]
  set B : ℝ → ℝ := fun t => Real.exp (2 / H ^ 2 * c₀ ^ 2 - R ^ 2 / H ^ 2) *
    Real.exp (-(1 / H ^ 2) * (t - τ) ^ 2) with hB
  have hBint : Integrable B :=
    ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / H ^ 2)).comp_sub_right τ).const_mul _
  have hpt : ∀ t ∈ (Ioc (τ - R) (τ + R))ᶜ, ‖gaussFourier H c₀ ω τ t‖ ≤ B t := by
    intro t ht
    have hR2 : R ^ 2 ≤ (t - τ) ^ 2 := by
      simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · nlinarith
      · nlinarith
    rw [norm_gaussFourier]
    simp only [hB]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have key : 2 / H ^ 2 * (c₀ ^ 2 - (t - τ) ^ 2) =
        2 / H ^ 2 * c₀ ^ 2 - R ^ 2 / H ^ 2 + -(1 / H ^ 2) * (t - τ) ^ 2 +
          (R ^ 2 - (t - τ) ^ 2) / H ^ 2 := by ring
    have hneg : (R ^ 2 - (t - τ) ^ 2) / H ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  calc ‖∫ t in (Ioc (τ - R) (τ + R))ᶜ, gaussFourier H c₀ ω τ t‖
      ≤ ∫ t in (Ioc (τ - R) (τ + R))ᶜ, ‖gaussFourier H c₀ ω τ t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in (Ioc (τ - R) (τ + R))ᶜ, B t :=
        setIntegral_mono_on hint.norm.integrableOn hBint.integrableOn measurableSet_Ioc.compl hpt
    _ ≤ ∫ t, B t := setIntegral_le_integral hBint (Filter.Eventually.of_forall fun t => by
        simp only [hB]; positivity)
    _ = Real.exp (2 / H ^ 2 * c₀ ^ 2 - R ^ 2 / H ^ 2) * Real.sqrt (Real.pi * H ^ 2) := by
        simp only [hB]
        rw [integral_const_mul,
          integral_sub_right_eq_self (fun t => Real.exp (-(1 / H ^ 2) * t ^ 2)) τ,
          integral_gaussian]
        congr 2
        field_simp

/-- **Off-diagonal damping.** A frequency `|ω| ≥ 1/(2n)` with `H² ≥ 24n` is damped by
`e^{1 − H²/(128n²)}`. -/
theorem norm_integral_gaussFourier_le {H : ℝ} (hH : 0 < H) {c₀ ω : ℝ} (τ : ℝ) {n : ℝ}
    (hn : 1 ≤ n) (hc0 : 0 ≤ c₀) (hc : c₀ ≤ 3 / 2) (hω : 1 / (2 * n) ≤ |ω|)
    (hHn : 24 * n ≤ H ^ 2) :
    ‖∫ t : ℝ, gaussFourier H c₀ ω τ t‖ ≤
      Real.sqrt (Real.pi * H ^ 2 / 2) * Real.exp (1 - H ^ 2 / (128 * n ^ 2)) := by
  rw [norm_integral_gaussFourier hH]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _)
  have hH2 : 0 < H ^ 2 := by positivity
  have hn0 : 0 < n := by linarith
  have he0 : 0 ≤ 4 * c₀ / H ^ 2 := by positivity
  have he1 : 4 * c₀ / H ^ 2 ≤ 1 / (4 * n) := by
    rw [div_le_div_iff₀ hH2 (by positivity)]
    nlinarith
  have habs : 1 / (4 * n) ≤ |ω + 4 * c₀ / H ^ 2| := by
    have h1 : |ω| ≤ |ω + 4 * c₀ / H ^ 2| + |4 * c₀ / H ^ 2| := by
      have := abs_sub (ω + 4 * c₀ / H ^ 2) (4 * c₀ / H ^ 2)
      simpa using this
    rw [abs_of_nonneg he0] at h1
    have h2 : 1 / (2 * n) = 1 / (4 * n) + 1 / (4 * n) := by field_simp; ring
    linarith
  have hsq : (1 / (4 * n)) ^ 2 ≤ (ω + 4 * c₀ / H ^ 2) ^ 2 := by
    rw [← sq_abs (ω + 4 * c₀ / H ^ 2)]
    exact pow_le_pow_left₀ (by positivity) habs 2
  have hdamp : H ^ 2 / (128 * n ^ 2) ≤ (ω + 4 * c₀ / H ^ 2) ^ 2 * H ^ 2 / 8 := by
    have : H ^ 2 / (128 * n ^ 2) = (1 / (4 * n)) ^ 2 * H ^ 2 / 8 := by field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hH2.le) (by norm_num)
  have hc2 : 2 / H ^ 2 * c₀ ^ 2 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hH2]
    nlinarith
  linarith

/-! ## The line `Re s = 2` with the Gaussian window -/

theorem twistedZetaTerm_mul_verticalGaussWindow {σ : ℝ} {d n m : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (τ H t : ℝ) :
    twistedZetaTerm σ d n m t * verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I) =
      (twistedZetaAmp σ d n m : ℂ) * gaussFourier H (2 - σ) (twistedZetaFreq d n m) τ t := by
  rw [twistedZetaTerm_eq hd hn hm]
  unfold gaussFourier verticalGaussWindow
  have h : (2 : ℂ) + (t : ℂ) * I - (σ : ℂ) - (τ : ℂ) * I =
      ((2 - σ : ℝ) : ℂ) + ((t - τ : ℝ) : ℂ) * I := by push_cast; ring
  rw [h]
  ring

/-- Off the diagonal the frequency `log n − log(dm)` is at least `1/(2n)`. -/
theorem abs_twistedZetaFreq_ge {d n m : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hne : d * m ≠ n) : 1 / (2 * (n : ℝ)) ≤ |twistedZetaFreq d n m| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdm : (0 : ℕ) < d * m := by positivity
  have hφ : twistedZetaFreq d n m = Real.log n - Real.log ((d * m : ℕ) : ℝ) := by
    unfold twistedZetaFreq
    push_cast
    rw [Real.log_mul (by exact_mod_cast (by omega : d ≠ 0)) (by exact_mod_cast (by omega : m ≠ 0))]
    ring
  rcases le_or_gt (2 * n) (d * m) with hbig | hsmall
  · have hlog2 : (1 / 2 : ℝ) ≤ |twistedZetaFreq d n m| := by
      rw [hφ, abs_sub_comm, abs_of_nonneg]
      · have h1 : Real.log (2 * (n : ℝ)) ≤ Real.log ((d * m : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hbig)
        rw [Real.log_mul (by norm_num) hn0.ne'] at h1
        have := Real.log_two_gt_d9
        linarith
      · have : Real.log (n : ℝ) ≤ Real.log ((d * m : ℕ) : ℝ) :=
          Real.log_le_log hn0 (by exact_mod_cast (by omega : n ≤ d * m))
        linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  · have hsp := HTGeometry.inv_max_le_abs_log_sub_log_nat
      (by omega : 0 < n) hdm hne.symm
    rw [← hφ] at hsp
    have hmax : max (n : ℝ) ((d * m : ℕ) : ℝ) ≤ 2 * n := by
      apply max_le (by linarith)
      exact_mod_cast hsmall.le
    exact le_trans (one_div_le_one_div_of_le (by positivity) hmax) hsp

/-- The per-window error on `Re s = 2`. -/
def gaussTwistError (H R n : ℝ) : ℝ :=
  Real.sqrt (Real.pi * H ^ 2 / 2) * Real.exp (1 - H ^ 2 / (128 * n ^ 2)) +
    Real.exp (1 - R ^ 2 / H ^ 2) * Real.sqrt (Real.pi * H ^ 2)

/-- **The line `Re s = 2` with the Gaussian window:** only the diagonal `dm = n` survives. -/
theorem norm_integral_twistedZeta_gauss_two_sub_diag_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {H : ℝ} (hH : 0 < H) (hHn : 24 * (n : ℝ) ≤ H ^ 2)
    (τ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ‖(∫ t in (τ - R)..(τ + R), twistedZeta σ d n ((2 : ℂ) + (t : ℂ) * I) *
          verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I)) -
        (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * Real.sqrt (Real.pi * H ^ 2 / 2) : ℝ) : ℂ) else 0)‖ ≤
      2 * n * gaussTwistError H R n := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hH2 : 0 < H ^ 2 := by positivity
  set K : ℝ := Real.sqrt (Real.pi * H ^ 2 / 2) with hK
  set G₀ : ℝ := Real.exp (2 / H ^ 2 * (2 - σ) ^ 2) with hG₀
  -- the Gaussian factor on `Re s = 2`
  have hGle : ∀ t : ℝ, ‖verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I)‖ ≤ G₀ := by
    intro t
    rw [norm_verticalGaussWindow, hG₀]
    apply Real.exp_le_exp.mpr
    have : ((2 : ℂ) + (t : ℂ) * I).re = 2 := by simp
    rw [this]
    have : 0 ≤ 2 / H ^ 2 * ((((2 : ℂ) + (t : ℂ) * I).im - τ) ^ 2) := by positivity
    nlinarith
  have hsum2 : Summable fun m : ℕ => (n : ℝ) * (1 / (m : ℝ) ^ 2) * G₀ :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _).mul_right _
  have hHas : HasSum (fun m => ∫ t in (τ - R)..(τ + R),
        twistedZetaTerm σ d n m t * verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I))
      (∫ t in (τ - R)..(τ + R), twistedZeta σ d n ((2 : ℂ) + (t : ℂ) * I) *
          verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => (n : ℝ) * (1 / (m : ℝ) ^ 2) * G₀) (fun m => ?_) (fun m => ?_) ?_ ?_ ?_
    · have hc : Continuous fun t : ℝ =>
          twistedZetaTerm σ d n m t * verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I) := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · have h0 : (fun t : ℝ => twistedZetaTerm σ d n 0 t *
              verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I)) = fun _ => 0 :=
            funext fun t => by rw [twistedZetaTerm_zero, zero_mul]
          rw [h0]; exact continuous_const
        · have : (fun t : ℝ => twistedZetaTerm σ d n m t *
              verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I)) = fun t : ℝ =>
              (twistedZetaAmp σ d n m : ℂ) * gaussFourier H (2 - σ) (twistedZetaFreq d n m) τ t :=
            funext fun t => twistedZetaTerm_mul_verticalGaussWindow hd hn hm τ H t
          rw [this]
          exact continuous_const.mul (continuous_gaussFourier _ _ _ _)
      exact hc.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t _ => ?_
      rw [norm_mul]
      exact mul_le_mul (norm_twistedZetaTerm_le hσ hd hn m t) (hGle t) (norm_nonneg _)
        (by positivity)
    · exact Filter.Eventually.of_forall fun t _ => hsum2
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ => (hasSum_twistedZetaTerm σ d n t).mul_right _
  -- the diagonal
  set D : ℕ → ℂ := fun m => if d * m = n then (((n : ℝ) ^ (-2 * σ) * K : ℝ) : ℂ) else 0 with hD
  have hDsum : HasSum D (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * K : ℝ) : ℂ) else 0) := by
    by_cases hdn : d ∣ n
    · obtain ⟨k, hk⟩ := hdn
      rw [if_pos ⟨k, hk⟩]
      have hsingle : ∀ m ≠ k, D m = 0 := by
        intro m hm
        simp only [hD]
        rw [if_neg]
        intro h
        apply hm
        have hd0 : 0 < d := by omega
        exact Nat.eq_of_mul_eq_mul_left hd0 (h.trans hk)
      have := hasSum_single k hsingle
      simp only [hD, if_pos hk.symm] at this
      exact this
    · rw [if_neg hdn]
      have : D = fun _ => 0 := by
        funext m
        simp only [hD]
        rw [if_neg]
        intro h
        exact hdn ⟨m, h.symm⟩
      rw [this]
      exact hasSum_zero
  have htail : ∀ ω : ℝ, ‖(∫ t : ℝ, gaussFourier H (2 - σ) ω τ t) -
      ∫ t in (τ - R)..(τ + R), gaussFourier H (2 - σ) ω τ t‖ ≤
        Real.exp (1 - R ^ 2 / H ^ 2) * Real.sqrt (Real.pi * H ^ 2) := by
    intro ω
    refine (norm_integral_gaussFourier_sub_interval_le hH (2 - σ) ω τ hR).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _)
    have : 2 / H ^ 2 * (2 - σ) ^ 2 ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hH2]; nlinarith
    linarith
  have hterm : ∀ m : ℕ, ‖(∫ t in (τ - R)..(τ + R),
        twistedZetaTerm σ d n m t * verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I)) - D m‖ ≤
      (n : ℝ) * (1 / (m : ℝ) ^ 2) * gaussTwistError H R n := by
    intro m
    have hE0 : 0 ≤ gaussTwistError H R n := by unfold gaussTwistError; positivity
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hD0 : D 0 = 0 := by
        simp only [hD]; rw [if_neg]; omega
      simp only [twistedZetaTerm_zero, zero_mul, intervalIntegral.integral_zero, hD0, sub_zero,
        norm_zero]
      positivity
    · have hint : (∫ t in (τ - R)..(τ + R),
          twistedZetaTerm σ d n m t * verticalGaussWindow σ τ H ((2 : ℂ) + (t : ℂ) * I)) =
          (twistedZetaAmp σ d n m : ℂ) *
            ∫ t in (τ - R)..(τ + R), gaussFourier H (2 - σ) (twistedZetaFreq d n m) τ t := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun t _ => twistedZetaTerm_mul_verticalGaussWindow hd hn hm τ H t
      have hA := twistedZetaAmp_le hσ hd hn hm
      have hA0 : 0 ≤ twistedZetaAmp σ d n m := (Real.exp_pos _).le
      by_cases hdiag : d * m = n
      · have hφ : twistedZetaFreq d n m = 0 := by
          unfold twistedZetaFreq
          rw [← hdiag]
          push_cast
          rw [Real.log_mul (by exact_mod_cast (by omega : d ≠ 0))
            (by exact_mod_cast (by omega : m ≠ 0))]
          ring
        have hamp : twistedZetaAmp σ d n m = (n : ℝ) ^ (-2 * σ) := by
          unfold twistedZetaAmp
          rw [Real.rpow_def_of_pos hn0]
          congr 1
          have : Real.log (n : ℝ) = Real.log d + Real.log m := by
            rw [← hdiag]; push_cast
            exact Real.log_mul (by exact_mod_cast (by omega : d ≠ 0))
              (by exact_mod_cast (by omega : m ≠ 0))
          rw [this]; ring
        have hDm : D m = (((n : ℝ) ^ (-2 * σ) * K : ℝ) : ℂ) := by
          simp only [hD]; rw [if_pos hdiag]
        rw [hint, hDm, hφ, hamp]
        have hfull := integral_gaussFourier_zero hH (2 - σ) τ
        have ht := htail 0
        rw [hfull] at ht
        rw [show ((((n : ℝ) ^ (-2 * σ) * K : ℝ)) : ℂ) = (((n : ℝ) ^ (-2 * σ) : ℝ) : ℂ) * (K : ℂ) by
          push_cast; ring, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hn0.le _), norm_sub_rev]
        have hamp_le : (n : ℝ) ^ (-2 * σ) ≤ (n : ℝ) * (1 / (m : ℝ) ^ 2) := by
          rw [← hamp, mul_one_div]; exact hA
        have hEge : Real.exp (1 - R ^ 2 / H ^ 2) * Real.sqrt (Real.pi * H ^ 2) ≤
            gaussTwistError H R n := by
          unfold gaussTwistError
          have : 0 ≤ Real.sqrt (Real.pi * H ^ 2 / 2) * Real.exp (1 - H ^ 2 / (128 * (n : ℝ) ^ 2)) :=
            by positivity
          linarith
        exact mul_le_mul hamp_le (ht.trans hEge) (norm_nonneg _) (by positivity)
      · have hD0 : D m = 0 := by simp only [hD]; rw [if_neg hdiag]
        rw [hD0, sub_zero, hint, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
        have hfreq := abs_twistedZetaFreq_ge hd hn hm hdiag
        have hoff := norm_integral_gaussFourier_le hH (c₀ := 2 - σ) τ hn1 (by linarith)
          (by linarith) hfreq hHn
        have ht := htail (twistedZetaFreq d n m)
        have hsplit : ‖∫ t in (τ - R)..(τ + R), gaussFourier H (2 - σ) (twistedZetaFreq d n m) τ t‖ ≤
            gaussTwistError H R n := by
          have := norm_sub_norm_le (∫ t : ℝ, gaussFourier H (2 - σ) (twistedZetaFreq d n m) τ t)
            ((∫ t : ℝ, gaussFourier H (2 - σ) (twistedZetaFreq d n m) τ t) -
              ∫ t in (τ - R)..(τ + R), gaussFourier H (2 - σ) (twistedZetaFreq d n m) τ t)
          rw [sub_sub_cancel] at this
          unfold gaussTwistError
          have := norm_le_insert' (∫ t in (τ - R)..(τ + R),
            gaussFourier H (2 - σ) (twistedZetaFreq d n m) τ t)
            (∫ t : ℝ, gaussFourier H (2 - σ) (twistedZetaFreq d n m) τ t)
          rw [norm_sub_rev] at this
          linarith
        have hA' : twistedZetaAmp σ d n m ≤ (n : ℝ) * (1 / (m : ℝ) ^ 2) := by
          rw [mul_one_div]; exact hA
        exact mul_le_mul hA' hsplit (norm_nonneg _) (by positivity)
  have hdiff := hHas.sub hDsum
  have hbound : Summable fun m : ℕ => (n : ℝ) * (1 / (m : ℝ) ^ 2) * gaussTwistError H R n :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _).mul_right _
  have hE0 : 0 ≤ gaussTwistError H R n := by unfold gaussTwistError; positivity
  calc _ ≤ ∑' m : ℕ, (n : ℝ) * (1 / (m : ℝ) ^ 2) * gaussTwistError H R n :=
        hdiff.norm_le_of_bounded hbound.hasSum hterm
    _ = (n : ℝ) * (Real.pi ^ 2 / 6) * gaussTwistError H R n := by
        rw [tsum_mul_right, tsum_mul_left, hasSum_zeta_two.tsum_eq]
    _ ≤ 2 * n * gaussTwistError H R n := by
        have h1 := Real.pi_lt_d2
        have hπ := Real.pi_pos
        have hπ2 : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_left hπ2 hn0.le
        exact mul_le_mul_of_nonneg_right (by linarith) hE0

/-! ## The contour shift -/

/-- On the horizontal edges `Im s = τ ± R` the windowed integrand is `≤ 9√T n e^{1−R²/H²}`. -/
theorem norm_twistedZeta_gauss_horizontal_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) {d n : ℕ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) {T H R τ x Y : ℝ} (hT : 4 ≤ T) (hY1 : T ≤ Y) (hY2 : Y ≤ 2 * T)
    (hYR : (Y - τ) ^ 2 = R ^ 2) (hH : 0 < H) (hH24 : 24 ≤ H ^ 2) (hx1 : σ ≤ x) (hx2 : x ≤ 2) :
    ‖twistedZeta σ d n ((x : ℂ) + (Y : ℂ) * I) * verticalGaussWindow σ τ H ((x : ℂ) + (Y : ℂ) * I)‖ ≤
      9 * Real.sqrt T * n * Real.exp (1 - R ^ 2 / H ^ 2) := by
  rw [norm_mul]
  refine mul_le_mul (norm_twistedZeta_horizontal_le hσ hd hn hT hY1 hY2 hx1 hx2) ?_
    (norm_nonneg _) (by positivity)
  rw [norm_verticalGaussWindow]
  apply Real.exp_le_exp.mpr
  have hre : ((x : ℂ) + (Y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (Y : ℂ) * I).im = Y := by simp
  rw [hre, him, hYR]
  have hH2 : 0 < H ^ 2 := by positivity
  have key : 2 / H ^ 2 * ((x - σ) ^ 2 - R ^ 2) = 2 * (x - σ) ^ 2 / H ^ 2 - R ^ 2 / H ^ 2 -
      R ^ 2 / H ^ 2 := by ring
  have h1 : 2 * (x - σ) ^ 2 / H ^ 2 ≤ 1 := by
    rw [div_le_one hH2]; nlinarith
  have h2 : 0 ≤ R ^ 2 / H ^ 2 := by positivity
  linarith

/-- **The Gaussian-windowed twisted first moment of `ζ`.** For `[τ−R, τ+R] ⊆ [T, 2T]`,
`‖∫_{τ−R}^{τ+R} ζ(σ+it) d^{-σ-it} n^{-σ+it} w_τ(t) dt − [d ∣ n] n^{-2σ} √(πH²/2)‖` is at most
`27√T n e^{1−R²/H²} + 2n·gaussTwistError H R n`. -/
theorem norm_integral_twistedZeta_gauss_sub_diag_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {T H R τ : ℝ} (hT : 4 ≤ T) (hH : 0 < H)
    (hHn : 24 * (n : ℝ) ≤ H ^ 2) (hR : 0 ≤ R) (hτ1 : T ≤ τ - R) (hτ2 : τ + R ≤ 2 * T) :
    ‖(∫ t in (τ - R)..(τ + R), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) *
          ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ)) -
        (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * Real.sqrt (Real.pi * H ^ 2 / 2) : ℝ) : ℂ) else 0)‖ ≤
      27 * Real.sqrt T * n * Real.exp (1 - R ^ 2 / H ^ 2) + 2 * n * gaussTwistError H R n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hH24 : 24 ≤ H ^ 2 := by linarith
  set f : ℂ → ℂ := fun s => twistedZeta σ d n s * verticalGaussWindow σ τ H s with hf
  set z : ℂ := (σ : ℂ) + ((τ - R : ℝ) : ℂ) * I with hz
  set w : ℂ := (2 : ℂ) + ((τ + R : ℝ) : ℂ) * I with hw
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = τ - R := by simp [hz]
  have hwre : w.re = 2 := by simp [hw]
  have hwim : w.im = τ + R := by simp [hw]
  have hdiff : DifferentiableOn ℂ f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    intro s hs
    have him := (Complex.mem_reProdIm.mp hs).2
    rw [hzim, hwim, Set.uIcc_of_le (by linarith)] at him
    have hs1 : s ≠ 1 := by
      intro h; rw [h, Complex.one_im] at him; linarith [him.1]
    exact ((differentiableAt_twistedZeta σ hd hn hs1).mul
      ((differentiable_verticalGaussWindow σ τ H) s)).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hdiff
  rw [hzre, hzim, hwre, hwim] at hrect
  have hhor : ∀ Y : ℝ, T ≤ Y → Y ≤ 2 * T → (Y - τ) ^ 2 = R ^ 2 →
      ‖∫ x in σ..2, f ((x : ℂ) + (Y : ℂ) * I)‖ ≤
        27 / 2 * Real.sqrt T * n * Real.exp (1 - R ^ 2 / H ^ 2) := by
    intro Y hY1 hY2 hYR
    have hb : ∀ x ∈ Set.uIoc σ 2, ‖f ((x : ℂ) + (Y : ℂ) * I)‖ ≤
        9 * Real.sqrt T * n * Real.exp (1 - R ^ 2 / H ^ 2) := by
      intro x hx
      rw [Set.uIoc_of_le hσ2] at hx
      exact norm_twistedZeta_gauss_horizontal_le hσ hd hn hT hY1 hY2 hYR hH hH24 hx.1.le hx.2
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    rw [abs_of_nonneg (by linarith)]
    have h0 : 0 ≤ Real.sqrt T * n * Real.exp (1 - R ^ 2 / H ^ 2) := by positivity
    nlinarith
  have hH1 := hhor (τ - R) hτ1 (by linarith) (by ring)
  have hH2 := hhor (τ + R) (by linarith) hτ2 (by ring)
  have hvert : ‖(∫ t in (τ - R)..(τ + R), f ((σ : ℂ) + (t : ℂ) * I)) -
      ∫ t in (τ - R)..(τ + R), f ((2 : ℂ) + (t : ℂ) * I)‖ ≤
        27 * Real.sqrt T * n * Real.exp (1 - R ^ 2 / H ^ 2) := by
    have hcast2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    rw [hcast2] at hrect
    have hkey : (∫ t in (τ - R)..(τ + R), f ((σ : ℂ) + (t : ℂ) * I)) -
        ∫ t in (τ - R)..(τ + R), f ((2 : ℂ) + (t : ℂ) * I) =
        -I * ((∫ x in σ..2, f ((x : ℂ) + ((τ - R : ℝ) : ℂ) * I)) -
          ∫ x in σ..2, f ((x : ℂ) + ((τ + R : ℝ) : ℂ) * I)) := by
      have hI : I * I = -1 := Complex.I_mul_I
      simp only [smul_eq_mul] at hrect
      linear_combination I * hrect + ((∫ t in (τ - R)..(τ + R), f ((σ : ℂ) + (t : ℂ) * I)) -
        ∫ t in (τ - R)..(τ + R), f ((2 : ℂ) + (t : ℂ) * I)) * hI
    rw [hkey, norm_mul, norm_neg, Complex.norm_I, one_mul]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hright := norm_integral_twistedZeta_gauss_two_sub_diag_le hσ hσ2 hd hn hH hHn τ hR
  have hleft : (∫ t in (τ - R)..(τ + R), f ((σ : ℂ) + (t : ℂ) * I)) =
      ∫ t in (τ - R)..(τ + R), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) *
        ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hf, verticalGaussWindow_line]
  rw [← hleft]
  calc ‖(∫ t in (τ - R)..(τ + R), f ((σ : ℂ) + (t : ℂ) * I)) -
        (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * Real.sqrt (Real.pi * H ^ 2 / 2) : ℝ) : ℂ) else 0)‖
      = ‖((∫ t in (τ - R)..(τ + R), f ((σ : ℂ) + (t : ℂ) * I)) -
          ∫ t in (τ - R)..(τ + R), f ((2 : ℂ) + (t : ℂ) * I)) +
        ((∫ t in (τ - R)..(τ + R), f ((2 : ℂ) + (t : ℂ) * I)) -
          (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * Real.sqrt (Real.pi * H ^ 2 / 2) : ℝ) : ℂ)
            else 0))‖ := by
        congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hvert hright)

end RHTower
