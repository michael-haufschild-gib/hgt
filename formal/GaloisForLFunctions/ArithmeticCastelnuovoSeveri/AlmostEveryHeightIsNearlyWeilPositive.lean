import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ShortWindowAveragedWeilPositivity

/-!
# Almost every height is nearly Weil-positive

For a real test `F₀ ∈ C²_c([-A, A])` and a height `γ`, write
`Q_γ(F₀) = Q(F₀ cos γ·) + Q(F₀ sin γ·)` for the complete Weil form of the two modulations. Positivity
of `Q_γ` at every height and aperture is RH. This module shows that the negative part of `Q_γ` is read
by one function of the height alone, and that this function is small at almost every height of every
window of length `Γ^{99/100}`.

* **The off-line field.** `Φ(γ) = Σ_q (Re q - 1/2)² / (1 + (Im q - γ)²)²` over the zero copies `q`
  (`offLineField`). It vanishes identically under RH.
* **Pointwise law** (`neg_offLineField_le_fullZeroForm`). For every aperture `A ≥ 0`, every test
  `F₀ ∈ C²_c([-A, A])` and every height `γ`:
  `Q_γ(F₀) ≥ -4 (A + 1)² e^A N(F₀)² Φ(γ)`.
  The depth difference of a zero at depth `δ` is at most `4(A+1)|δ| e^{A/2} N / (1 + x²)`
  (`norm_depthDiff_le_depth`), with the factor `δ` coming from the conjugate-point difference and the
  decay from two integrations by parts.
* **Short windows** (`exists_volume_offLineField_gt_le`). For `Γ^{99/100} ≤ H ≤ Γ/8` and `η > 0`, the
  heights `γ ∈ [Γ, Γ + H]` with `Φ(γ) > η` have measure `≤ C H / (η log Γ)`: the squared depths of
  the zeros near the window sum to `O(H / log Γ)` by Selberg's near-line density on short windows
  (`exists_window_sum_sq_depth_le`).

**Selection** (`exists_shortWindow_almostEvery_height_nearly_positive`). Outside a set of measure
`C H / (η log Γ)`, every height of the window satisfies `Q_γ(F₀) ≥ -4η (A + 1)² e^A N(F₀)²` for all
apertures and all tests at once. The exceptional set depends on neither the aperture nor the test.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped BigOperators Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.BiScaleUncertainty
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. The depth difference carries the depth -/

/-- `|e^y - e^{-y}| ≤ 2|y| e^{|y|}`. -/
theorem abs_exp_sub_exp_neg_le (y : ℝ) :
    |Real.exp y - Real.exp (-y)| ≤ 2 * |y| * Real.exp |y| := by
  have key : ∀ t : ℝ, 0 ≤ t → Real.exp t - Real.exp (-t) ≤ 2 * t * Real.exp t := by
    intro t ht
    have h1 := Real.add_one_le_exp (-(2 * t))
    have h2 : Real.exp (-t) = Real.exp t * Real.exp (-(2 * t)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    nlinarith [Real.exp_pos t]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, abs_of_nonneg (by
      have := Real.exp_le_exp.mpr (by linarith : -y ≤ y); linarith)]
    exact key y hy
  · have h := key (-y) (by linarith)
    rw [neg_neg] at h
    rw [abs_of_nonpos hy, abs_of_nonpos (by
      have := Real.exp_le_exp.mpr (by linarith : y ≤ -y); linarith)]
    linarith

/-- The transform of a profile supported in `[-A, A]` moves by at most `2|δ| A e^{|δ|A} ‖f‖₁` between
the conjugate points `x - iδ` and `x + iδ`. -/
theorem norm_paperFT_sub_paperFT_conj_le {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → f u = 0)
    (x δ : ℝ) :
    ‖paperFT (fun u => (f u : ℂ)) ((x : ℂ) - (δ : ℂ) * I) -
        paperFT (fun u => (f u : ℂ)) ((x : ℂ) + (δ : ℂ) * I)‖ ≤
      2 * |δ| * A * Real.exp (|δ| * A) * ∫ u, |f u| := by
  have hint : ∀ w : ℂ, Integrable fun u : ℝ => (f u : ℂ) * Complex.exp (Complex.I * w * (u : ℂ)) :=
    fun w => ((Complex.continuous_ofReal.comp hf).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hfc.comp_left Complex.ofReal_zero).mul_right)
  have hfi : Integrable fun u : ℝ => |f u| := hf.abs.integrable_of_hasCompactSupport hfc.abs
  unfold paperFT
  rw [← integral_sub (hint _) (hint _), ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hfi.const_mul _) (Eventually.of_forall fun u => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hu : |u| ≤ A
  · have h1 : Complex.I * ((x : ℂ) - (δ : ℂ) * I) * (u : ℂ) =
        ((x * u : ℝ) : ℂ) * Complex.I + ((δ * u : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have h2 : Complex.I * ((x : ℂ) + (δ : ℂ) * I) * (u : ℂ) =
        ((x * u : ℝ) : ℂ) * Complex.I + ((-(δ * u) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have he : Complex.exp (Complex.I * ((x : ℂ) - (δ : ℂ) * I) * (u : ℂ)) -
        Complex.exp (Complex.I * ((x : ℂ) + (δ : ℂ) * I) * (u : ℂ)) =
        Complex.exp (((x * u : ℝ) : ℂ) * Complex.I) *
          (((Real.exp (δ * u) - Real.exp (-(δ * u)) : ℝ) : ℂ)) := by
      rw [h1, h2, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
      push_cast; ring
    rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have hb := abs_exp_sub_exp_neg_le (δ * u)
    have hdu : |δ * u| ≤ |δ| * A := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    have hb' : |Real.exp (δ * u) - Real.exp (-(δ * u))| ≤ 2 * |δ| * A * Real.exp (|δ| * A) := by
      calc |Real.exp (δ * u) - Real.exp (-(δ * u))| ≤ 2 * |δ * u| * Real.exp |δ * u| := hb
        _ ≤ 2 * (|δ| * A) * Real.exp (|δ| * A) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hdu (by norm_num))
              (Real.exp_le_exp.mpr hdu) (Real.exp_pos _).le (by positivity)
        _ = 2 * |δ| * A * Real.exp (|δ| * A) := by ring
    calc |f u| * |Real.exp (δ * u) - Real.exp (-(δ * u))|
        ≤ |f u| * (2 * |δ| * A * Real.exp (|δ| * A)) :=
          mul_le_mul_of_nonneg_left hb' (abs_nonneg _)
      _ = 2 * |δ| * A * Real.exp (|δ| * A) * |f u| := by ring
  · rw [hsupp u (not_le.mp hu)]
    simp

private theorem gammaOf_sub_real'' (ρ : ℂ) (ω : ℝ) :
    gammaOf ρ - (ω : ℂ) = ((ρ.im - ω : ℝ) : ℂ) - ((ρ.re - 1 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [gammaOf, Complex.div_I]
  apply Complex.ext <;> simp

private theorem conj_gammaOf_sub_real'' (ρ : ℂ) (ω : ℝ) :
    conj (gammaOf ρ) - (ω : ℂ) = ((ρ.im - ω : ℝ) : ℂ) + ((ρ.re - 1 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [gammaOf, Complex.div_I]
  apply Complex.ext <;> simp

/-- **The depth difference carries the depth.** For a strip zero `ρ` at depth `δ = Re ρ - 1/2`,
`‖F̂(γ_ρ - ω) - F̂(γ̄_ρ - ω)‖ ≤ 4(A + 1) |δ| e^{A/2} N(F₀) / (1 + (Im ρ - ω)²)`. -/
theorem norm_depthDiff_le_depth {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (ω : ℝ) :
    ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ))‖ ≤
      4 * (A + 1) * |ρ.re - 1 / 2| * Real.exp (A / 2) * envelopeWindowNorm F₀ /
        (1 + (ρ.im - ω) ^ 2) := by
  rw [gammaOf_sub_real'', conj_gammaOf_sub_real'']
  set x : ℝ := ρ.im - ω with hx
  set δ : ℝ := ρ.re - 1 / 2 with hδ
  have hδ2 : |δ| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  set g : ℝ → ℂ := fun u => (F₀ u : ℂ) with hg_def
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp hF₀
  have hgc : HasCompactSupport g := hF₀c.comp_left Complex.ofReal_zero
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) F₀ from hF₀)
  have h2 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv F₀) from h1.2.2)
  have hF''_cont : Continuous (deriv (deriv F₀)) := h2.2.2.continuous
  have hsupp'' : ∀ u : ℝ, A < |u| → deriv (deriv F₀) u = 0 := fun u hu => by
    rcases lt_abs.mp hu with hu1 | hu2
    · have heq : F₀ =ᶠ[𝓝 u] 0 := Filter.eventually_of_mem (Ioi_mem_nhds hu1) fun s hs =>
        hsupp s (lt_abs.mpr (Or.inl hs))
      exact ((heq.deriv).deriv).eq_of_nhds.trans (by simp)
    · have heq : F₀ =ᶠ[𝓝 u] 0 := Filter.eventually_of_mem (Iio_mem_nhds (by linarith : u < -A))
        fun s hs => hsupp s (lt_abs.mpr (Or.inr (by linarith [Set.mem_Iio.mp hs])))
      exact ((heq.deriv).deriv).eq_of_nhds.trans (by simp)
  have hg''_eq : deriv (deriv g) = fun u => ((deriv (deriv F₀) u : ℝ) : ℂ) := by
    have hd1 : deriv g = fun u => ((deriv F₀ u : ℝ) : ℂ) := by
      funext u
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (h1.1 u).hasDerivAt).deriv
    rw [hd1]
    funext u
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (h2.1 u).hasDerivAt).deriv
  set z : ℂ := (x : ℂ) - (δ : ℂ) * I with hz
  set zc : ℂ := (x : ℂ) + (δ : ℂ) * I with hzc
  set N : ℝ := envelopeWindowNorm F₀ with hN
  have hI1 : 0 ≤ ∫ u, |F₀ u| := integral_nonneg fun u => abs_nonneg _
  have hI2 : 0 ≤ ∫ u, |deriv (deriv F₀) u| := integral_nonneg fun u => abs_nonneg _
  have hN1 : (∫ u, |F₀ u|) ≤ N := by rw [hN, envelopeWindowNorm]; linarith
  have hN2 : (∫ u, |deriv (deriv F₀) u|) ≤ N := by rw [hN, envelopeWindowNorm]; linarith
  have hN0 : 0 ≤ N := envelopeWindowNorm_nonneg F₀
  have he : Real.exp (|δ| * A) ≤ Real.exp (A / 2) := Real.exp_le_exp.mpr (by nlinarith)
  -- The plain difference.
  have ha0 : ‖paperFT g z - paperFT g zc‖ ≤ 2 * |δ| * A * Real.exp (|δ| * A) * N :=
    (norm_paperFT_sub_paperFT_conj_le hF₀.continuous hF₀c hA hsupp x δ).trans
      (mul_le_mul_of_nonneg_left hN1 (by positivity))
  -- The second-derivative difference.
  have hb0 : ‖paperFT (deriv (deriv g)) z - paperFT (deriv (deriv g)) zc‖ ≤
      2 * |δ| * A * Real.exp (|δ| * A) * N := by
    rw [hg''_eq]
    exact (norm_paperFT_sub_paperFT_conj_le hF''_cont hF₀c.deriv.deriv hA hsupp'' x δ).trans
      (mul_le_mul_of_nonneg_left hN2 (by positivity))
  have hzc_bd : ‖paperFT g zc‖ ≤ Real.exp (|δ| * A) * N / (1 + x ^ 2) := by
    have h := norm_paperFT_symm_le hF₀ hF₀c hA hsupp zc
    have hre : zc.re = x := by simp [hzc]
    have him : zc.im = δ := by simp [hzc]
    rwa [hre, him, mul_comm A |δ|] at h
  have hid : z ^ 2 * (paperFT g z - paperFT g zc) =
      -(paperFT (deriv (deriv g)) z - paperFT (deriv (deriv g)) zc) +
        (zc ^ 2 - z ^ 2) * paperFT g zc := by
    rw [EvenSector.paperFT_deriv_deriv_of_compact hg hgc z,
      EvenSector.paperFT_deriv_deriv_of_compact hg hgc zc]
    ring
  have hdiff : zc ^ 2 - z ^ 2 = ((4 * x * δ : ℝ) : ℂ) * I := by
    rw [hz, hzc]; push_cast; ring
  have hnorm_z : x ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [hz, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
      zero_sub]
    nlinarith [sq_nonneg δ]
  have hx_frac : |x| / (1 + x ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  set a : ℝ := ‖paperFT g z - paperFT g zc‖ with ha
  have hza : ‖z‖ ^ 2 * a ≤ 2 * |δ| * A * Real.exp (|δ| * A) * N +
      2 * |δ| * Real.exp (|δ| * A) * N := by
    have h := congrArg norm hid
    rw [norm_mul, norm_pow] at h
    rw [ha, h]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, hdiff, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs]
    refine add_le_add hb0 ?_
    have habs : |4 * x * δ| = 4 * |x| * |δ| := by rw [abs_mul, abs_mul]; norm_num
    rw [habs]
    calc 4 * |x| * |δ| * ‖paperFT g zc‖
        ≤ 4 * |x| * |δ| * (Real.exp (|δ| * A) * N / (1 + x ^ 2)) :=
          mul_le_mul_of_nonneg_left hzc_bd (by positivity)
      _ = 4 * |δ| * Real.exp (|δ| * A) * N * (|x| / (1 + x ^ 2)) := by ring
      _ ≤ 4 * |δ| * Real.exp (|δ| * A) * N * (1 / 2) :=
          mul_le_mul_of_nonneg_left hx_frac (by positivity)
      _ = 2 * |δ| * Real.exp (|δ| * A) * N := by ring
  have hxa : x ^ 2 * a ≤ ‖z‖ ^ 2 * a := mul_le_mul_of_nonneg_right hnorm_z (norm_nonneg _)
  have htot : (1 + x ^ 2) * a ≤ 4 * (A + 1) * |δ| * Real.exp (A / 2) * N := by
    have hsum : (1 + x ^ 2) * a ≤ (4 * A + 2) * |δ| * Real.exp (|δ| * A) * N := by
      nlinarith [ha0, hza, hxa]
    calc (1 + x ^ 2) * a ≤ (4 * A + 2) * |δ| * Real.exp (|δ| * A) * N := hsum
      _ ≤ (4 * A + 4) * |δ| * Real.exp (A / 2) * N := by
          have h4 : (4 * A + 2) * |δ| ≤ (4 * A + 4) * |δ| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          have := mul_le_mul h4 he (Real.exp_pos _).le (by positivity)
          nlinarith [hN0]
      _ = 4 * (A + 1) * |δ| * Real.exp (A / 2) * N := by ring
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact htot

/-- The squared depth difference over four is at most `4 (A+1)² e^A N² δ² / (1 + x²)²`. -/
theorem depthDiff_sq_div_four_le_depth {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (ω : ℝ) :
    ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ))‖ ^ 2 / 4 ≤
      4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 *
        ((ρ.re - 1 / 2) ^ 2 / (1 + (ρ.im - ω) ^ 2) ^ 2) := by
  have h := norm_depthDiff_le_depth hF₀ hF₀c hA hsupp hρ0 hρ1 ω
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hexp : Real.exp (A / 2) ^ 2 = Real.exp A := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hd : 0 < 1 + (ρ.im - ω) ^ 2 := by positivity
  calc _ ≤ (4 * (A + 1) * |ρ.re - 1 / 2| * Real.exp (A / 2) * envelopeWindowNorm F₀ /
        (1 + (ρ.im - ω) ^ 2)) ^ 2 / 4 := div_le_div_of_nonneg_right hsq (by norm_num)
    _ = 4 * (A + 1) ^ 2 * Real.exp (A / 2) ^ 2 * envelopeWindowNorm F₀ ^ 2 *
        (|ρ.re - 1 / 2| ^ 2 / (1 + (ρ.im - ω) ^ 2) ^ 2) := by rw [div_pow]; ring
    _ = _ := by rw [hexp, sq_abs]

/-! ### 2. The off-line field -/

/-- The off-line field `Φ(γ) = Σ_q (Re q - 1/2)² / (1 + (Im q - γ)²)²` over the zero copies. -/
def offLineField (γ : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, ((q.1 : ℂ).re - 1 / 2) ^ 2 / (1 + ((q.1 : ℂ).im - γ) ^ 2) ^ 2

theorem offLineField_term_le (γ : ℝ) (q : XiZeroCopy) :
    ((q.1 : ℂ).re - 1 / 2) ^ 2 / (1 + ((q.1 : ℂ).im - γ) ^ 2) ^ 2 ≤
      (1 / 4) * lorentzMassTerm γ q := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hδ : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith [hstrip.1, hstrip.2]
  have hd : 0 < 1 + ((q.1 : ℂ).im - γ) ^ 2 := by positivity
  have hterm : lorentzMassTerm γ q = 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2) := by
    unfold lorentzMassTerm
    rw [show (γ - (q.1 : ℂ).im) ^ 2 = ((q.1 : ℂ).im - γ) ^ 2 by ring]
  rw [hterm]
  have hsq : 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2) ^ 2 ≤ 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2) :=
    one_div_le_one_div_of_le hd (le_self_pow₀ (le_add_of_nonneg_right (sq_nonneg _)) two_ne_zero)
  calc ((q.1 : ℂ).re - 1 / 2) ^ 2 / (1 + ((q.1 : ℂ).im - γ) ^ 2) ^ 2
      = ((q.1 : ℂ).re - 1 / 2) ^ 2 * (1 / (1 + ((q.1 : ℂ).im - γ) ^ 2) ^ 2) := by ring
    _ ≤ (1 / 4) * (1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) :=
        mul_le_mul hδ hsq (by positivity) (by norm_num)

theorem summable_offLineField (γ : ℝ) :
    Summable fun q : XiZeroCopy =>
      ((q.1 : ℂ).re - 1 / 2) ^ 2 / (1 + ((q.1 : ℂ).im - γ) ^ 2) ^ 2 :=
  ((summable_lorentzMassTerm γ).mul_left (1 / 4)).of_nonneg_of_le (fun q => by positivity)
    (offLineField_term_le γ)

theorem offLineField_nonneg (γ : ℝ) : 0 ≤ offLineField γ :=
  tsum_nonneg fun q => by positivity

/-- **The negative part of the Weil form at one height is read by the off-line field.** For every
aperture `A ≥ 0`, every real `F₀ ∈ C²_c([-A, A])` and every height `γ`,
`Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ -4 (A + 1)² e^A N(F₀)² Φ(γ)`. -/
theorem neg_offLineField_le_fullZeroForm {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    (γ : ℝ) :
    -(4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 * offLineField γ) ≤
      fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  rw [fullZeroForm_cosine_add_sine_eq_zeta_W_re hF₀ hF₀c γ]
  obtain ⟨hsum, -⟩ := integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c (Γ := 1) le_rfl hA hsupp
  have h := re_zeta_W_complexModulatedSource_ge_finset hF₀ hF₀c γ ∅ (hsum γ)
  rw [Finset.sum_empty, zero_sub] at h
  set K : ℝ := 4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 with hK
  set d : ℂ → ℝ := fun z =>
    ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (γ : ℂ)) -
      paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (γ : ℂ))‖ ^ 2 / 4 with hd_def
  have hdom : ∀ q : XiZeroCopy, d (q.1 : ℂ) ≤
      K * (((q.1 : ℂ).re - 1 / 2) ^ 2 / (1 + ((q.1 : ℂ).im - γ) ^ 2) ^ 2) := fun q => by
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    exact depthDiff_sq_div_four_le_depth hF₀ hF₀c hA hsupp hstrip.1 hstrip.2 γ
  have hsum_q : Summable fun q : XiZeroCopy => d (q.1 : ℂ) :=
    ((summable_offLineField γ).mul_left K).of_nonneg_of_le (fun q => by simp only [hd_def]; positivity)
      hdom
  have hbridge := tsum_xiZeroCopy_eq_zetaCarrier (g := d) hsum_q
  have hle : (∑' q : XiZeroCopy, d (q.1 : ℂ)) ≤ K * offLineField γ := by
    rw [offLineField, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hdom hsum_q ((summable_offLineField γ).mul_left K)
  have hform : (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * d (ρ : ℂ) :=
    tsum_congr fun ρ => by simp only [hd_def]; ring
  rw [hform, ← hbridge] at h
  linarith

/-! ### 3. Squared depths near a short window -/

/-- `(y - 1/2)² ≤ 2 e^{λ(y - 1/2)L} / (λL)²` for `y ≥ 1/2`. -/
private theorem sq_le_exp_div (y lam L : ℝ) (hy : 1 / 2 ≤ y) (hlam : 0 < lam) (hL : 0 < L) :
    (y - 1 / 2) ^ 2 ≤ 2 * Real.exp (lam * (y - 1 / 2) * L) / (lam * L) ^ 2 := by
  set t : ℝ := lam * (y - 1 / 2) * L with ht
  have ht0 : 0 ≤ t := by rw [ht]; have : 0 ≤ y - 1 / 2 := by linarith
                         positivity
  have hq := Real.quadratic_le_exp_of_nonneg ht0
  have hpos : 0 < (lam * L) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have e : (y - 1 / 2) ^ 2 * (lam * L) ^ 2 = t ^ 2 := by rw [ht]; ring
  rw [e]
  nlinarith [sq_nonneg t]

/-- **Squared depths near a short window.** There are `C₃` and `Γ₁` such that for `Γ ≥ Γ₁`,
`Γ^{99/100} ≤ H ≤ Γ/8` and every finite set `G` of zero copies with ordinates in `[Γ - H, Γ + 2H]`,
`Σ_{q ∈ G} (Re q - 1/2)² ≤ C₃ H / log Γ`. Zeros within `4800/log Γ` of the line are counted; the
deeper ones are paid by Selberg's weighted near-line density at `λ = 1/19200`. -/
theorem exists_window_sum_sq_depth_le :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∃ Γ₁ : ℝ, 64 ≤ Γ₁ ∧
      ∀ Γ : ℝ, Γ₁ ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 →
        ∀ G : Finset XiZeroCopy,
          (∀ q ∈ G, Γ - H ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 2 * H) →
          ∑ q ∈ G, (foldedRe q - 1 / 2) ^ 2 ≤ C₃ * H / Real.log Γ := by
  obtain ⟨A_sel, K_sel, hA_sel, hK_sel, hev_sel⟩ := RHTower.exists_shortWindowZeros_weighted_le
  obtain ⟨U_sel, hU_sel⟩ := Filter.eventually_atTop.mp hev_sel
  obtain ⟨Cw, hCw, T₀w, -, hwinle⟩ := exists_xiZeroCount_window_le
  obtain ⟨K₃, hK₃1, hK₃⟩ := exists_one_add_log_pow_le_rpow 3 (by norm_num : (0 : ℝ) < 1 / 4)
  set C₂ : ℝ := 4800 with hC₂
  set lam : ℝ := 1 / 19200 with hlam
  set C₃ : ℝ := 3 * C₂ ^ 2 + (8 / lam ^ 2) * (8 * A_sel / (Real.pi * C₂)) +
    (8 / lam ^ 2) * (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) with hC₃
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  obtain ⟨Γ₁, hΓ₁_64, hΓ₁U, hΓ₁e, hΓ₁T, hΓ₁C⟩ : ∃ Γ₁ : ℝ, 64 ≤ Γ₁ ∧ U_sel ≤ Γ₁ ∧
      Real.exp (4 * C₂) ≤ Γ₁ ∧ 2 * T₀w + 2 ≤ Γ₁ ∧ (8 * Cw + 8) ^ (2 : ℕ) ≤ Γ₁ := by
    refine ⟨max 64 (max U_sel (max (Real.exp (4 * C₂)) (max (2 * T₀w + 2)
      ((8 * Cw + 8) ^ (2 : ℕ))))), le_max_left _ _, ?_, ?_, ?_, ?_⟩
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)
    · exact (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)
  refine ⟨C₃, hC₃0, Γ₁, hΓ₁_64, fun Γ hΓ H hH1 hH2 G hG => ?_⟩
  classical
  have hΓ64 : 64 ≤ Γ := hΓ₁_64.trans hΓ
  have hΓ0 : 0 < Γ := by linarith
  have hΓ1 : 1 ≤ Γ := by linarith
  have hlogΓ_ge : 4 * C₂ ≤ Real.log Γ := by
    have := Real.log_le_log (Real.exp_pos _) (hΓ₁e.trans hΓ); rwa [Real.log_exp] at this
  have hlogΓ_ge1 : 1 ≤ Real.log Γ := by linarith
  have hlogΓ_pos : 0 < Real.log Γ := by linarith
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hΓ0 _) hH1
  have hHC : 8 * Cw + 8 ≤ H := by
    refine le_trans ?_ ((Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num : (1 / 2 : ℝ) ≤
      99 / 100)).trans hH1)
    have := Real.rpow_le_rpow (by positivity) (hΓ₁C.trans hΓ) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at this
  have hv₀_pos : 0 < C₂ / Real.log Γ := by rw [hC₂]; positivity
  have hv₀_q : C₂ / Real.log Γ ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hlogΓ_pos (by norm_num)]; linarith
  have hsplit_G := (Finset.sum_filter_add_sum_filter_not G
    (fun q => foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ) (fun q => (foldedRe q - 1 / 2) ^ 2)).symm
  -- Shallow copies.
  have hcard := window_card_le hCw hwinle (hΓ₁T.trans hΓ) hH0 hH2 hHC G hG
  have hsh : (∑ q ∈ G.filter (fun q => foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
      (foldedRe q - 1 / 2) ^ 2) ≤ 3 * C₂ ^ 2 * H / Real.log Γ := by
    have hpt : ∀ q ∈ G.filter (fun q => foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
        (foldedRe q - 1 / 2) ^ 2 ≤ (C₂ / Real.log Γ) ^ 2 := fun q hq => by
      have h1 := (Finset.mem_filter.mp hq).2
      have h0 : 0 ≤ foldedRe q - 1 / 2 := sub_nonneg.mpr (half_le_foldedRe q)
      exact pow_le_pow_left₀ h0 (by linarith) 2
    have hcard_sh : ((G.filter (fun q => foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ)).card : ℝ) ≤
        3 * H * Real.log Γ := le_trans (by exact_mod_cast Finset.card_filter_le G _) hcard
    calc (∑ q ∈ G.filter (fun q => foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
          (foldedRe q - 1 / 2) ^ 2)
        ≤ ((G.filter (fun q => foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ)).card : ℝ) *
            (C₂ / Real.log Γ) ^ 2 := by
          refine (Finset.sum_le_sum hpt).trans_eq ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 * H * Real.log Γ) * (C₂ / Real.log Γ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard_sh (by positivity)
      _ = 3 * C₂ ^ 2 * H / Real.log Γ := by field_simp
  -- Deep copies: one Selberg window at `U = 3Γ`.
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 3 * Γ := ⟨_, rfl⟩
  have hlogU_ge : Real.log Γ ≤ Real.log U := Real.log_le_log hΓ0 (by rw [hU]; linarith)
  have hlogU_le : Real.log U ≤ 2 * Real.log Γ := by
    have hΓsq : 16 * Γ ≤ Γ ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hΓ0.le
    have : Real.log U ≤ Real.log (Γ ^ 2) :=
      Real.log_le_log (by rw [hU]; positivity) (by rw [hU]; linarith)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlogU_pos : 0 < Real.log U := lt_of_lt_of_le hlogΓ_pos hlogU_ge
  have hW99 : Real.exp (99 / 100 * Real.log U) + 2 ≤ 3 * H + 4 := by
    have hU99 : Real.exp (99 / 100 * Real.log U) = U ^ (99 / 100 : ℝ) := by
      rw [Real.rpow_def_of_pos (by rw [hU]; positivity), mul_comm]
    rw [hU99, hU, Real.mul_rpow (by norm_num) hΓ0.le]
    have h3 : (3 : ℝ) ^ (99 / 100 : ℝ) ≤ 3 := by
      calc (3 : ℝ) ^ (99 / 100 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    have := mul_le_mul h3 hH1 (Real.rpow_nonneg hΓ0.le _) (by norm_num)
    linarith
  obtain ⟨T₁, hT₁, T₂, hT₂, hsel⟩ := hU_sel U (by rw [hU]; linarith [hΓ₁U.trans hΓ])
    (Γ - H - 2) (3 * H + 4) (by rw [hU]; linarith) (by rw [hU]; linarith) hW99
  have hT₁pos : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have hv₀_low : 2 / Real.log U ≤ C₂ / Real.log Γ :=
    (div_le_div_of_nonneg_left (by norm_num) hlogΓ_pos hlogU_ge).trans
      (div_le_div_of_nonneg_right (by linarith) hlogΓ_pos.le)
  have hG_dp : ∀ q ∈ G.filter (fun q => ¬ foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
      1 / 2 + C₂ / Real.log Γ < foldedRe q ∧ T₁ ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂ :=
    fun q hq => by
      have hq1 := Finset.mem_filter.mp hq
      have hqG := hG q hq1.1
      rw [abs_of_pos (by linarith [hqG.1] : 0 < (q.1 : ℂ).im)]
      exact ⟨not_le.mp hq1.2, by linarith [hT₁.2, hqG.1], by linarith [hT₂.1, hqG.2]⟩
  have h4 := sum_foldedRe_le_four_mul_windowZeros
    (g := fun y => Real.exp (lam * (y - 1 / 2) * Real.log U))
    (fun _ => (Real.exp_pos _).le) hT₁pos hT12 hv₀_pos _ hG_dp
  have hS := hsel lam (C₂ / Real.log Γ) (by rw [hlam]; norm_num) (by rw [hlam]; norm_num)
    hv₀_low hv₀_q
  have hterm1 := window_selberg_main_le hA_sel (le_of_eq hC₂.symm) hlogΓ_pos rfl hlogU_ge
    (by linarith [hT₁.1, hT₂.2] : T₂ - T₁ ≤ 4 * H) hH0
  have hterm2 := window_selberg_error_le (U := U) (C₂ := C₂) hK_sel (by rw [hC₂]; norm_num) hΓ1
    hlogΓ_pos
    rfl hlogU_ge hlogU_le hK₃
  have hlam_def : lam = 1 / 19200 := hlam
  rw [← hlam_def] at hterm2
  have hexp_sum : (∑ q ∈ G.filter (fun q => ¬ foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
      Real.exp (lam * (foldedRe q - 1 / 2) * Real.log U)) ≤
        4 * ((8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ +
          (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ)) :=
    h4.trans (by
      have := mul_le_mul_of_nonneg_left hS (by norm_num : (0 : ℝ) ≤ 4)
      linarith [hterm1, hterm2])
  have hdp : (∑ q ∈ G.filter (fun q => ¬ foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
      (foldedRe q - 1 / 2) ^ 2) ≤
        (8 / lam ^ 2) * (8 * A_sel / (Real.pi * C₂)) * H / Real.log Γ +
          (8 / lam ^ 2) * (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * H / Real.log Γ := by
    have hlam0 : 0 < lam := by rw [hlam]; norm_num
    have hpt : ∀ q ∈ G.filter (fun q => ¬ foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
        (foldedRe q - 1 / 2) ^ 2 ≤
          (2 / (lam * Real.log Γ) ^ 2) * Real.exp (lam * (foldedRe q - 1 / 2) * Real.log U) :=
      fun q _ => by
        have h := sq_le_exp_div (foldedRe q) lam (Real.log U) (half_le_foldedRe q) hlam0
          hlogU_pos
        calc (foldedRe q - 1 / 2) ^ 2
            ≤ 2 * Real.exp (lam * (foldedRe q - 1 / 2) * Real.log U) / (lam * Real.log U) ^ 2 := h
          _ ≤ 2 * Real.exp (lam * (foldedRe q - 1 / 2) * Real.log U) / (lam * Real.log Γ) ^ 2 :=
              div_le_div_of_nonneg_left (by positivity) (by positivity)
                (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hlogU_ge hlam0.le) 2)
          _ = (2 / (lam * Real.log Γ) ^ 2) *
                Real.exp (lam * (foldedRe q - 1 / 2) * Real.log U) := by ring
    have hΓ34 : Γ ^ (3 / 4 : ℝ) ≤ H * Real.log Γ := by
      have h1 : Γ ^ (3 / 4 : ℝ) ≤ Γ ^ (99 / 100 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num)
      have h2 : H ≤ H * Real.log Γ := le_mul_of_one_le_right hH0.le hlogΓ_ge1
      linarith
    calc (∑ q ∈ G.filter (fun q => ¬ foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
          (foldedRe q - 1 / 2) ^ 2)
        ≤ ∑ q ∈ G.filter (fun q => ¬ foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
            (2 / (lam * Real.log Γ) ^ 2) * Real.exp (lam * (foldedRe q - 1 / 2) * Real.log U) :=
          Finset.sum_le_sum hpt
      _ = (2 / (lam * Real.log Γ) ^ 2) *
            ∑ q ∈ G.filter (fun q => ¬ foldedRe q ≤ 1 / 2 + C₂ / Real.log Γ),
              Real.exp (lam * (foldedRe q - 1 / 2) * Real.log U) := by rw [Finset.mul_sum]
      _ ≤ (2 / (lam * Real.log Γ) ^ 2) * (4 * ((8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ +
            (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp_sum (by positivity)
      _ ≤ (2 / (lam * Real.log Γ) ^ 2) * (4 * ((8 * A_sel / (Real.pi * C₂)) * H * Real.log Γ +
            (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * (H * Real.log Γ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hΓ34 (by positivity))
      _ = _ := by
          have hC₂ne : C₂ ≠ 0 := by rw [hC₂]; norm_num
          field_simp [hlam0.ne', hC₂ne, hlogΓ_pos.ne', Real.pi_ne_zero]
          ring
  rw [hsplit_G]
  have hfin : 3 * C₂ ^ 2 * H / Real.log Γ +
      ((8 / lam ^ 2) * (8 * A_sel / (Real.pi * C₂)) * H / Real.log Γ +
        (8 / lam ^ 2) * (4 * (K_sel + 1) * K₃ / (Real.pi * C₂)) * H / Real.log Γ) =
      C₃ * H / Real.log Γ := by rw [hC₃]; ring
  linarith [hsh, hdp]

/-! ### 4. The off-line field is small at almost every height of a short window -/

/-- **The off-line field on a short window.** There are `C` and `Γ₀` such that for `Γ ≥ Γ₀`,
`Γ^{99/100} ≤ H ≤ Γ/8` and `η > 0`, the heights `γ ∈ [Γ, Γ + H]` with `Φ(γ) > η` have measure at most
`C H / (η log Γ)`. -/
theorem exists_volume_offLineField_gt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 →
        ∀ η : ℝ, 0 < η →
          volume {γ | γ ∈ Icc Γ (Γ + H) ∧ η < offLineField γ} ≤
            ENNReal.ofReal (C * H / (η * Real.log Γ)) := by
  obtain ⟨C₃, hC₃, Γ₁, hΓ₁, hsq⟩ := exists_window_sum_sq_depth_le
  set c : ℝ := |xiLineTwoLogDerivConstant| with hc
  -- `Γ` large enough that the remote tail is below the main term.
  obtain ⟨K₁, hK₁1, hK₁⟩ := exists_one_add_log_pow_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Γ₂, hΓ₂1, hΓ₂⟩ : ∃ Γ₂ : ℝ, Γ₁ ≤ Γ₂ ∧ (8 * (c + 3) * K₁) ^ (2 : ℕ) ≤ Γ₂ :=
    ⟨max Γ₁ ((8 * (c + 3) * K₁) ^ (2 : ℕ)), le_max_left _ _, le_max_right _ _⟩
  refine ⟨Real.pi * C₃ + 1, by positivity, Γ₂, hΓ₁.trans hΓ₂1,
    fun Γ hΓ H hH1 hH2 η hη => ?_⟩
  classical
  have hΓ1' : Γ₁ ≤ Γ := hΓ₂1.trans hΓ
  have hΓ64 : 64 ≤ Γ := hΓ₁.trans hΓ1'
  have hΓ0 : 0 < Γ := by linarith
  have hΓ1 : 1 ≤ Γ := by linarith
  have hL : 1 ≤ Real.log Γ := by
    have : Real.exp 1 ≤ Γ := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at this
  have hL0 : 0 < Real.log Γ := by linarith
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hΓ0 _) hH1
  -- The local copies.
  have hS_fin : ({q : XiZeroCopy | Γ - H ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 2 * H}).Finite :=
    (finite_xiOrdinateWindow (Γ + 2 * H) 0).subset fun q hq => by
      rw [mem_xiOrdinateWindow_iff, sub_zero, abs_le]
      exact ⟨by linarith [hq.1], hq.2⟩
  obtain ⟨G_loc, hmem⟩ : ∃ G_loc : Finset XiZeroCopy,
      ∀ q : XiZeroCopy, q ∈ G_loc ↔ Γ - H ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 2 * H :=
    ⟨hS_fin.toFinset, fun _ => hS_fin.mem_toFinset⟩
  have hsumG := hsq Γ hΓ1' H hH1 hH2 G_loc fun q hq => (hmem q).mp hq
  -- The majorant on the window.
  set B : ℝ := 2 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) / H ^ 2 with hB
  set Ψ : ℝ → ℝ := fun γ => (∑ q ∈ G_loc, (foldedRe q - 1 / 2) ^ 2 *
    (1 / (1 + ((q.1 : ℂ).im - γ) ^ 2))) + B with hΨ
  have hΨc : Continuous Ψ := by
    refine (continuous_finsetSum _ fun q _ => continuous_const.mul ?_).add continuous_const
    exact continuous_const.div (by fun_prop) fun γ => by positivity
  have hΦΨ : ∀ γ ∈ Icc Γ (Γ + H), offLineField γ ≤ Ψ γ := by
    intro γ hγ
    have hs := summable_offLineField γ
    unfold offLineField
    rw [← hs.sum_add_tsum_subtype_compl G_loc]
    refine add_le_add (Finset.sum_le_sum fun q _ => ?_) ?_
    · have hd : 0 < 1 + ((q.1 : ℂ).im - γ) ^ 2 := by positivity
      have hsqre : ((q.1 : ℂ).re - 1 / 2) ^ 2 = (foldedRe q - 1 / 2) ^ 2 := by
        rw [foldedRe_sub_half_eq_abs, sq_abs]
      rw [hsqre, div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact one_div_le_one_div_of_le hd
        (le_self_pow₀ (le_add_of_nonneg_right (sq_nonneg _)) two_ne_zero)
    · have hfar : ∀ q : {q : XiZeroCopy // q ∉ G_loc},
          (((q : XiZeroCopy).1 : ℂ).re - 1 / 2) ^ 2 /
              (1 + (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2) ^ 2 ≤
            (1 / (4 * H ^ 2)) * lorentzMassTerm γ q := fun q => by
        have hq := q.2
        rw [hmem, not_and_or] at hq
        have hfarx : H ≤ |((q : XiZeroCopy).1 : ℂ).im - γ| := by
          rcases hq with h | h
          · rw [abs_sub_comm, abs_of_nonneg (by linarith [hγ.1, not_le.mp h])]
            linarith [hγ.1, not_le.mp h]
          · rw [abs_of_nonneg (by linarith [hγ.2, not_le.mp h])]
            linarith [hγ.2, not_le.mp h]
        have hstrip := xi_divisor_support_re_mem_open_unit (q : XiZeroCopy).1
        have hδ : (((q : XiZeroCopy).1 : ℂ).re - 1 / 2) ^ 2 ≤ 1 / 4 := by
          nlinarith [hstrip.1, hstrip.2]
        have hl := lorentz_sq_le_of_far hH0 hfarx
        have hterm : lorentzMassTerm γ q =
            1 / (1 + (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2) := by
          unfold lorentzMassTerm
          rw [show (γ - ((q : XiZeroCopy).1 : ℂ).im) ^ 2 =
            (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2 by ring]
        rw [hterm]
        calc (((q : XiZeroCopy).1 : ℂ).re - 1 / 2) ^ 2 /
              (1 + (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2) ^ 2
            = (((q : XiZeroCopy).1 : ℂ).re - 1 / 2) ^ 2 *
                (1 / (1 + (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2) ^ 2) := by ring
          _ ≤ (1 / 4) * ((1 / H ^ 2) * (1 / (1 + (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2))) :=
              mul_le_mul hδ hl (by positivity) (by norm_num)
          _ = _ := by ring
      have hsum_far : Summable fun q : {q : XiZeroCopy // q ∉ G_loc} =>
          (1 / (4 * H ^ 2)) * lorentzMassTerm γ q :=
        ((summable_lorentzMassTerm γ).subtype {q | q ∉ G_loc}).mul_left _
      have hmass_sub : (∑' q : {q : XiZeroCopy // q ∉ G_loc}, lorentzMassTerm γ q) ≤
          lorentzMass γ :=
        Summable.tsum_subtype_le (lorentzMassTerm γ) {q | q ∉ G_loc}
          (fun q => lorentzMassTerm_nonneg γ q) (summable_lorentzMassTerm γ)
      have hlog : lorentzMass γ ≤ 8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) := by
        refine (lorentzMass_le_log γ).trans ?_
        have hγpos : 0 ≤ γ := by linarith [hγ.1]
        have hle : |γ| + 4 ≤ 2 * Γ + 4 := by rw [abs_of_nonneg hγpos]; linarith [hγ.2]
        have := Real.log_le_log (by positivity) hle
        linarith
      calc (∑' q : {q : XiZeroCopy // q ∉ G_loc},
            (((q : XiZeroCopy).1 : ℂ).re - 1 / 2) ^ 2 /
              (1 + (((q : XiZeroCopy).1 : ℂ).im - γ) ^ 2) ^ 2)
          ≤ ∑' q : {q : XiZeroCopy // q ∉ G_loc}, (1 / (4 * H ^ 2)) * lorentzMassTerm γ q :=
            Summable.tsum_le_tsum hfar (hs.subtype _) hsum_far
        _ = (1 / (4 * H ^ 2)) * ∑' q : {q : XiZeroCopy // q ∉ G_loc}, lorentzMassTerm γ q :=
            tsum_mul_left
        _ ≤ (1 / (4 * H ^ 2)) * (8 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4))) :=
            mul_le_mul_of_nonneg_left (hmass_sub.trans hlog) (by positivity)
        _ = B := by rw [hB]; field_simp; ring
  -- The integral of the majorant.
  have hΨint : IntegrableOn Ψ (Icc Γ (Γ + H)) := hΨc.integrableOn_Icc
  have hB0 : 0 ≤ B := by
    have h := lorentzMass_le_log Γ
    have hm : 0 ≤ lorentzMass Γ := tsum_nonneg fun q => lorentzMassTerm_nonneg Γ q
    have hle : |Γ| + 4 ≤ 2 * Γ + 4 := by rw [abs_of_pos hΓ0]; linarith
    have := Real.log_le_log (by positivity) hle
    rw [hB]
    apply div_nonneg ?_ (by positivity)
    linarith
  have hΨ_nn : ∀ γ, 0 ≤ Ψ γ := fun γ => by
    simp only [hΨ]
    exact add_nonneg (Finset.sum_nonneg fun q _ => by positivity) hB0
  have hint_le : (∫ γ in Icc Γ (Γ + H), Ψ γ) ≤
      Real.pi * (∑ q ∈ G_loc, (foldedRe q - 1 / 2) ^ 2) + H * B := by
    have hterm_int : ∀ q ∈ G_loc, IntegrableOn
        (fun γ : ℝ => (foldedRe q - 1 / 2) ^ 2 * (1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)))
        (Icc Γ (Γ + H)) := fun q _ =>
      (continuous_const.mul (continuous_const.div (by fun_prop)
        fun γ => by positivity)).integrableOn_Icc
    have hsum_c : Continuous fun γ : ℝ => ∑ q ∈ G_loc, (foldedRe q - 1 / 2) ^ 2 *
        (1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) :=
      continuous_finsetSum _ fun q _ => continuous_const.mul
        (continuous_const.div (by fun_prop) fun γ => by positivity)
    simp only [hΨ]
    rw [integral_add hsum_c.integrableOn_Icc continuous_const.integrableOn_Icc,
      integral_finsetSum _ hterm_int, setIntegral_const, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), show Γ + H - Γ = H by ring, smul_eq_mul]
    refine add_le_add ?_ le_rfl
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    rw [integral_const_mul, mul_comm Real.pi]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hlor : Integrable fun γ : ℝ => 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2) := by
      have heq : (fun γ : ℝ => 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) =
          fun γ : ℝ => (1 + (γ - (q.1 : ℂ).im) ^ 2)⁻¹ := by
        funext γ; rw [one_div]; congr 2; ring
      rw [heq]; exact integrable_inv_one_add_sq.comp_sub_right _
    have hval : (∫ γ : ℝ, 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) = Real.pi := by
      have heq : (fun γ : ℝ => 1 / (1 + ((q.1 : ℂ).im - γ) ^ 2)) =
          fun γ : ℝ => (1 + (γ - (q.1 : ℂ).im) ^ 2)⁻¹ := by
        funext γ; rw [one_div]; congr 2; ring
      rw [heq, integral_sub_right_eq_self (fun u : ℝ => (1 + u ^ 2)⁻¹) _]
      exact integral_univ_inv_one_add_sq
    rw [← hval]
    exact setIntegral_le_integral hlor (Eventually.of_forall fun γ => by positivity)
  -- The remote tail is below the main term.
  have htail : H * B ≤ H / Real.log Γ := by
    have hlog24 : Real.log (2 * Γ + 4) ≤ 3 * Real.log Γ := by
      have hΓsq : 16 * Γ ≤ Γ ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hΓ0.le
      have hΓ3 : Γ ^ 2 ≤ Γ ^ 3 := pow_le_pow_right₀ hΓ1 (by norm_num)
      have : Real.log (2 * Γ + 4) ≤ Real.log (Γ ^ 3) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hc1 : xiLineTwoLogDerivConstant ≤ c * Real.log Γ := by
      rw [hc]
      exact (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hL)
    have hnum : 2 * (xiLineTwoLogDerivConstant + Real.log (2 * Γ + 4)) ≤
        2 * (c + 3) * Real.log Γ := by nlinarith
    -- `2(c+3) log Γ · log Γ ≤ H²`.
    have hsqrt : 8 * (c + 3) * K₁ ≤ Γ ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) (hΓ₂.trans hΓ) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at this
    have hlogsq : Real.log Γ ^ 2 ≤ K₁ * Γ ^ (1 / 2 : ℝ) :=
      (pow_le_pow_left₀ hL0.le (by linarith) 2).trans (hK₁ Γ hΓ1)
    have hHsq : Γ ^ (1 / 2 : ℝ) * Γ ^ (1 / 2 : ℝ) ≤ H ^ 2 := by
      have h1 : Γ ^ (1 / 2 : ℝ) ≤ H :=
        (Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num)).trans hH1
      rw [sq]; exact mul_le_mul h1 h1 (by positivity) hH0.le
    have hkey : 2 * (c + 3) * Real.log Γ * Real.log Γ ≤ H ^ 2 := by
      have hc0 : 0 ≤ c := by rw [hc]; exact abs_nonneg _
      calc 2 * (c + 3) * Real.log Γ * Real.log Γ = 2 * (c + 3) * Real.log Γ ^ 2 := by ring
        _ ≤ 2 * (c + 3) * (K₁ * Γ ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogsq (by positivity)
        _ = (2 * (c + 3) * K₁) * Γ ^ (1 / 2 : ℝ) := by ring
        _ ≤ Γ ^ (1 / 2 : ℝ) * Γ ^ (1 / 2 : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            nlinarith [hsqrt, hc0, hK₁1]
        _ ≤ H ^ 2 := hHsq
    have hH2 : 0 < H ^ 2 := by positivity
    rw [hB, mul_div_assoc', le_div_iff₀ hL0, div_mul_eq_mul_div, div_le_iff₀ hH2]
    have h1 := mul_le_mul_of_nonneg_left hnum (by positivity : 0 ≤ H * Real.log Γ)
    have h2 := mul_le_mul_of_nonneg_left hkey hH0.le
    nlinarith [h1, h2]
  have hintΨ : (∫ γ in Icc Γ (Γ + H), Ψ γ) ≤ (Real.pi * C₃ + 1) * H / Real.log Γ := by
    have h1 := mul_le_mul_of_nonneg_left hsumG Real.pi_pos.le
    have e : (Real.pi * C₃ + 1) * H / Real.log Γ = Real.pi * (C₃ * H / Real.log Γ) +
        H / Real.log Γ := by ring
    linarith [hint_le, htail]
  -- Markov's inequality for the continuous majorant.
  have hsub : {γ | γ ∈ Icc Γ (Γ + H) ∧ η < offLineField γ} ⊆
      Icc Γ (Γ + H) ∩ {γ | η ≤ Ψ γ} := fun γ hγ =>
    ⟨hγ.1, le_of_lt (hγ.2.trans_le (hΦΨ γ hγ.1))⟩
  have hmeasS : MeasurableSet {γ : ℝ | η ≤ Ψ γ} :=
    measurableSet_le measurable_const hΨc.measurable
  have hfin : volume.restrict (Icc Γ (Γ + H)) {γ | η ≤ Ψ γ} ≠ ⊤ := by
    rw [Measure.restrict_apply hmeasS]
    have hlt : volume ({γ | η ≤ Ψ γ} ∩ Icc Γ (Γ + H)) < ⊤ :=
      (measure_mono Set.inter_subset_right).trans_lt
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    exact hlt.ne
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Icc Γ (Γ + H))) (Eventually.of_forall hΨ_nn) hΨint η
  calc volume {γ | γ ∈ Icc Γ (Γ + H) ∧ η < offLineField γ}
      ≤ volume (Icc Γ (Γ + H) ∩ {γ | η ≤ Ψ γ}) := measure_mono hsub
    _ = volume.restrict (Icc Γ (Γ + H)) {γ | η ≤ Ψ γ} := by
        rw [Measure.restrict_apply hmeasS, Set.inter_comm]
    _ = ENNReal.ofReal (volume.restrict (Icc Γ (Γ + H)) {γ | η ≤ Ψ γ}).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal ((Real.pi * C₃ + 1) * H / (η * Real.log Γ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ (by positivity)]
        have h := hmarkov.trans hintΨ
        have h' := (le_div_iff₀ hL0).mp h
        calc (volume.restrict (Icc Γ (Γ + H)) {γ | η ≤ Ψ γ}).toReal * (η * Real.log Γ)
            = η * (volume.restrict (Icc Γ (Γ + H)) {γ | η ≤ Ψ γ}).toReal * Real.log Γ := by ring
          _ ≤ (Real.pi * C₃ + 1) * H := h'

/-! ### 5. Selection -/

/-- **Almost every height of a short window is nearly Weil-positive.** There are `C` and `Γ₀` such
that for `Γ ≥ Γ₀`, `Γ^{99/100} ≤ H ≤ Γ/8` and `η > 0` there is a set `B` of measure at most
`C H / (η log Γ)` such that every height `γ ∈ [Γ, Γ + H] ∖ B` satisfies, for every aperture `A ≥ 0`
and every real `F₀ ∈ C²_c([-A, A])`,
`Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ -4η (A + 1)² e^A N(F₀)²`. -/
theorem exists_shortWindow_almostEvery_height_nearly_positive :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 →
        ∀ η : ℝ, 0 < η → ∃ B : Set ℝ, volume B ≤ ENNReal.ofReal (C * H / (η * Real.log Γ)) ∧
          ∀ γ ∈ Icc Γ (Γ + H), γ ∉ B →
            ∀ A : ℝ, 0 ≤ A → ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
              (∀ u : ℝ, A < |u| → F₀ u = 0) →
              -(4 * η * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
                fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  obtain ⟨C, hC, Γ₀, hΓ₀, hvol⟩ := exists_volume_offLineField_gt_le
  refine ⟨C, hC, Γ₀, hΓ₀, fun Γ hΓ H hH1 hH2 η hη => ⟨_, hvol Γ hΓ H hH1 hH2 η hη,
    fun γ hγ hγB A hA F₀ hF₀ hF₀c hsupp => ?_⟩⟩
  have hΦ : offLineField γ ≤ η := not_lt.mp fun h => hγB ⟨hγ, h⟩
  have h := neg_offLineField_le_fullZeroForm hF₀ hF₀c hA hsupp γ
  have hK : 0 ≤ 4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hΦ hK
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
