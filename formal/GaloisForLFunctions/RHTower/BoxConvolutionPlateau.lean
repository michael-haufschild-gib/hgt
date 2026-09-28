import GaloisForLFunctions.RHTower.TiltedKernelResolventTest

/-!
# Smooth plateaus with exponentially decaying transforms

`boxPower A h n = 1_{[-A,A]} ⋆ B_h^{⋆n}`, with `B_h` the unit-mass box of half-width `h`, has
transform `∫_{-A}^{A} e^{izu} du · (sin(hz)/(hz))^n`. Smoothing once more with a normalised
`C^∞` bump of radius `r` gives the plateau `boxPlateau A h n r`:

* `C^∞`, equal to `1` on `|u| ≤ A - nh - r` and `0` for `|u| ≥ A + nh + r`;
* `|b̂(z)| ≤ (2e^{A|y|}/|z|)·(e^{h|y|}/(h|z|))^n·e^{r|y|}` for `z = x + iy ≠ 0`.

With `n ≍ h|x|` the last factor is `e^{-n}`: exponential decay at a prescribed frequency, which a
fixed `C^∞` bump cannot give.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## The unit box -/

/-- The unit-mass box of half-width `h`. -/
def unitBox (h : ℝ) : ℝ → ℂ := (Icc (-h) h).indicator (fun _ => ((1 / (2 * h) : ℝ) : ℂ))

theorem unitBox_eq_zero {h u : ℝ} (hu : h < |u|) : unitBox h u = 0 := by
  unfold unitBox
  refine indicator_of_notMem (fun hm => ?_) _
  have := abs_le.mpr ⟨hm.1, hm.2⟩
  linarith

theorem norm_unitBox_le {h : ℝ} (hh : 0 < h) (u : ℝ) : ‖unitBox h u‖ ≤ 1 / (2 * h) := by
  unfold unitBox
  by_cases hu : u ∈ Icc (-h) h
  · rw [indicator_of_mem hu, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  · rw [indicator_of_notMem hu, norm_zero]; positivity

theorem integrable_unitBox (h : ℝ) : Integrable (unitBox h) :=
  (continuous_const.integrableOn_Icc (μ := volume)).integrable_indicator measurableSet_Icc

theorem integral_unitBox {h : ℝ} (hh : 0 < h) : ∫ u, unitBox h u = 1 := by
  unfold unitBox
  rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le
    (by linarith), Complex.real_smul]
  have h2 : (2 * h : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * h : ℝ) ≠ 0)
  push_cast
  field_simp
  ring_nf
  rw [mul_inv_cancel₀ (by exact_mod_cast hh.ne'), one_mul]

/-! ## Iterated box smoothing of an interval -/

/-- `1_{[-A,A]} ⋆ B_h^{⋆n}`. -/
def boxPower (A h : ℝ) : ℕ → ℝ → ℂ
  | 0 => (Icc (-A) A).indicator (fun _ => 1)
  | n + 1 => convolution (boxPower A h n) (unitBox h) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem boxPower_zero (A h : ℝ) : boxPower A h 0 = (Icc (-A) A).indicator (fun _ => 1) := rfl

theorem boxPower_succ (A h : ℝ) (n : ℕ) : boxPower A h (n + 1) =
    convolution (boxPower A h n) (unitBox h) (ContinuousLinearMap.mul ℝ ℂ) volume := rfl

theorem integrable_boxPower (A h : ℝ) : ∀ n, Integrable (boxPower A h n)
  | 0 => (continuous_const.integrableOn_Icc (μ := volume)).integrable_indicator measurableSet_Icc
  | n + 1 => (integrable_boxPower A h n).integrable_convolution _ (integrable_unitBox h)

/-- The value of one box smoothing: `(G ⋆ B_h)(x) = ∫ G(t) B_h(x - t) dt`. -/
theorem boxPower_succ_apply (A h : ℝ) (n : ℕ) (x : ℝ) :
    boxPower A h (n + 1) x = ∫ t, boxPower A h n t * unitBox h (x - t) := by
  rw [boxPower_succ, convolution_def]; rfl

theorem integral_unitBox_sub {h : ℝ} (hh : 0 < h) (x : ℝ) : ∫ t, unitBox h (x - t) = 1 := by
  rw [integral_sub_left_eq_self (fun t => unitBox h t) volume x, integral_unitBox hh]

theorem norm_boxPower_le {A h : ℝ} (hh : 0 < h) : ∀ n x, ‖boxPower A h n x‖ ≤ 1
  | 0, x => by
    rw [boxPower_zero]
    by_cases hx : x ∈ Icc (-A) A
    · rw [indicator_of_mem hx, norm_one]
    · rw [indicator_of_notMem hx, norm_zero]; norm_num
  | n + 1, x => by
    rw [boxPower_succ_apply]
    have hint : Integrable (fun t => unitBox h (x - t)) :=
      (integrable_unitBox h).comp_sub_left x
    calc ‖∫ t, boxPower A h n t * unitBox h (x - t)‖
        ≤ ∫ t, ‖boxPower A h n t * unitBox h (x - t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, ‖unitBox h (x - t)‖ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            hint.norm (Eventually.of_forall fun t => ?_)
          simp only [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (norm_boxPower_le hh n t)
      _ = 1 := by
          have : ∀ t, ‖unitBox h (x - t)‖ = (unitBox h (x - t)).re := by
            intro t
            unfold unitBox
            by_cases hm : x - t ∈ Icc (-h) h
            · rw [indicator_of_mem hm, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
                abs_of_pos (by positivity)]
            · rw [indicator_of_notMem hm, norm_zero, Complex.zero_re]
          simp_rw [this]
          have h1 := integral_re hint
          simp only [RCLike.re_to_complex] at h1
          rw [h1, integral_unitBox_sub hh, Complex.one_re]

theorem boxPower_eq_zero {A h : ℝ} (hh : 0 < h) : ∀ (n : ℕ) {x : ℝ}, A + n * h < |x| →
    boxPower A h n x = 0
  | 0, x, hx => by
    rw [boxPower_zero]
    refine indicator_of_notMem (fun hm => ?_) _
    have := abs_le.mpr ⟨hm.1, hm.2⟩
    push_cast at hx; linarith
  | n + 1, x, hx => by
    rw [boxPower_succ_apply]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    simp only [Pi.zero_apply]
    by_cases ht : h < |x - t|
    · rw [unitBox_eq_zero ht, mul_zero]
    · push Not at ht
      have : A + n * h < |t| := by
        have := abs_sub_abs_le_abs_sub x t
        push_cast at hx; linarith
      rw [boxPower_eq_zero hh n this, zero_mul]

theorem boxPower_eq_one {A h : ℝ} (hh : 0 < h) : ∀ (n : ℕ) {x : ℝ}, |x| ≤ A - n * h →
    boxPower A h n x = 1
  | 0, x, hx => by
    rw [boxPower_zero]
    push_cast at hx
    exact indicator_of_mem (show x ∈ Icc (-A) A from
      ⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩) _
  | n + 1, x, hx => by
    rw [boxPower_succ_apply]
    have e : ∀ t, boxPower A h n t * unitBox h (x - t) = unitBox h (x - t) := by
      intro t
      by_cases ht : h < |x - t|
      · rw [unitBox_eq_zero ht, mul_zero]
      · push Not at ht
        have : |t| ≤ A - n * h := by
          have := abs_sub_abs_le_abs_sub t x
          rw [abs_sub_comm t x] at this
          push_cast at hx; linarith
        rw [boxPower_eq_one hh n this, one_mul]
    simp_rw [e]
    exact integral_unitBox_sub hh x

/-! ## Transforms -/

theorem boxPower_support {A h : ℝ} (hh : 0 < h) (n : ℕ) :
    ∀ u, A + n * h < |u| → boxPower A h n u = 0 :=
  fun _ hu => boxPower_eq_zero hh n hu

theorem paperFT_boxPower {A h : ℝ} (hh : 0 < h) (z : ℂ) : ∀ n : ℕ,
    paperFT (boxPower A h n) z = paperFT (boxPower A h 0) z * paperFT (unitBox h) z ^ n
  | 0 => by simp
  | n + 1 => by
    rw [boxPower_succ, paperFT_convolution
      (integrable_mul_cexp_of_support (integrable_boxPower A h n) (boxPower_support hh n) z)
      (integrable_mul_cexp_of_support (integrable_unitBox h) (fun _ hu => unitBox_eq_zero hu) z),
      paperFT_boxPower hh z n, pow_succ]
    ring

/-- `∫_{-a}^{a} e^{izu} du`, bounded by `2e^{a|Im z|}/|z|`. -/
theorem norm_setIntegral_Icc_cexp_le {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z ≠ 0) :
    ‖∫ u in Icc (-a) a, Complex.exp (I * z * u)‖ ≤ 2 * Real.exp (a * |z.im|) / ‖z‖ := by
  have hIz : I * z ≠ 0 := mul_ne_zero I_ne_zero hz
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    integral_exp_mul_complex hIz, norm_div, norm_mul, Complex.norm_I, one_mul]
  have hb : ∀ v : ℝ, |v| ≤ a → ‖Complex.exp (I * z * v)‖ ≤ Real.exp (a * |z.im|) := by
    intro v hv
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (I * z * (v : ℂ)).re = -(z.im * v) := by simp
    rw [this]
    have h1 : -(z.im * v) ≤ |z.im * v| := neg_le_abs _
    rw [abs_mul] at h1
    nlinarith [abs_nonneg z.im]
  have h1 := hb a (by rw [abs_of_nonneg ha])
  have h2 := hb (-a) (by rw [abs_neg, abs_of_nonneg ha])
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [div_le_div_iff_of_pos_right hn]
  calc ‖Complex.exp (I * z * a) - Complex.exp (I * z * ((-a : ℝ) : ℂ))‖
      ≤ ‖Complex.exp (I * z * a)‖ + ‖Complex.exp (I * z * ((-a : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ ≤ 2 * Real.exp (a * |z.im|) := by linarith

theorem paperFT_boxPower_zero_eq (A h : ℝ) (z : ℂ) :
    paperFT (boxPower A h 0) z = ∫ u in Icc (-A) A, Complex.exp (I * z * u) := by
  unfold paperFT
  rw [boxPower_zero, ← integral_indicator measurableSet_Icc]
  congr 1; funext u
  by_cases hu : u ∈ Icc (-A) A
  · rw [indicator_of_mem hu, indicator_of_mem hu, one_mul]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]

theorem paperFT_unitBox_eq (h : ℝ) (z : ℂ) :
    paperFT (unitBox h) z = ((1 / (2 * h) : ℝ) : ℂ) * ∫ u in Icc (-h) h, Complex.exp (I * z * u) := by
  unfold paperFT unitBox
  rw [← integral_const_mul, ← integral_indicator measurableSet_Icc]
  congr 1; funext u
  by_cases hu : u ∈ Icc (-h) h
  · rw [indicator_of_mem hu, indicator_of_mem hu]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]

theorem norm_paperFT_boxPower_zero_le {A h : ℝ} (hA : 0 ≤ A) {z : ℂ} (hz : z ≠ 0) :
    ‖paperFT (boxPower A h 0) z‖ ≤ 2 * Real.exp (A * |z.im|) / ‖z‖ := by
  rw [paperFT_boxPower_zero_eq]; exact norm_setIntegral_Icc_cexp_le hA hz

theorem norm_paperFT_unitBox_le {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z ≠ 0) :
    ‖paperFT (unitBox h) z‖ ≤ Real.exp (h * |z.im|) / (h * ‖z‖) := by
  rw [paperFT_unitBox_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have := norm_setIntegral_Icc_cexp_le hh.le hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  calc 1 / (2 * h) * ‖∫ u in Icc (-h) h, Complex.exp (I * z * u)‖
      ≤ 1 / (2 * h) * (2 * Real.exp (h * |z.im|) / ‖z‖) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = Real.exp (h * |z.im|) / (h * ‖z‖) := by field_simp

/-! ## The smooth unit-mass bump -/

/-- The `C^∞` bump of radius `r` with `rIn = r/2`. -/
def radiusBump {r : ℝ} (hr : 0 < r) : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩

/-- A `C^∞` unit-mass bump of radius `r` (zero for `r ≤ 0`). -/
def smoothUnitBump (r : ℝ) : ℝ → ℂ :=
  if hr : 0 < r then fun u => (((radiusBump hr).normed volume u : ℝ) : ℂ) else 0

theorem smoothUnitBump_eq {r : ℝ} (hr : 0 < r) (u : ℝ) :
    smoothUnitBump r u = (((radiusBump hr).normed volume u : ℝ) : ℂ) := by
  simp [smoothUnitBump, hr]

theorem contDiff_smoothUnitBump {r : ℝ} (hr : 0 < r) {n : ℕ∞} :
    ContDiff ℝ n (smoothUnitBump r) := by
  have : smoothUnitBump r = fun u => (((radiusBump hr).normed volume u : ℝ) : ℂ) :=
    funext (smoothUnitBump_eq hr)
  rw [this]
  exact Complex.ofRealCLM.contDiff.comp (radiusBump hr).contDiff_normed

theorem smoothUnitBump_eq_zero {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : r ≤ |u|) :
    smoothUnitBump r u = 0 := by
  rw [smoothUnitBump_eq hr]
  have h : u ∉ Function.support ((radiusBump hr).normed volume) := by
    rw [(radiusBump hr).support_normed_eq]
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hu
  rw [Function.notMem_support.mp h, Complex.ofReal_zero]

theorem hasCompactSupport_smoothUnitBump {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (smoothUnitBump r) :=
  hasCompactSupport_of_support_subset_abs (Λ := r) fun u hu => by
    by_contra h; push Not at h; exact hu (smoothUnitBump_eq_zero hr h.le)

theorem norm_smoothUnitBump {r : ℝ} (hr : 0 < r) (u : ℝ) :
    ‖smoothUnitBump r u‖ = (radiusBump hr).normed volume u := by
  rw [smoothUnitBump_eq hr, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((radiusBump hr).nonneg_normed u)]

theorem integrable_smoothUnitBump {r : ℝ} (hr : 0 < r) : Integrable (smoothUnitBump r) :=
  (contDiff_smoothUnitBump hr (n := 0)).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_smoothUnitBump hr)

theorem integral_smoothUnitBump_sub {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∫ t, smoothUnitBump r (x - t) = 1 := by
  rw [integral_sub_left_eq_self (fun t => smoothUnitBump r t) volume x]
  simp_rw [smoothUnitBump_eq hr]
  rw [integral_complex_ofReal, (radiusBump hr).integral_normed, Complex.ofReal_one]

theorem norm_paperFT_smoothUnitBump_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖paperFT (smoothUnitBump r) z‖ ≤ Real.exp (r * |z.im|) := by
  unfold paperFT
  have hint : Integrable (fun u => (radiusBump hr).normed volume u) :=
    (radiusBump hr).integrable_normed
  calc ‖∫ u, smoothUnitBump r u * Complex.exp (I * z * u)‖
      ≤ ∫ u, ‖smoothUnitBump r u * Complex.exp (I * z * u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, (radiusBump hr).normed volume u * Real.exp (r * |z.im|) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hint.mul_const _) (Eventually.of_forall fun u => ?_)
        simp only
        rw [norm_mul, norm_smoothUnitBump hr]
        by_cases hu : r ≤ |u|
        · have h0 : (radiusBump hr).normed volume u = 0 := by
            have := smoothUnitBump_eq_zero hr hu
            rw [smoothUnitBump_eq hr, Complex.ofReal_eq_zero] at this; exact this
          rw [h0, zero_mul, zero_mul]
        · push Not at hu
          refine mul_le_mul_of_nonneg_left ?_ ((radiusBump hr).nonneg_normed u)
          rw [Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          have : (I * z * (u : ℂ)).re = -(z.im * u) := by simp
          rw [this]
          have h1 : -(z.im * u) ≤ |z.im| * |u| := by
            rw [← abs_mul]; exact neg_le_abs _
          nlinarith [abs_nonneg z.im]
    _ = Real.exp (r * |z.im|) := by
        rw [integral_mul_const, (radiusBump hr).integral_normed, one_mul]

/-! ## The plateau -/

/-- `b = 1_{[-A,A]} ⋆ B_h^{⋆n} ⋆ β_r`. -/
def boxPlateau (A h : ℝ) (n : ℕ) (r : ℝ) : ℝ → ℂ :=
  convolution (boxPower A h n) (smoothUnitBump r) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem contDiff_boxPlateau {A h r : ℝ} (hr : 0 < r) (n : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (boxPlateau A h n r) :=
  (hasCompactSupport_smoothUnitBump hr).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) (integrable_boxPower A h n).locallyIntegrable
    (contDiff_smoothUnitBump hr)

theorem boxPlateau_apply (A h : ℝ) (n : ℕ) (r x : ℝ) :
    boxPlateau A h n r x = ∫ t, boxPower A h n t * smoothUnitBump r (x - t) := by
  rw [boxPlateau, convolution_def]; rfl

theorem boxPlateau_eq_one {A h r : ℝ} (hh : 0 < h) (hr : 0 < r) (n : ℕ) {x : ℝ}
    (hx : |x| ≤ A - n * h - r) : boxPlateau A h n r x = 1 := by
  rw [boxPlateau_apply]
  have e : ∀ t, boxPower A h n t * smoothUnitBump r (x - t) = smoothUnitBump r (x - t) := by
    intro t
    by_cases ht : r ≤ |x - t|
    · rw [smoothUnitBump_eq_zero hr ht, mul_zero]
    · push Not at ht
      have : |t| ≤ A - n * h := by
        have := abs_sub_abs_le_abs_sub t x
        rw [abs_sub_comm t x] at this
        linarith
      rw [boxPower_eq_one hh n this, one_mul]
  simp_rw [e]
  exact integral_smoothUnitBump_sub hr x

theorem boxPlateau_eq_zero {A h r : ℝ} (hh : 0 < h) (hr : 0 < r) (n : ℕ) {x : ℝ}
    (hx : A + n * h + r ≤ |x|) : boxPlateau A h n r x = 0 := by
  rw [boxPlateau_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  simp only [Pi.zero_apply]
  by_cases ht : r ≤ |x - t|
  · rw [smoothUnitBump_eq_zero hr ht, mul_zero]
  · push Not at ht
    have : A + n * h < |t| := by
      have := abs_sub_abs_le_abs_sub x t
      linarith
    rw [boxPower_eq_zero hh n this, zero_mul]

theorem paperFT_boxPlateau {A h r : ℝ} (hh : 0 < h) (hr : 0 < r) (n : ℕ) (z : ℂ) :
    paperFT (boxPlateau A h n r) z =
      paperFT (boxPower A h 0) z * paperFT (unitBox h) z ^ n * paperFT (smoothUnitBump r) z := by
  rw [boxPlateau, paperFT_convolution
    (integrable_mul_cexp_of_support (integrable_boxPower A h n) (boxPower_support hh n) z)
    (integrable_mul_cexp_of_support (integrable_smoothUnitBump hr)
      (fun _ hu => smoothUnitBump_eq_zero hr hu.le) z), paperFT_boxPower hh z n]

/-- **Decay of the plateau transform.** For `z ≠ 0`,
`|b̂(z)| ≤ (2e^{A|y|}/|z|)·(e^{h|y|}/(h|z|))^n·e^{r|y|}`, `y = Im z`. -/
theorem norm_paperFT_boxPlateau_le {A h r : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ)
    {z : ℂ} (hz : z ≠ 0) :
    ‖paperFT (boxPlateau A h n r) z‖ ≤
      2 * Real.exp (A * |z.im|) / ‖z‖ * (Real.exp (h * |z.im|) / (h * ‖z‖)) ^ n *
        Real.exp (r * |z.im|) := by
  rw [paperFT_boxPlateau hh hr, norm_mul, norm_mul, norm_pow]
  have h1 := norm_paperFT_boxPower_zero_le (h := h) hA hz
  have h2 := norm_paperFT_unitBox_le hh hz
  have h3 := norm_paperFT_smoothUnitBump_le hr z
  gcongr

end

end RHTower
