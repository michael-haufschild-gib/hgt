import GaloisForLFunctions.GaloisTheoryOfZeros.TheHeatFamilyIsAnIntegralThroughTheOriginAndTheSaddle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The segment through the origin is a Gaussian at the centre value of the kernel

For `Re τ > 0` the factor `e^{−τv²}` concentrates the segment integral

`i ∫_0^η Φ(iv) e^{−τv² − zv} dv`

at `v = 0`, on the scale `(Re τ)^{−1/2}`. Its leading term is `(iΦ(0)/2)(π/τ)^{1/2}`, of the
modulus `|τ|^{−1/2}`, and the error is of the order `1/Re τ`.

* `stripConst`, `norm_kernelC_le_stripConst`: `|Φ(x)| ≤ K(η) e^{Re x/2}` for `Re x ≥ 0`,
  `|Im x| ≤ η < π/4`.
* `exists_norm_kernelC_sub_le`: `Φ` is Lipschitz at the origin.
* `exists_norm_bulkHalf_sub_le` (**bulk term**): for `Re τ > 0`, `1/2 ≤ η < π/4`, `|z| ≤ 1`,
  `|i∫_0^η Φ(iv)e^{−τv²−zv}dv − (iΦ(0)/2)(π/τ)^{1/2}| ≤ C(1 + K(η))/Re τ`, `C` absolute.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real Interval

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The kernel on a closed substrip -/

/-- The bound `K(η)` of `Φ(x)e^{−Re x/2}` on `Re x ≥ 0`, `|Im x| ≤ η`. -/
def stripConst (η : ℝ) : ℝ :=
  termConst riemannCuspPoly (π * Real.cos (2 * η) / 2) /
    (1 - Real.exp (-(π * Real.cos (2 * η) / 2)))

theorem stripConst_nonneg {η : ℝ} (h0 : 0 ≤ η) (hη : η < π / 4) : 0 ≤ stripConst η := by
  have hπ := Real.pi_pos
  have hκ : 0 < Real.cos (2 * η) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have ha0 : 0 < π * Real.cos (2 * η) / 2 := by positivity
  have hea : Real.exp (-(π * Real.cos (2 * η) / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1 := termConst_nonneg riemannCuspPoly ha0
  have h2 : 0 < 1 - Real.exp (-(π * Real.cos (2 * η) / 2)) := by linarith
  unfold stripConst
  positivity

/-- `|Φ(x)| ≤ K(η) e^{Re x/2}` for `Re x ≥ 0`, `|Im x| ≤ η < π/4`. -/
theorem norm_kernelC_le_stripConst {η : ℝ} (hη : η < π / 4) {x : ℂ} (hx : |x.im| ≤ η)
    (hre : 0 ≤ x.re) : ‖kernelC x‖ ≤ stripConst η * Real.exp (x.re / 2) := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hx
  have h := norm_cseries_le_of_re_nonneg riemannCuspPoly hη hx hre
  have hK := stripConst_nonneg hη0 hη
  have hπ := Real.pi_pos
  have hκ : 0 < Real.cos (2 * η) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h1 : Real.exp (-(π * Real.cos (2 * η) / 2 * Real.exp (2 * x.re))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ π * Real.cos (2 * η) / 2 * Real.exp (2 * x.re) := by positivity
    linarith
  calc ‖kernelC x‖ ≤ stripConst η * (Real.exp (x.re / 2) *
        Real.exp (-(π * Real.cos (2 * η) / 2 * Real.exp (2 * x.re)))) := h
    _ ≤ stripConst η * (Real.exp (x.re / 2) * 1) := by gcongr
    _ = stripConst η * Real.exp (x.re / 2) := by rw [mul_one]

/-- `Φ` is Lipschitz at the origin: `|Φ(x) − Φ(0)| ≤ L|x|` for `|x| ≤ 1/2`. -/
theorem exists_norm_kernelC_sub_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℂ, ‖x‖ ≤ 1 / 2 → ‖kernelC x - kernelC 0‖ ≤ L * ‖x‖ := by
  have hπ := Real.pi_gt_three
  have hsub : Metric.closedBall (0 : ℂ) (1 / 2) ⊆ strip := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx
    exact mem_strip.mpr (lt_of_le_of_lt ((Complex.abs_im_le_norm x).trans hx) (by linarith))
  have hd : DifferentiableOn ℂ kernelC strip := fun w hw =>
    (differentiableAt_kernelC (mem_strip.mp hw)).differentiableWithinAt
  have hcont : ContinuousOn (deriv kernelC) (Metric.closedBall (0 : ℂ) (1 / 2)) :=
    (hd.deriv isOpen_strip).continuousOn.mono hsub
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : ℂ) (1 / 2) := mem_closedBall_zero_iff.mpr hx
  have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (1 / 2) :=
    Metric.mem_closedBall_self (by norm_num)
  have h := (convex_closedBall (0 : ℂ) (1 / 2)).norm_image_sub_le_of_norm_deriv_le (f := kernelC)
    (fun w hw => differentiableAt_kernelC (mem_strip.mp (hsub hw)))
    (fun w hw => (hC w hw).trans (le_max_left C 0)) h0 hx'
  rwa [sub_zero] at h

/-- On the segment `[0, iη]`: `|Φ(iv)e^{−zv} − Φ(0)| ≤ 3(L + 2K(η) + 3|Φ(0)|) v` for `|z| ≤ 1`. -/
theorem norm_kernelC_mul_cexp_sub_le {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x : ℂ, ‖x‖ ≤ 1 / 2 → ‖kernelC x - kernelC 0‖ ≤ L * ‖x‖) {η : ℝ} (hη : η < π / 4)
    {z : ℂ} (hz : ‖z‖ ≤ 1) {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ η) :
    ‖kernelC (v * I) * cexp (-(z * v)) - kernelC 0‖ ≤
      3 * (L + 2 * stripConst η + 3 * ‖kernelC 0‖) * v := by
  have hπ := Real.pi_lt_d2
  have hv1 : v ≤ 1 := by linarith
  have hη0 : 0 ≤ η := hv0.trans hv
  have hK := stripConst_nonneg hη0 hη
  have hΦ := norm_nonneg (kernelC 0)
  have hnorm : ‖(v : ℂ) * I‖ = v := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
  have hre : ((v : ℂ) * I).re = 0 := by simp
  have him : ((v : ℂ) * I).im = v := by simp
  -- the kernel
  have hA : ‖kernelC (v * I) - kernelC 0‖ ≤ (L + 2 * stripConst η + 2 * ‖kernelC 0‖) * v := by
    rcases le_total v (1 / 2) with h | h
    · have h1 := hL (v * I) (by rw [hnorm]; exact h)
      rw [hnorm] at h1
      have h2 : 0 ≤ (2 * stripConst η + 2 * ‖kernelC 0‖) * v := by positivity
      linarith
    · have h1 : ‖kernelC (v * I)‖ ≤ stripConst η := by
        have h2 := norm_kernelC_le_stripConst hη (x := v * I)
          (by rw [him, abs_of_nonneg hv0]; exact hv) (by rw [hre])
        rwa [hre, zero_div, Real.exp_zero, mul_one] at h2
      have h3 : ‖kernelC (v * I) - kernelC 0‖ ≤ stripConst η + ‖kernelC 0‖ :=
        (norm_sub_le _ _).trans (by linarith)
      have h4 : stripConst η + ‖kernelC 0‖ ≤ (2 * stripConst η + 2 * ‖kernelC 0‖) * v := by
        nlinarith
      have h5 : 0 ≤ L * v := by positivity
      linarith
  have hnn : 0 ≤ (L + 2 * stripConst η + 2 * ‖kernelC 0‖) * v := by positivity
  -- the exponential
  have hzv : ‖-(z * (v : ℂ))‖ ≤ v := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
    calc ‖z‖ * v ≤ 1 * v := mul_le_mul_of_nonneg_right hz hv0
      _ = v := one_mul v
  have he3 : Real.exp v ≤ 3 := by
    have h1 : Real.exp v ≤ Real.exp 1 := Real.exp_le_exp.mpr hv1
    have h2 := Real.exp_one_lt_d9
    linarith
  have hE1 : ‖cexp (-(z * v))‖ ≤ 3 := by
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hzv)).trans he3
  have hE2 : ‖cexp (-(z * v)) - 1‖ ≤ 3 * v := by
    refine (norm_cexp_sub_one_le _).trans ?_
    calc ‖-(z * (v : ℂ))‖ * Real.exp ‖-(z * (v : ℂ))‖ ≤ v * Real.exp v :=
          mul_le_mul hzv (Real.exp_le_exp.mpr hzv) (Real.exp_pos _).le hv0
      _ ≤ v * 3 := mul_le_mul_of_nonneg_left he3 hv0
      _ = 3 * v := mul_comm _ _
  have e : kernelC (v * I) * cexp (-(z * v)) - kernelC 0 =
      (kernelC (v * I) - kernelC 0) * cexp (-(z * v)) + kernelC 0 * (cexp (-(z * v)) - 1) := by
    ring
  rw [e]
  calc ‖(kernelC (v * I) - kernelC 0) * cexp (-(z * v)) + kernelC 0 * (cexp (-(z * v)) - 1)‖
      ≤ ‖kernelC (v * I) - kernelC 0‖ * ‖cexp (-(z * v))‖ +
          ‖kernelC 0‖ * ‖cexp (-(z * v)) - 1‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul]
    _ ≤ (L + 2 * stripConst η + 2 * ‖kernelC 0‖) * v * 3 + ‖kernelC 0‖ * (3 * v) :=
        add_le_add (mul_le_mul hA hE1 (norm_nonneg _) hnn)
          (mul_le_mul_of_nonneg_left hE2 hΦ)
    _ = 3 * (L + 2 * stripConst η + 3 * ‖kernelC 0‖) * v := by ring

/-! ## Two elementary integrals -/

theorem norm_cexp_neg_mul_sq (τ : ℂ) (v : ℝ) :
    ‖cexp (-τ * (v : ℂ) ^ 2)‖ = Real.exp (-(τ.re * v ^ 2)) := by
  have e : -τ * (v : ℂ) ^ 2 = (-τ) * ((v ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.norm_exp, e, Complex.re_mul_ofReal, Complex.neg_re, neg_mul]

/-- `∫_0^η v e^{−tv²} dv ≤ 1/(2t)`. -/
theorem integral_mul_exp_neg_mul_sq_le {t : ℝ} (ht : 0 < t) (η : ℝ) :
    ∫ v in (0 : ℝ)..η, v * Real.exp (-(t * v ^ 2)) ≤ 1 / (2 * t) := by
  have ht' : t ≠ 0 := ht.ne'
  have hd : ∀ v ∈ uIcc (0 : ℝ) η,
      HasDerivAt (fun v : ℝ => -(Real.exp (-(t * v ^ 2)) / (2 * t)))
        (v * Real.exp (-(t * v ^ 2))) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => -(t * v ^ 2)) (-(t * (2 * v))) v := by
      refine ((hasDerivAt_pow 2 v).const_mul t).neg.congr_deriv ?_
      norm_num
    refine (h1.exp.div_const (2 * t)).neg.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun v : ℝ => v * Real.exp (-(t * v ^ 2))) volume 0 η :=
    (by fun_prop : Continuous fun v : ℝ => v * Real.exp (-(t * v ^ 2))).intervalIntegrable _ _
  have key : ∫ v in (0 : ℝ)..η, v * Real.exp (-(t * v ^ 2)) =
      -(Real.exp (-(t * η ^ 2)) / (2 * t)) - -(Real.exp (-(t * (0 : ℝ) ^ 2)) / (2 * t)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  have e0 : Real.exp (-(t * (0 : ℝ) ^ 2)) = 1 := by norm_num
  have h1 : 0 < Real.exp (-(t * η ^ 2)) / (2 * t) := by positivity
  rw [key, e0]
  linarith

/-- `∫_η^∞ e^{−tv²} dv ≤ 1/(tη)`. -/
theorem integral_Ioi_exp_neg_mul_sq_le {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∫ v in Ioi η, Real.exp (-(t * v ^ 2)) ≤ 1 / (t * η) := by
  have h4 : 0 < t * η := mul_pos ht hη
  have ha : -(t * η) < 0 := by linarith
  have h1 : IntegrableOn (fun v : ℝ => Real.exp (-(t * η) * v)) (Ioi η) :=
    integrableOn_exp_mul_Ioi ha η
  have h0 : IntegrableOn (fun v : ℝ => Real.exp (-(t * v ^ 2))) (Ioi η) := by
    have h := (integrable_exp_neg_mul_sq ht).integrableOn (s := Ioi η)
    simpa only [neg_mul] using h
  have h2 : ∫ v in Ioi η, Real.exp (-(t * v ^ 2)) ≤ ∫ v in Ioi η, Real.exp (-(t * η) * v) := by
    refine setIntegral_mono_on h0 h1 measurableSet_Ioi fun v hv => Real.exp_le_exp.mpr ?_
    have hv' : η < v := hv
    nlinarith [mul_nonneg (mul_nonneg ht.le (hη.le.trans hv'.le)) (sub_nonneg.mpr hv'.le)]
  rw [integral_exp_mul_Ioi ha η, neg_div_neg_eq] at h2
  refine h2.trans (div_le_div_of_nonneg_right ?_ h4.le)
  refine Real.exp_le_one_iff.mpr ?_
  nlinarith

/-! ## The bulk term -/

/-- **The bulk term.** For `Re τ > 0`, `1/2 ≤ η < π/4` and `|z| ≤ 1` the segment integral is
`(iΦ(0)/2)(π/τ)^{1/2}` up to `C(1 + K(η))/Re τ`: the kernel is replaced by its centre value
(Lipschitz bound) and the Gaussian is completed to the half line. -/
theorem exists_norm_bulkHalf_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ z : ℂ) (η : ℝ), 0 < τ.re → 1 / 2 ≤ η → η < π / 4 → ‖z‖ ≤ 1 →
      ‖bulkHalf τ η z - I * kernelC 0 / 2 * ((π : ℂ) / τ) ^ (1 / 2 : ℂ)‖ ≤
        C * (1 + stripConst η) / τ.re := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_kernelC_sub_le
  refine ⟨3 * L + 11 * ‖kernelC 0‖ + 6, by positivity, fun τ z η hτ hη2 hη hz => ?_⟩
  have hη0 : 0 ≤ η := by linarith
  have hK := stripConst_nonneg hη0 hη
  have hΦ := norm_nonneg (kernelC 0)
  set t := τ.re with ht
  set L' : ℝ := 3 * (L + 2 * stripConst η + 3 * ‖kernelC 0‖) with hL'
  have hL'0 : 0 ≤ L' := by positivity
  set G : ℝ → ℂ := fun v => cexp (-τ * (v : ℂ) ^ 2) with hG
  have hGn : ∀ v : ℝ, ‖G v‖ = Real.exp (-(t * v ^ 2)) := fun v => norm_cexp_neg_mul_sq τ v
  have hGi : Integrable G := integrable_cexp_neg_mul_sq hτ
  have hGc : Continuous G := by simp only [hG]; fun_prop
  -- the Gaussian of the centre value
  have hgauss : (∫ v in (0 : ℝ)..η, G v) + ∫ v in Ioi η, G v =
      ((π : ℂ) / τ) ^ (1 / 2 : ℂ) / 2 := by
    rw [intervalIntegral.integral_interval_add_Ioi hGi.integrableOn hGi.integrableOn]
    exact integral_gaussian_complex_Ioi hτ
  -- the segment
  set g : ℝ → ℂ := fun v => kernelC (v * I) * cexp (-(τ * (v : ℂ) ^ 2) - z * v) with hg
  have hb : bulkHalf τ η z = I * ∫ v in (0 : ℝ)..η, g v := rfl
  have hkc : ContinuousOn (fun v : ℝ => kernelC (v * I)) (uIcc 0 η) := by
    intro v hv
    rw [uIcc_of_le hη0] at hv
    have him : ((v : ℂ) * I).im = v := by simp
    have hd : DifferentiableAt ℂ kernelC ((v : ℂ) * I) :=
      differentiableAt_kernelC (by rw [him, abs_of_nonneg hv.1]; exact lt_of_le_of_lt hv.2 hη)
    exact (hd.continuousAt.comp (f := fun v : ℝ => (v : ℂ) * I)
      (by fun_prop)).continuousWithinAt
  have hgi : IntervalIntegrable g volume 0 η :=
    (hkc.mul (Continuous.continuousOn (by fun_prop))).intervalIntegrable
  have hGii : IntervalIntegrable G volume 0 η := hGc.intervalIntegrable _ _
  have hdecomp : bulkHalf τ η z - I * kernelC 0 / 2 * ((π : ℂ) / τ) ^ (1 / 2 : ℂ) =
      I * (∫ v in (0 : ℝ)..η, (g v - kernelC 0 * G v)) -
        I * kernelC 0 * ∫ v in Ioi η, G v := by
    rw [intervalIntegral.integral_sub hgi (hGii.const_mul (kernelC 0)),
      intervalIntegral.integral_const_mul, hb]
    linear_combination (I * kernelC 0) * hgauss
  -- pointwise: the kernel at its centre value
  have hpt : ∀ v ∈ Icc (0 : ℝ) η,
      ‖g v - kernelC 0 * G v‖ ≤ L' * (v * Real.exp (-(t * v ^ 2))) := by
    intro v hv
    have e : g v - kernelC 0 * G v = (kernelC (v * I) * cexp (-(z * v)) - kernelC 0) * G v := by
      simp only [hg, hG]
      rw [show -(τ * (v : ℂ) ^ 2) - z * v = -(z * v) + -τ * (v : ℂ) ^ 2 by ring, Complex.exp_add]
      ring
    rw [e, norm_mul, hGn]
    have h1 := norm_kernelC_mul_cexp_sub_le hL0 hL hη hz hv.1 hv.2
    calc ‖kernelC (v * I) * cexp (-(z * v)) - kernelC 0‖ * Real.exp (-(t * v ^ 2))
        ≤ L' * v * Real.exp (-(t * v ^ 2)) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = L' * (v * Real.exp (-(t * v ^ 2))) := mul_assoc _ _ _
  have hA : ‖∫ v in (0 : ℝ)..η, (g v - kernelC 0 * G v)‖ ≤ L' / (2 * t) := by
    have hc1 : IntervalIntegrable (fun v : ℝ => ‖g v - kernelC 0 * G v‖) volume 0 η :=
      (hgi.sub (hGii.const_mul (kernelC 0))).norm
    have hc2 : IntervalIntegrable (fun v : ℝ => L' * (v * Real.exp (-(t * v ^ 2)))) volume 0 η :=
      (by fun_prop : Continuous fun v : ℝ =>
        L' * (v * Real.exp (-(t * v ^ 2)))).intervalIntegrable _ _
    calc ‖∫ v in (0 : ℝ)..η, (g v - kernelC 0 * G v)‖
        ≤ ∫ v in (0 : ℝ)..η, ‖g v - kernelC 0 * G v‖ :=
          intervalIntegral.norm_integral_le_integral_norm hη0
      _ ≤ ∫ v in (0 : ℝ)..η, L' * (v * Real.exp (-(t * v ^ 2))) :=
          intervalIntegral.integral_mono_on hη0 hc1 hc2 hpt
      _ = L' * ∫ v in (0 : ℝ)..η, v * Real.exp (-(t * v ^ 2)) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ L' * (1 / (2 * t)) :=
          mul_le_mul_of_nonneg_left (integral_mul_exp_neg_mul_sq_le hτ η) hL'0
      _ = L' / (2 * t) := by ring
  -- the Gaussian beyond the segment
  have hT : ‖∫ v in Ioi η, G v‖ ≤ 2 / t := by
    have hη' : 0 < η := by linarith
    have h1 : ‖∫ v in Ioi η, G v‖ ≤ ∫ v in Ioi η, ‖G v‖ := norm_integral_le_integral_norm _
    simp only [hGn] at h1
    refine h1.trans ((integral_Ioi_exp_neg_mul_sq_le hτ hη').trans ?_)
    rw [div_le_div_iff₀ (by positivity) hτ]
    nlinarith [mul_le_mul_of_nonneg_left hη2 hτ.le]
  rw [hdecomp]
  calc ‖I * (∫ v in (0 : ℝ)..η, (g v - kernelC 0 * G v)) - I * kernelC 0 * ∫ v in Ioi η, G v‖
      ≤ ‖∫ v in (0 : ℝ)..η, (g v - kernelC 0 * G v)‖ +
          ‖kernelC 0‖ * ‖∫ v in Ioi η, G v‖ := by
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul, Complex.norm_I, one_mul]
    _ ≤ L' / (2 * t) + ‖kernelC 0‖ * (2 / t) :=
        add_le_add hA (mul_le_mul_of_nonneg_left hT hΦ)
    _ = (L' / 2 + 2 * ‖kernelC 0‖) / t := by
        field_simp
    _ ≤ (3 * L + 11 * ‖kernelC 0‖ + 6) * (1 + stripConst η) / t := by
        refine div_le_div_of_nonneg_right ?_ hτ.le
        rw [hL']
        nlinarith [mul_nonneg hL0 hK, mul_nonneg hΦ hK]

end

end GaloisForLFunctions.GaloisTheoryOfZeros
