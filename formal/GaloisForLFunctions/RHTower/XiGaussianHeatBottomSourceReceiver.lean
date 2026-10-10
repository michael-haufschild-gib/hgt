import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalLineReceiver
import GaloisForLFunctions.RHTower.XiGaussianExplicitFormula

/-!
# The arithmetic bottom-source form of the single vertical-line receiver

On the horizontal line `Im z = -1` of the centered coordinate (`s = 3/2 + ix`) the logarithmic
derivative `logDeriv XiC (x - i)` is the completed prime–Gamma source: absolutely convergent von
Mangoldt series plus Gamma and pole terms (`xiGaussianCompletedBottomSource_eq_neg_I_mul_XiLog`).
For complex time `τ` set

`J(τ) = ∫_ℝ exp(-τ (x - i)²) · logDeriv XiC (x - i) dx`

(`xiGaussianBottomSourceC`).

* `J` is holomorphic on `Re τ > 0` (`differentiableAt_xiGaussianBottomSourceC`).  The Gaussian factor
  at complex time is dominated by a real-time one,
  `‖exp(-τ(x-i)²)‖ ≤ exp(σ₂ + 2R²/σ₁) ‖exp(-(σ₁/2)(x-i)²)‖`
  (`norm_exp_neg_mul_sub_I_sq_le`), and the real-time bottom integrands are integrable.
* The corpus explicit formula `xiGaussianHeatMoment_eq_completedBottomSource_div_pi` holds for real
  time.  The identity theorem continues it to the right half-plane:
  `ν(τ) = -(i/π) J(τ)` (`xiGaussianHeatTraceC_eq_bottomSource`).

**Theorem** (`riemannHypothesis_iff_xiGaussianBottomSourceC_bounded_on_vertical_line`).  For every
`a > 0`, RH holds iff `b ↦ J(a + ib)` is bounded.  The left side involves only the zeros, the right
side only the prime–Gamma source on `Re s = 3/2`, and no height parameter remains.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The complex-time bottom source. -/
def xiGaussianBottomSourceC (τ : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-τ * ((x : ℂ) - I) ^ (2 : ℕ)) * logDeriv XiC ((x : ℂ) - I)

theorem re_neg_mul_sub_I_sq (τ : ℂ) (x : ℝ) :
    (-τ * ((x : ℂ) - I) ^ (2 : ℕ)).re = -(τ.re * (x ^ 2 - 1) + 2 * τ.im * x) := by
  have hre : (((x : ℂ) - I) ^ (2 : ℕ)).re = x ^ 2 - 1 := by
    simp only [pow_two, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im]; ring
  have him : (((x : ℂ) - I) ^ (2 : ℕ)).im = -(2 * x) := by
    simp only [pow_two, mul_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im]; ring
  rw [neg_mul, neg_re, mul_re, hre, him]
  ring

/-- **Complex-time Gaussian domination.**  If `σ₁ ≤ Re τ ≤ σ₂` and `|Im τ| ≤ R`, the complex-time
Gaussian on the bottom line is dominated by the real-time Gaussian at `σ₁/2`. -/
theorem norm_exp_neg_mul_sub_I_sq_le {σ₁ σ₂ R : ℝ} (hσ₁ : 0 < σ₁) {τ : ℂ} (h1 : σ₁ ≤ τ.re)
    (h2 : τ.re ≤ σ₂) (hR : |τ.im| ≤ R) (x : ℝ) :
    ‖Complex.exp (-τ * ((x : ℂ) - I) ^ (2 : ℕ))‖ ≤
      Real.exp (σ₂ + 2 * R ^ 2 / σ₁) *
        ‖Complex.exp (-((σ₁ / 2 : ℝ) : ℂ) * ((x : ℂ) - I) ^ (2 : ℕ))‖ := by
  rw [Complex.norm_exp, Complex.norm_exp, re_neg_mul_sub_I_sq, re_neg_mul_sub_I_sq, ← Real.exp_add]
  apply Real.exp_le_exp.2
  simp only [ofReal_re, ofReal_im]
  have hbx : -(2 * τ.im * x) ≤ 2 * R * |x| := by
    have := abs_le.1 hR
    have hx := abs_nonneg x
    cases abs_cases x <;> nlinarith
  have hsq : 2 * R * |x| ≤ σ₁ / 2 * x ^ 2 + 2 * R ^ 2 / σ₁ := by
    have h := sq_nonneg (σ₁ / 2 * |x| - R)
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    have : σ₁ / 2 * x ^ 2 + 2 * R ^ 2 / σ₁ - 2 * R * |x| =
        (σ₁ / 2 * |x| - R) ^ 2 * (2 / σ₁) := by
      field_simp
      rw [← hx2]
      ring
    nlinarith [div_pos two_pos hσ₁]
  have hre : -(τ.re * (x ^ 2 - 1)) ≤ σ₂ - σ₁ * x ^ 2 := by nlinarith [sq_nonneg x]
  nlinarith

theorem xiGaussianBottomXiLogIntegrand_zero (t : ℝ) (x : ℝ) :
    xiGaussianBottomXiLogIntegrand t 0 1 x =
      Complex.exp (-(t : ℂ) * ((x : ℂ) - I) ^ (2 : ℕ)) * logDeriv XiC ((x : ℂ) - I) := by
  simp [xiGaussianBottomXiLogIntegrand, xiGaussianTestC]

theorem xiGaussianBottomXiLogIntegrand_one (t : ℝ) (x : ℝ) :
    xiGaussianBottomXiLogIntegrand t 1 1 x =
      ((x : ℂ) - I) ^ (2 : ℕ) * Complex.exp (-(t : ℂ) * ((x : ℂ) - I) ^ (2 : ℕ)) *
        logDeriv XiC ((x : ℂ) - I) := by
  simp [xiGaussianBottomXiLogIntegrand, xiGaussianTestC]

theorem measurable_logDeriv_XiC_bottom : Measurable (fun x : ℝ => logDeriv XiC ((x : ℂ) - I)) := by
  have hXi : Continuous XiC :=
    continuous_iff_continuousAt.2 fun z => (XiC_analytic z (mem_univ z)).continuousAt
  have hm : Measurable (fun x : ℝ => (x : ℂ) - I) := by fun_prop
  unfold logDeriv
  exact ((measurable_deriv XiC).comp hm).div (hXi.measurable.comp hm)

/-- The bottom source is holomorphic on the open right half-plane. -/
theorem hasDerivAt_xiGaussianBottomSourceC {τ₀ : ℂ} (h : 0 < τ₀.re) :
    HasDerivAt xiGaussianBottomSourceC
      (∫ x : ℝ, -((x : ℂ) - I) ^ (2 : ℕ) * Complex.exp (-τ₀ * ((x : ℂ) - I) ^ (2 : ℕ)) *
        logDeriv XiC ((x : ℂ) - I)) τ₀ := by
  set σ₁ : ℝ := τ₀.re / 2
  set σ₂ : ℝ := 3 * τ₀.re / 2
  set R : ℝ := |τ₀.im| + τ₀.re / 2
  have hσ₁ : 0 < σ₁ := by positivity
  set M : ℝ := Real.exp (σ₂ + 2 * R ^ 2 / σ₁)
  set s : Set ℂ := Metric.ball τ₀ (τ₀.re / 2)
  have hs : s ∈ 𝓝 τ₀ := Metric.ball_mem_nhds _ (by positivity)
  have hball : ∀ τ ∈ s, σ₁ ≤ τ.re ∧ τ.re ≤ σ₂ ∧ |τ.im| ≤ R := by
    intro τ hτ
    have hd : ‖τ - τ₀‖ < τ₀.re / 2 := by simpa [s, dist_eq_norm] using hτ
    have hre := abs_re_le_norm (τ - τ₀)
    have him := abs_im_le_norm (τ - τ₀)
    rw [sub_re] at hre
    rw [sub_im] at him
    refine ⟨?_, ?_, ?_⟩
    · have := (abs_le.1 (hre.trans hd.le)).1; simp only [σ₁]; linarith
    · have := (abs_le.1 (hre.trans hd.le)).2; simp only [σ₂]; linarith
    · have h' := abs_sub_abs_le_abs_sub τ.im τ₀.im
      simp only [R]; linarith
  have hL := measurable_logDeriv_XiC_bottom
  have hmeasF : ∀ τ : ℂ, AEStronglyMeasurable
      (fun x : ℝ => Complex.exp (-τ * ((x : ℂ) - I) ^ (2 : ℕ)) * logDeriv XiC ((x : ℂ) - I)) := by
    intro τ
    exact ((by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-τ * ((x : ℂ) - I) ^ (2 : ℕ))).measurable.mul hL).aestronglyMeasurable
  have hint0 : Integrable (fun x : ℝ =>
      Complex.exp (-((σ₁ / 2 : ℝ) : ℂ) * ((x : ℂ) - I) ^ (2 : ℕ)) * logDeriv XiC ((x : ℂ) - I)) := by
    have := integrable_xiGaussianBottomXiLogIntegrand (t := σ₁ / 2) (c := 1) (by positivity)
      (by norm_num) 0
    refine this.congr (Eventually.of_forall fun x => ?_)
    exact xiGaussianBottomXiLogIntegrand_zero _ x
  have hint1 : Integrable (fun x : ℝ =>
      ((x : ℂ) - I) ^ (2 : ℕ) * Complex.exp (-((σ₁ / 2 : ℝ) : ℂ) * ((x : ℂ) - I) ^ (2 : ℕ)) *
        logDeriv XiC ((x : ℂ) - I)) := by
    have := integrable_xiGaussianBottomXiLogIntegrand (t := σ₁ / 2) (c := 1) (by positivity)
      (by norm_num) 1
    refine this.congr (Eventually.of_forall fun x => ?_)
    exact xiGaussianBottomXiLogIntegrand_one _ x
  have hintτ₀ : Integrable (fun x : ℝ =>
      Complex.exp (-τ₀ * ((x : ℂ) - I) ^ (2 : ℕ)) * logDeriv XiC ((x : ℂ) - I)) := by
    obtain ⟨h1, h2, h3⟩ := hball τ₀ (Metric.mem_ball_self (by positivity))
    refine (hint0.norm.const_mul M).mono' (hmeasF τ₀) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_exp_neg_mul_sub_I_sq_le hσ₁ h1 h2 h3 x) (norm_nonneg _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (α := ℝ) (μ := volume)
    (F := fun τ (x : ℝ) => Complex.exp (-τ * ((x : ℂ) - I) ^ (2 : ℕ)) * logDeriv XiC ((x : ℂ) - I))
    (F' := fun τ (x : ℝ) => -((x : ℂ) - I) ^ (2 : ℕ) * Complex.exp (-τ * ((x : ℂ) - I) ^ (2 : ℕ)) *
      logDeriv XiC ((x : ℂ) - I))
    (bound := fun x : ℝ => M * ‖((x : ℂ) - I) ^ (2 : ℕ) *
      Complex.exp (-((σ₁ / 2 : ℝ) : ℂ) * ((x : ℂ) - I) ^ (2 : ℕ)) * logDeriv XiC ((x : ℂ) - I)‖)
    hs (Eventually.of_forall hmeasF) hintτ₀
    (((by fun_prop : Continuous fun x : ℝ => -((x : ℂ) - I) ^ (2 : ℕ) *
      Complex.exp (-τ₀ * ((x : ℂ) - I) ^ (2 : ℕ))).measurable.mul hL).aestronglyMeasurable)
    (Eventually.of_forall fun x τ hτ => by
      obtain ⟨h1, h2, h3⟩ := hball τ hτ
      have hb := norm_exp_neg_mul_sub_I_sq_le hσ₁ h1 h2 h3 x
      rw [norm_mul, norm_mul, norm_neg]
      calc ‖((x : ℂ) - I) ^ (2 : ℕ)‖ * ‖Complex.exp (-τ * ((x : ℂ) - I) ^ (2 : ℕ))‖ *
            ‖logDeriv XiC ((x : ℂ) - I)‖
          ≤ ‖((x : ℂ) - I) ^ (2 : ℕ)‖ * (M *
              ‖Complex.exp (-((σ₁ / 2 : ℝ) : ℂ) * ((x : ℂ) - I) ^ (2 : ℕ))‖) *
            ‖logDeriv XiC ((x : ℂ) - I)‖ := by gcongr
        _ = M * ‖((x : ℂ) - I) ^ (2 : ℕ) *
              Complex.exp (-((σ₁ / 2 : ℝ) : ℂ) * ((x : ℂ) - I) ^ (2 : ℕ)) *
            logDeriv XiC ((x : ℂ) - I)‖ := by rw [norm_mul, norm_mul]; ring)
    (hint1.norm.const_mul M)
    (Eventually.of_forall fun x τ _ => by
      have h := (((hasDerivAt_id' τ).neg.mul_const (((x : ℂ) - I) ^ (2 : ℕ))).cexp).mul_const
        (logDeriv XiC ((x : ℂ) - I))
      exact h.congr_deriv (by simp only [Pi.neg_apply]; ring))
  exact key.2

theorem differentiableAt_xiGaussianBottomSourceC {τ₀ : ℂ} (h : 0 < τ₀.re) :
    DifferentiableAt ℂ xiGaussianBottomSourceC τ₀ :=
  (hasDerivAt_xiGaussianBottomSourceC h).differentiableAt

/-- At real time the heat trace is the explicit bottom source. -/
theorem xiGaussianHeatTraceC_ofReal_eq_bottomSource {t : ℝ} (ht : 0 < t) :
    xiGaussianHeatTraceC (t : ℂ) =
      (Real.pi : ℂ)⁻¹ * (-I * xiGaussianBottomSourceC (t : ℂ)) := by
  have h := xiGaussianHeatMoment_eq_completedBottomSource_div_pi ht 0
  rw [integral_xiGaussianCompletedBottomSource_eq_neg_I_mul_XiLog ht (by norm_num)] at h
  have hmom : xiGaussianHeatMoment 0 t = xiGaussianHeatTraceC (t : ℂ) := by
    simp only [xiGaussianHeatMoment, pow_zero, one_mul, xiGaussianHeatTraceC,
      xiGaussianHeatTermC, xiGaussianHeatTerm]
  have hJ : (∫ x : ℝ, xiGaussianBottomXiLogIntegrand t 0 1 x) = xiGaussianBottomSourceC (t : ℂ) := by
    rw [xiGaussianBottomSourceC]
    exact integral_congr_ae (Eventually.of_forall fun x => xiGaussianBottomXiLogIntegrand_zero t x)
  rw [← hmom, h, hJ]

/-- **Analytic continuation of the bottom-source explicit formula.**  On the whole right half-plane
`ν(τ) = -(i/π) J(τ)`. -/
theorem xiGaussianHeatTraceC_eq_bottomSource {τ : ℂ} (hτ : 0 < τ.re) :
    xiGaussianHeatTraceC τ = (Real.pi : ℂ)⁻¹ * (-I * xiGaussianBottomSourceC τ) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  set f : ℂ → ℂ := fun z => xiGaussianHeatTraceC z - (Real.pi : ℂ)⁻¹ * (-I * xiGaussianBottomSourceC z)
  have hf : DifferentiableOn ℂ f U := fun z hz =>
    ((differentiableAt_xiGaussianHeatTraceC hz).sub
      (((differentiableAt_xiGaussianBottomSourceC hz).const_mul (-I)).const_mul _)).differentiableWithinAt
  have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 := (h0.const_add (1 : ℝ))
      rw [add_zero] at h1
      have h2 := (Complex.continuous_ofReal.tendsto 1).comp h1
      rw [Complex.ofReal_one] at h2
      exact h2
    · refine Eventually.of_forall fun n => ?_
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have h' := congrArg Complex.re h
      simp only [ofReal_re, one_re] at h'
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), f z = 0 := by
    refine hseq.frequently (Eventually.frequently (Eventually.of_forall fun n => ?_))
    have hpos : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by positivity
    simp only [f]
    rw [xiGaussianHeatTraceC_ofReal_eq_bottomSource hpos, sub_self]
  have hzero := (hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt 0).isPreconnected (by simp [U]) hfreq hτ
  have h0 : f τ = 0 := hzero
  exact sub_eq_zero.1 h0

/-- **Arithmetic single vertical-line receiver.**  For every `a > 0`, RH holds iff the complex-time
Gaussian transform of the prime–Gamma source on `Re s = 3/2`,
`b ↦ ∫ exp(-(a + ib)(x - i)²) logDeriv XiC (x - i) dx`, is bounded. -/
theorem riemannHypothesis_iff_xiGaussianBottomSourceC_bounded_on_vertical_line {a : ℝ}
    (ha : 0 < a) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ b : ℝ, ‖xiGaussianBottomSourceC ((a : ℂ) + b * I)‖ ≤ C := by
  have hnorm : ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ =
      ‖xiGaussianBottomSourceC ((a : ℂ) + b * I)‖ / Real.pi := fun b => by
    rw [xiGaussianHeatTraceC_eq_bottomSource (by simpa using ha), norm_mul, norm_mul, norm_inv,
      norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    ring
  rw [riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line ha]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨Real.pi * C, fun b => ?_⟩
    have := hC b
    rw [hnorm, div_le_iff₀ Real.pi_pos] at this
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C / Real.pi, fun b => ?_⟩
    rw [hnorm]
    exact div_le_div_of_nonneg_right (hC b) Real.pi_pos.le

end

end RHTower
