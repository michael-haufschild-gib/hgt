import GaloisForLFunctions.RHTower.XiGaussianHeatBottomSourceReceiver

/-!
# One explicit prime sum on one vertical line decides RH

For complex time `τ` with `Re τ > 0` let

`S(τ) = Σ_n Λ(n) n^{-1/2} exp(-(log n)²/(4τ))`   (`gaussianPrimeChirpSum`).

This is the von Mangoldt function weighted by a complex Gaussian in `log n`.  At `τ = a + ib` the
weight has modulus `exp(-(log n)² a / (4|τ|²))` and phase `(log n)² b / (4|τ|²)`.

**Theorem** (`riemannHypothesis_iff_gaussianPrimeChirp_bounded_on_vertical_line`).  For every `a > 0`,
RH holds iff `b ↦ (π/τ)^{1/2} S(τ)` is bounded on `τ = a + ib`.  Equivalently, `S(a+ib) = O(|a+ib|^{1/2})`
(`riemannHypothesis_iff_gaussianPrimeChirpSum_le_sqrt_norm`).

No zero, height or Gamma factor appears in the statement.  The Gamma factor and the pole of `ζ` stay
bounded on vertical lines and drop out.

Mechanism.  At real time the corpus formula for the Gaussian Xi heat trace is

`π ν(t) = ∫ e^{-t x²} (log Γ_arch)'(1/2 + ix) dx + 2π e^{t/4} - Σ_n Λ(n) n^{-1/2} ĝ_t(log n)`,

with `ĝ_t(w) = (π/t)^{1/2} e^{-w²/(4t)}` (`integral_xiGaussianCompletedBottomSource_eq`).  Every term
is holomorphic in `t` on `Re t > 0`, so the identity continues to complex time
(`pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime`).  On `Re τ = a` the archimedean integral
is at most its value at `a`, and the pole term has modulus `2π e^{a/4}`.  So the heat trace is
bounded on the line iff the prime term is, and `riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line`
concludes.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

open RiemannGaussian

noncomputable section

/-- The von Mangoldt atom at `s = 1/2`. -/
abbrev vonMangoldtHalfTerm (n : ℕ) : ℂ :=
  LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2) n

/-- The Gaussian–von Mangoldt chirp sum `Σ Λ(n) n^{-1/2} exp(-(log n)²/(4τ))`. -/
def gaussianPrimeChirpSum (τ : ℂ) : ℂ :=
  ∑' n : ℕ, vonMangoldtHalfTerm n * Complex.exp (-((Real.log n : ℝ) : ℂ) ^ 2 / (4 * τ))

/-- The archimedean Gaussian integral on the critical line at complex time. -/
def gaussianArchCriticalC (τ : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-τ * (x : ℂ) ^ (2 : ℕ)) *
    logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))

/-- The prime term `(π/τ)^{1/2} S(τ)`. -/
def gaussianPrimeChirpC (τ : ℂ) : ℂ :=
  ((Real.pi : ℂ) / τ) ^ (1 / 2 : ℂ) * gaussianPrimeChirpSum τ

/-! ## The Gaussian Fourier transform in closed form -/

theorem xiGaussianHermiteFourier_zero {t : ℝ} (ht : 0 < t) (w : ℝ) :
    xiGaussianHermiteFourier t 0 w =
      ((Real.pi : ℂ) / t) ^ (1 / 2 : ℂ) * Complex.exp (-((w : ℂ) ^ 2) / (4 * t)) := by
  have hb : (-(t : ℂ)).re < 0 := by simp [ht]
  have h := integral_cexp_quadratic hb (-(I * w)) 0
  rw [xiGaussianHermiteFourier]
  have hcongr : (fun x : ℝ => xiGaussianTestC t 0 (x : ℂ) * Complex.exp (-(I * (w : ℂ) * (x : ℂ)))) =
      fun x : ℝ => Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2 + -(I * w) * x + 0) := by
    funext x
    rw [xiGaussianTestC, pow_zero, one_mul, ← Complex.exp_add]
    congr 1
    ring
  rw [hcongr, h, neg_neg]
  congr 2
  have hI : (I * (w : ℂ)) ^ 2 = -((w : ℂ) ^ 2) := by rw [mul_pow, I_sq]; ring
  rw [neg_sq, hI]
  ring

theorem tsum_xiGaussianCenteredPrimeAtom_zero {t : ℝ} (ht : 0 < t) :
    ∑' n : ℕ, xiGaussianCenteredPrimeAtom t 0 n = gaussianPrimeChirpC (t : ℂ) := by
  rw [gaussianPrimeChirpC, gaussianPrimeChirpSum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [xiGaussianCenteredPrimeAtom, xiGaussianHermiteFourier_zero ht]
  ring

/-! ## Holomorphy of the three terms -/

theorem norm_cexp_neg_log_sq_div (τ : ℂ) (L : ℝ) :
    ‖Complex.exp (-((L : ℂ) ^ 2) / (4 * τ))‖ = Real.exp (-(L ^ 2) * τ.re / (4 * Complex.normSq τ)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : -((L : ℂ) ^ 2) / (4 * τ) = ((-(L ^ 2) / 4 : ℝ) : ℂ) * τ⁻¹ := by
    push_cast
    field_simp
  rw [h, Complex.re_ofReal_mul, Complex.inv_re]
  field_simp

theorem norm_vonMangoldtHalfTerm_mul_cexp_le {τ : ℂ} {c : ℝ} (hc : 0 < c)
    (hτ : c ≤ τ.re / (4 * Complex.normSq τ)) (n : ℕ) :
    ‖vonMangoldtHalfTerm n * Complex.exp (-((Real.log n : ℝ) : ℂ) ^ 2 / (4 * τ))‖ ≤
      gaussianPrimeSummand (1 / (4 * c)) 0 n := by
  rw [norm_mul, norm_cexp_neg_log_sq_div, gaussianPrimeSummand, zero_mul, Real.cos_zero, mul_one,
    vonMangoldtHalfTerm, LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [if_neg hn]
  have hΛ : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hsqrt : (n : ℝ) ^ ((1 / 2 : ℂ).re) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [hΛ, hsqrt]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hL : 0 ≤ Real.log n ^ 2 := sq_nonneg _
  have hdiv : -(Real.log n) ^ (2 : ℕ) / (4 * (1 / (4 * c))) = -(Real.log n ^ 2) * c := by
    field_simp
  rw [hdiv]
  have : -(Real.log n ^ 2) * τ.re / (4 * Complex.normSq τ) =
      -(Real.log n ^ 2) * (τ.re / (4 * Complex.normSq τ)) := by ring
  rw [this]
  nlinarith

/-- The chirp sum is holomorphic on the open right half-plane. -/
theorem differentiableAt_gaussianPrimeChirpSum {τ₀ : ℂ} (h : 0 < τ₀.re) :
    DifferentiableAt ℂ gaussianPrimeChirpSum τ₀ := by
  set r : ℝ := τ₀.re / 2
  set c : ℝ := r / (4 * (‖τ₀‖ + r) ^ 2)
  have hr : 0 < r := by positivity
  have hnorm0 : 0 < ‖τ₀‖ := norm_pos_iff.2 (fun h0 => by rw [h0] at h; simp at h)
  have hc : 0 < c := by positivity
  set U : Set ℂ := Metric.ball τ₀ r
  have hU : IsOpen U := Metric.isOpen_ball
  have hbound : ∀ (n : ℕ) (τ : ℂ), τ ∈ U →
      ‖vonMangoldtHalfTerm n * Complex.exp (-((Real.log n : ℝ) : ℂ) ^ 2 / (4 * τ))‖ ≤
        gaussianPrimeSummand (1 / (4 * c)) 0 n := by
    intro n τ hτ
    apply norm_vonMangoldtHalfTerm_mul_cexp_le hc
    have hd : ‖τ - τ₀‖ < r := by simpa [U, dist_eq_norm] using hτ
    have hre : r ≤ τ.re := by
      have := abs_re_le_norm (τ - τ₀)
      rw [sub_re] at this
      have := (abs_le.1 (this.trans hd.le)).1
      simp only [r] at this ⊢
      linarith
    have hn : ‖τ‖ ≤ ‖τ₀‖ + r := by
      have := norm_le_norm_add_norm_sub' τ τ₀
      linarith [norm_sub_rev τ τ₀]
    have hns : Complex.normSq τ ≤ (‖τ₀‖ + r) ^ 2 := by
      rw [← Complex.sq_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hτpos : 0 < τ.re := hr.trans_le hre
    have hns0 : 0 < Complex.normSq τ := Complex.normSq_pos.2 (fun h0 => by rw [h0] at hτpos; simp at hτpos)
    calc c = r / (4 * (‖τ₀‖ + r) ^ 2) := rfl
      _ ≤ τ.re / (4 * (‖τ₀‖ + r) ^ 2) := by gcongr
      _ ≤ τ.re / (4 * Complex.normSq τ) := by gcongr
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ
      (fun τ => vonMangoldtHalfTerm n * Complex.exp (-((Real.log n : ℝ) : ℂ) ^ 2 / (4 * τ))) U := by
    intro n τ hτ
    have hτ0 : τ ≠ 0 := by
      have hd : ‖τ - τ₀‖ < r := by simpa [U, dist_eq_norm] using hτ
      intro h0
      rw [h0, zero_sub, norm_neg] at hd
      have := Complex.abs_re_le_norm τ₀
      rw [abs_of_pos h] at this
      simp only [r] at hd
      linarith
    exact (((differentiableAt_const _).div ((differentiableAt_const _).mul differentiableAt_id)
      (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hτ0)).cexp.const_mul _).differentiableWithinAt
  have hD := Complex.differentiableOn_tsum_of_summable_norm
    (summable_gaussianPrimeSummand (by positivity) 0) hdiff hU hbound
  exact hD.differentiableAt (hU.mem_nhds (Metric.mem_ball_self hr))

theorem differentiableAt_gaussianPrimeChirpC {τ₀ : ℂ} (h : 0 < τ₀.re) :
    DifferentiableAt ℂ gaussianPrimeChirpC τ₀ := by
  have hτ0 : τ₀ ≠ 0 := fun h0 => by rw [h0] at h; simp at h
  have hslit : (Real.pi : ℂ) / τ₀ ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    rw [div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re]
    have : 0 < Complex.normSq τ₀ := Complex.normSq_pos.2 hτ0
    positivity
  exact (((differentiableAt_const _).div differentiableAt_id hτ0).cpow
    (differentiableAt_const _) hslit).mul (differentiableAt_gaussianPrimeChirpSum h)

theorem xiGaussianCenteredArchIntegrand_eq (t : ℝ) (k : ℕ) (x : ℝ) :
    xiGaussianCenteredArchIntegrand t k x =
      (x : ℂ) ^ (2 * k) * Complex.exp (-(t : ℂ) * (x : ℂ) ^ (2 : ℕ)) *
        logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ)) := by
  simp [xiGaussianCenteredArchIntegrand, xiGaussianArchHorizontalIntegrand, xiGaussianTestC]

theorem integrable_xiGaussianCenteredArchIntegrand {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (xiGaussianCenteredArchIntegrand t k) :=
  integrable_xiGaussianArchHorizontalIntegrand (c := 1) ht (by norm_num) k
    (y := 0) ⟨by norm_num, le_rfl⟩ (by norm_num)

theorem continuous_logDeriv_archFactor_critical :
    Continuous (fun x : ℝ => logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))) := by
  have h := continuous_xiGaussianArchLogDeriv_horizontal (y := 0) (by norm_num) (by norm_num)
  simpa using h

/-- The archimedean critical-line integral is holomorphic on the open right half-plane. -/
theorem differentiableAt_gaussianArchCriticalC {τ₀ : ℂ} (h : 0 < τ₀.re) :
    DifferentiableAt ℂ gaussianArchCriticalC τ₀ := by
  set r : ℝ := τ₀.re / 2
  have hr : 0 < r := by positivity
  set s : Set ℂ := Metric.ball τ₀ r
  have hs : s ∈ 𝓝 τ₀ := Metric.ball_mem_nhds _ hr
  have hball : ∀ τ ∈ s, r ≤ τ.re := by
    intro τ hτ
    have hd : ‖τ - τ₀‖ < r := by simpa [s, dist_eq_norm] using hτ
    have := abs_re_le_norm (τ - τ₀)
    rw [sub_re] at this
    have := (abs_le.1 (this.trans hd.le)).1
    simp only [r] at this ⊢
    linarith
  have hL := continuous_logDeriv_archFactor_critical
  have hnormexp : ∀ (τ : ℂ) (x : ℝ), ‖Complex.exp (-τ * (x : ℂ) ^ (2 : ℕ))‖ =
      Real.exp (-(τ.re * x ^ 2)) := by
    intro τ x
    rw [Complex.norm_exp]
    congr 1
    have : (x : ℂ) ^ (2 : ℕ) = ((x ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, neg_mul, neg_re, Complex.mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have hmono : ∀ τ ∈ s, ∀ x : ℝ, ‖Complex.exp (-τ * (x : ℂ) ^ (2 : ℕ))‖ ≤
      ‖Complex.exp (-((r : ℝ) : ℂ) * (x : ℂ) ^ (2 : ℕ))‖ := by
    intro τ hτ x
    rw [hnormexp, hnormexp, ofReal_re]
    apply Real.exp_le_exp.2
    nlinarith [hball τ hτ, sq_nonneg x]
  have hint0 : Integrable (fun x : ℝ => Complex.exp (-((r : ℝ) : ℂ) * (x : ℂ) ^ (2 : ℕ)) *
      logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))) := by
    refine (integrable_xiGaussianCenteredArchIntegrand hr 0).congr
      (Eventually.of_forall fun x => ?_)
    rw [xiGaussianCenteredArchIntegrand_eq]
    simp
  have hint1 : Integrable (fun x : ℝ => (x : ℂ) ^ (2 : ℕ) *
      Complex.exp (-((r : ℝ) : ℂ) * (x : ℂ) ^ (2 : ℕ)) *
        logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))) := by
    refine (integrable_xiGaussianCenteredArchIntegrand hr 1).congr
      (Eventually.of_forall fun x => ?_)
    rw [xiGaussianCenteredArchIntegrand_eq]
  have hmeas : ∀ τ : ℂ, AEStronglyMeasurable (fun x : ℝ =>
      Complex.exp (-τ * (x : ℂ) ^ (2 : ℕ)) * logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))) :=
    fun τ => ((by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-τ * (x : ℂ) ^ (2 : ℕ))).mul hL).aestronglyMeasurable
  have hintτ₀ : Integrable (fun x : ℝ => Complex.exp (-τ₀ * (x : ℂ) ^ (2 : ℕ)) *
      logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))) := by
    refine hint0.norm.mono' (hmeas τ₀) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hmono τ₀ (Metric.mem_ball_self hr) x) (norm_nonneg _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (α := ℝ) (μ := volume)
    (F := fun τ (x : ℝ) => Complex.exp (-τ * (x : ℂ) ^ (2 : ℕ)) *
      logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ)))
    (F' := fun τ (x : ℝ) => -(x : ℂ) ^ (2 : ℕ) * Complex.exp (-τ * (x : ℂ) ^ (2 : ℕ)) *
      logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ)))
    (bound := fun x : ℝ => ‖(x : ℂ) ^ (2 : ℕ) * Complex.exp (-((r : ℝ) : ℂ) * (x : ℂ) ^ (2 : ℕ)) *
      logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))‖)
    hs (Eventually.of_forall hmeas) hintτ₀
    (((by fun_prop : Continuous fun x : ℝ => -(x : ℂ) ^ (2 : ℕ) *
      Complex.exp (-τ₀ * (x : ℂ) ^ (2 : ℕ))).mul hL).aestronglyMeasurable)
    (Eventually.of_forall fun x τ hτ => by
      rw [norm_mul, norm_mul, norm_neg, norm_mul, norm_mul]
      gcongr
      exact hmono τ hτ x)
    hint1.norm
    (Eventually.of_forall fun x τ _ => by
      have h := (((hasDerivAt_id' τ).neg.mul_const ((x : ℂ) ^ (2 : ℕ))).cexp).mul_const
        (logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ)))
      exact h.congr_deriv (by simp only [Pi.neg_apply]; ring))
  exact key.2.differentiableAt

/-! ## Continuation of the three-term formula -/

/-- The pole term `2π exp(-τ (−i/2)²) = 2π exp(τ/4)`. -/
def gaussianArchPoleC (τ : ℂ) : ℂ := 2 * Real.pi * Complex.exp (-τ * xiMassArchPole ^ (2 : ℕ))

theorem pi_mul_xiGaussianHeatTraceC_ofReal {t : ℝ} (ht : 0 < t) :
    (Real.pi : ℂ) * xiGaussianHeatTraceC (t : ℂ) =
      gaussianArchCriticalC t + gaussianArchPoleC t - gaussianPrimeChirpC t := by
  have h := xiGaussianHeatMoment_eq_completedBottomSource_div_pi ht 0
  rw [integral_xiGaussianCompletedBottomSource_eq ht (by norm_num : (1 / 2 : ℝ) < 1) 0,
    tsum_xiGaussianCenteredPrimeAtom_zero ht] at h
  have hmom : xiGaussianHeatMoment 0 t = xiGaussianHeatTraceC (t : ℂ) := by
    simp only [xiGaussianHeatMoment, pow_zero, one_mul, xiGaussianHeatTraceC,
      xiGaussianHeatTermC, xiGaussianHeatTerm]
  have harch : (∫ x : ℝ, xiGaussianCenteredArchIntegrand t 0 x) = gaussianArchCriticalC t := by
    rw [gaussianArchCriticalC]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [xiGaussianCenteredArchIntegrand_eq]
    simp
  have hpole : 2 * (Real.pi : ℂ) * xiGaussianTestC t 0 xiMassArchPole = gaussianArchPoleC t := by
    rw [gaussianArchPoleC, xiGaussianTestC, pow_zero, one_mul]
  rw [← hmom, h, harch, hpole]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **Three-term formula at complex time.** -/
theorem pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime {τ : ℂ} (hτ : 0 < τ.re) :
    (Real.pi : ℂ) * xiGaussianHeatTraceC τ =
      gaussianArchCriticalC τ + gaussianArchPoleC τ - gaussianPrimeChirpC τ := by
  set U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  set f : ℂ → ℂ := fun z => (Real.pi : ℂ) * xiGaussianHeatTraceC z -
    (gaussianArchCriticalC z + gaussianArchPoleC z - gaussianPrimeChirpC z)
  have hf : DifferentiableOn ℂ f U := fun z hz =>
    (((differentiableAt_xiGaussianHeatTraceC hz).const_mul _).sub
      (((differentiableAt_gaussianArchCriticalC hz).add
        ((by unfold gaussianArchPoleC; fun_prop : Differentiable ℂ gaussianArchPoleC) z)).sub
          (differentiableAt_gaussianPrimeChirpC hz))).differentiableWithinAt
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
    rw [pi_mul_xiGaussianHeatTraceC_ofReal hpos, sub_self]
  have hzero := (hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt 0).isPreconnected (by simp [U]) hfreq hτ
  have h0 : f τ = 0 := hzero
  exact sub_eq_zero.1 h0

/-! ## The receiver -/

theorem norm_gaussianArchCriticalC_le (a b : ℝ) :
    ‖gaussianArchCriticalC ((a : ℂ) + b * I)‖ ≤ ∫ x : ℝ, ‖xiGaussianCenteredArchIntegrand a 0 x‖ := by
  rw [gaussianArchCriticalC]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Eventually.of_forall fun x => ?_)))
  simp only
  rw [xiGaussianCenteredArchIntegrand_eq, norm_mul, norm_mul, norm_mul, Complex.norm_exp,
    Complex.norm_exp]
  have h1 : (-((a : ℂ) + b * I) * (x : ℂ) ^ (2 : ℕ)).re = (-(a : ℂ) * (x : ℂ) ^ (2 : ℕ)).re := by
    have hx2im : ((x : ℂ) ^ (2 : ℕ)).im = 0 := by rw [← ofReal_pow]; exact ofReal_im _
    rw [neg_mul, neg_mul, neg_re, neg_re, mul_re, mul_re, hx2im]
    simp
  rw [h1]
  simp

theorem norm_gaussianArchPoleC (a b : ℝ) :
    ‖gaussianArchPoleC ((a : ℂ) + b * I)‖ = 2 * Real.pi * Real.exp (a / 4) := by
  rw [gaussianArchPoleC, norm_mul, norm_mul, Complex.norm_exp]
  have hp : xiMassArchPole ^ (2 : ℕ) = -(1 / 4 : ℂ) := by
    rw [xiMassArchPole, div_pow, neg_pow, I_sq]; norm_num
  rw [hp]
  have : (-((a : ℂ) + b * I) * -(1 / 4 : ℂ)).re = a / 4 := by simp; ring
  rw [this]
  simp [Real.pi_pos.le]

/-- **Prime chirp receiver.**  For every `a > 0`, RH holds iff
`b ↦ (π/(a+ib))^{1/2} Σ_n Λ(n) n^{-1/2} exp(-(log n)²/(4(a+ib)))` is bounded. -/
theorem riemannHypothesis_iff_gaussianPrimeChirp_bounded_on_vertical_line {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ b : ℝ, ‖gaussianPrimeChirpC ((a : ℂ) + b * I)‖ ≤ C := by
  set A : ℝ := ∫ x : ℝ, ‖xiGaussianCenteredArchIntegrand a 0 x‖
  set P : ℝ := 2 * Real.pi * Real.exp (a / 4)
  have hre : ∀ b : ℝ, 0 < ((a : ℂ) + b * I).re := fun b => by simpa using ha
  have hid := fun b : ℝ => pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime (hre b)
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line ha]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨A + P + Real.pi * C, fun b => ?_⟩
    have hprime : gaussianPrimeChirpC ((a : ℂ) + b * I) =
        gaussianArchCriticalC ((a : ℂ) + b * I) + gaussianArchPoleC ((a : ℂ) + b * I) -
          (Real.pi : ℂ) * xiGaussianHeatTraceC ((a : ℂ) + b * I) := by
      rw [hid b]; ring
    rw [hprime]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_gaussianArchCriticalC_le a b)
      (norm_gaussianArchPoleC a b).le)) ?_
    rw [norm_mul, hpi]
    exact mul_le_mul_of_nonneg_left (hC b) Real.pi_pos.le
  · rintro ⟨C, hC⟩
    refine ⟨(A + P + C) / Real.pi, fun b => ?_⟩
    rw [le_div_iff₀ Real.pi_pos, mul_comm, ← hpi, ← norm_mul, hid b]
    refine (norm_sub_le _ _).trans ?_
    exact add_le_add ((norm_add_le _ _).trans (add_le_add (norm_gaussianArchCriticalC_le a b)
      (norm_gaussianArchPoleC a b).le)) (hC b)

/-- **Square-root form.**  For every `a > 0`, RH holds iff the chirp sum grows at most like
`|a + ib|^{1/2}` along the vertical line. -/
theorem riemannHypothesis_iff_gaussianPrimeChirpSum_le_sqrt_norm {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ b : ℝ,
      ‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ ≤ C * Real.sqrt ‖(a : ℂ) + b * I‖ := by
  have hfac : ∀ b : ℝ, ‖((Real.pi : ℂ) / ((a : ℂ) + b * I)) ^ (1 / 2 : ℂ)‖ =
      Real.sqrt Real.pi / Real.sqrt ‖(a : ℂ) + b * I‖ := by
    intro b
    have hτ0 : (a : ℂ) + b * I ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    have hne : (Real.pi : ℂ) / ((a : ℂ) + b * I) ≠ 0 :=
      div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hτ0
    rw [Complex.norm_cpow_of_ne_zero hne]
    have him : (1 / 2 : ℂ).im = 0 := by norm_num
    have hre : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [him, hre, mul_zero, Real.exp_zero, div_one, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Real.div_rpow Real.pi_pos.le (norm_nonneg _), ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow]
  have hsq : ∀ b : ℝ, 0 < Real.sqrt ‖(a : ℂ) + b * I‖ := fun b => by
    apply Real.sqrt_pos.2
    apply norm_pos_iff.2
    intro h0
    have := congrArg Complex.re h0; simp at this; linarith
  have hnorm : ∀ b : ℝ, ‖gaussianPrimeChirpC ((a : ℂ) + b * I)‖ =
      Real.sqrt Real.pi * (‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ /
        Real.sqrt ‖(a : ℂ) + b * I‖) := fun b => by
    rw [gaussianPrimeChirpC, norm_mul, hfac b]
    ring
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [riemannHypothesis_iff_gaussianPrimeChirp_bounded_on_vertical_line ha]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C / Real.sqrt Real.pi, fun b => ?_⟩
    have h := hC b
    rw [hnorm b] at h
    have h2 : ‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ / Real.sqrt ‖(a : ℂ) + b * I‖ ≤
        C / Real.sqrt Real.pi := by
      rw [le_div_iff₀ hspi]; linarith
    rwa [div_le_iff₀ (hsq b)] at h2
  · rintro ⟨C, hC⟩
    refine ⟨Real.sqrt Real.pi * C, fun b => ?_⟩
    rw [hnorm b]
    refine mul_le_mul_of_nonneg_left ?_ hspi.le
    rw [div_le_iff₀ (hsq b)]
    exact hC b

/-- **Prime-side contraction.**  For every `a > 0`, RH holds iff on the line `Re τ = a` the explicit
prime–Gamma combination `Arch(τ) + 2πe^{τ/4} - (π/τ)^{1/2} S(τ)` never exceeds its real-time value
`π ν(a)` in modulus. -/
theorem riemannHypothesis_iff_forall_norm_arch_add_pole_sub_primeChirp_le {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ b : ℝ,
      ‖gaussianArchCriticalC ((a : ℂ) + b * I) + gaussianArchPoleC ((a : ℂ) + b * I) -
          gaussianPrimeChirpC ((a : ℂ) + b * I)‖ ≤ Real.pi * xiGaussianHeatTraceReal a := by
  have hre : ∀ b : ℝ, 0 < ((a : ℂ) + b * I).re := fun b => by simpa using ha
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hid : ∀ b : ℝ, ‖gaussianArchCriticalC ((a : ℂ) + b * I) +
      gaussianArchPoleC ((a : ℂ) + b * I) - gaussianPrimeChirpC ((a : ℂ) + b * I)‖ =
        Real.pi * ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ := fun b => by
    rw [← pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime (hre b), norm_mul, hpi]
  rw [riemannHypothesis_iff_forall_norm_xiGaussianHeatTraceC_le_real ha]
  refine forall_congr' fun b => ?_
  rw [hid b]
  exact ⟨fun h => mul_le_mul_of_nonneg_left h Real.pi_pos.le,
    fun h => le_of_mul_le_mul_left h Real.pi_pos⟩

end

end RHTower
