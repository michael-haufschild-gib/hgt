import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalOmegaLaw
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalVarianceLaw
import GaloisForLFunctions.RHTower.ZetaLineFirstMoment

/-!
# The vertical Bohr spectrum of the prime chirp is the set of squared ordinates

On the vertical line `Re τ = a` the Gaussian–von Mangoldt prime term
`(π/τ)^{1/2} S(τ)`, with `S(τ) = Σ Λ(n) n^{-1/2} exp(-(log n)²/(4τ))`, satisfies the three-term
formula `π ν(τ) = Arch(τ) + 2π e^{τ/4} - (π/τ)^{1/2} S(τ)`
(`pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime`).  Under RH every `w_q = z_q²` is a
positive real `λ_q`, so `b ↦ ν(a + ib) = Σ_q e^{-aλ_q} e^{-ibλ_q}` is almost periodic.

**Theorem** (`tendsto_bohrCoeff_gaussianPrimeChirpC_of_rh`).  Under RH, for every `a > 0` and every
frequency `λ ≥ 0`,

`(1/B) ∫₀^B (π/τ_b)^{1/2} S(τ_b) e^{iλb} db  →  -π Σ_{q : λ_q = λ} e^{-aλ}`,   `τ_b = a + ib`.

The archimedean part contributes nothing (`tendsto_bohrCoeff_gaussianArchCriticalC`), and the pole
`2π e^{τ/4}` only contributes at the frequency `-1/4`.  So, Fourier-analysed along one vertical line,
the primes return exactly the squared ordinates `γ²` as frequencies, weighted by multiplicity: a
spectral counterpart of the height zero detector `tendsto_gaussianPrimeContribution_of_outside_cones`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The Fejér average of `e^{-iΔb}` over `[0, B]`. -/
def fejerExp (B Δ : ℝ) : ℂ := (1 / (B : ℂ)) * ∫ b in (0 : ℝ)..B, Complex.exp (-(I * Δ) * b)

theorem norm_fejerExp_le {B : ℝ} (hB : 0 < B) (Δ : ℝ) : ‖fejerExp B Δ‖ ≤ 1 := by
  rw [fejerExp, norm_mul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := B) (C := 1)
    (f := fun b : ℝ => Complex.exp (-(I * Δ) * b)) (fun x _ => by
      rw [Complex.norm_exp]
      simp)
  rw [sub_zero, abs_of_pos hB, one_mul] at h
  calc ‖1 / (B : ℂ)‖ * ‖∫ b in (0 : ℝ)..B, Complex.exp (-(I * Δ) * b)‖
      ≤ ‖1 / (B : ℂ)‖ * B := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = 1 := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
      field_simp

theorem continuous_fejerExp (B : ℝ) : Continuous fun Δ : ℝ => fejerExp B Δ := by
  unfold fejerExp
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun Δ b : ℝ => Complex.exp (-(I * Δ) * b)) (by fun_prop) 0 B)

theorem norm_exp_neg_ofReal_mul_sq (a x : ℝ) :
    ‖Complex.exp (-(a : ℂ) * (x : ℂ) ^ (2 : ℕ))‖ = Real.exp (-(a * x ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  rw [show -(a : ℂ) * (x : ℂ) ^ (2 : ℕ) = ((-(a * x ^ 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

theorem tendsto_fejerExp (Δ : ℝ) :
    Tendsto (fun B : ℝ => fejerExp B Δ) atTop (𝓝 (if Δ = 0 then 1 else 0)) := by
  by_cases hΔ : Δ = 0
  · rw [if_pos hΔ]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    rw [fejerExp, hΔ]
    simp only [ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero, real_smul, mul_one]
    have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
    field_simp
  · rw [if_neg hΔ]
    have hc : -(I * (Δ : ℂ)) ≠ 0 := by
      simp [hΔ, I_ne_zero]
    have hlim : Tendsto (fun B : ℝ => (2 / |Δ|) / B) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    rw [fejerExp, integral_exp_mul_complex hc, norm_mul, norm_div, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hB]
    have hnum : ‖Complex.exp (-(I * Δ) * B) - Complex.exp (-(I * Δ) * (0 : ℝ))‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖Complex.exp (-(I * Δ) * B)‖ = 1 := by rw [Complex.norm_exp]; simp
      have h2 : ‖Complex.exp (-(I * Δ) * ((0 : ℝ) : ℂ))‖ = 1 := by simp
      rw [h1, h2]; norm_num
    have hden : ‖-(I * (Δ : ℂ))‖ = |Δ| := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_div, hden]
    have hΔ0 : 0 < |Δ| := abs_pos.2 hΔ
    calc 1 / B * (‖Complex.exp (-(I * Δ) * B) - Complex.exp (-(I * Δ) * ((0 : ℝ) : ℂ))‖ / |Δ|)
        ≤ 1 / B * (2 / |Δ|) := by gcongr
      _ = 2 / |Δ| / B := by ring

/-- **Bohr coefficients of the heat trace under RH.** -/
theorem tendsto_bohrCoeff_xiGaussianHeatTraceC_of_rh (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 < a)
    (ω : ℝ) :
    Tendsto (fun B : ℝ => (1 / (B : ℂ)) *
        ∫ b in (0 : ℝ)..B, xiGaussianHeatTraceC ((a : ℂ) + b * I) * Complex.exp (I * ω * b))
      atTop (𝓝 (∑' q : XiZeroCopy,
        if xiSpectralSqRe q = ω then ((Real.exp (-(a * xiSpectralSqRe q)) : ℝ) : ℂ) else 0)) := by
  classical
  set c : XiZeroCopy → ℝ := fun q => Real.exp (-(a * xiSpectralSqRe q))
  have hc : Summable c := by
    have h := summable_norm_xiGaussianHeatTermC (τ := (a : ℂ)) (by simpa using ha)
    refine h.congr fun q => ?_
    rw [norm_xiGaussianHeatTermC]
    simp [c, xiSpectralSqRe]
  -- the integrand as a series
  have hterm : ∀ (q : XiZeroCopy) (b : ℝ),
      xiGaussianHeatTermC ((a : ℂ) + b * I) q * Complex.exp (I * ω * b) =
        (c q : ℂ) * Complex.exp (-(I * (xiSpectralSqRe q - ω : ℝ)) * b) := by
    intro q b
    rw [xiGaussianHeatTermC, xiSpectralSq_eq_ofReal_xiSpectralSqRe_of_rh hRH, ← Complex.exp_add]
    simp only [c, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hseries : ∀ b : ℝ, xiGaussianHeatTraceC ((a : ℂ) + b * I) * Complex.exp (I * ω * b) =
      ∑' q, (c q : ℂ) * Complex.exp (-(I * (xiSpectralSqRe q - ω : ℝ)) * b) := by
    intro b
    rw [xiGaussianHeatTraceC, ← tsum_mul_right]
    exact tsum_congr fun q => hterm q b
  have hint : ∀ B : ℝ, 0 ≤ B →
      (∫ b in (0 : ℝ)..B, xiGaussianHeatTraceC ((a : ℂ) + b * I) * Complex.exp (I * ω * b)) =
        ∑' q, (c q : ℂ) * ∫ b in (0 : ℝ)..B,
          Complex.exp (-(I * (xiSpectralSqRe q - ω : ℝ)) * b) := by
    intro B hB
    simp_rw [hseries]
    rw [intervalIntegral.integral_of_le hB]
    set G : XiZeroCopy → ℝ → ℂ := fun q b =>
      (c q : ℂ) * Complex.exp (-(I * (xiSpectralSqRe q - ω : ℝ)) * b)
    have hGint : ∀ q, Integrable (G q) (volume.restrict (Ioc 0 B)) := fun q =>
      (by fun_prop : Continuous (G q)).integrableOn_Ioc
    have hGnorm : ∀ q b, ‖G q b‖ = c q := by
      intro q b
      simp only [G, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exp_neg_I_mul_ofReal_mul,
        mul_one]
      exact abs_of_pos (Real.exp_pos _)
    have hGsum : Summable (fun q => ∫ b in Ioc 0 B, ‖G q b‖) := by
      simp_rw [hGnorm]
      simp only [integral_const, smul_eq_mul]
      exact hc.mul_left _
    rw [← integral_tsum_of_summable_integral_norm hGint hGsum]
    refine tsum_congr fun q => ?_
    rw [← intervalIntegral.integral_of_le hB, ← intervalIntegral.integral_const_mul]
  have hrepr : ∀ᶠ B : ℝ in atTop, (1 / (B : ℂ)) *
      (∫ b in (0 : ℝ)..B, xiGaussianHeatTraceC ((a : ℂ) + b * I) * Complex.exp (I * ω * b)) =
        ∑' q, (c q : ℂ) * fejerExp B (xiSpectralSqRe q - ω) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    rw [hint B hB, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [fejerExp]
    ring
  have hlim : Tendsto (fun B : ℝ => ∑' q, (c q : ℂ) * fejerExp B (xiSpectralSqRe q - ω)) atTop
      (𝓝 (∑' q, (c q : ℂ) * (if xiSpectralSqRe q - ω = 0 then 1 else 0))) := by
    refine tendsto_tsum_of_dominated_convergence hc (fun q => ?_) ?_
    · exact (tendsto_fejerExp _).const_mul _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB q
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (norm_fejerExp_le hB _)
  have hval : (∑' q, (c q : ℂ) * (if xiSpectralSqRe q - ω = 0 then 1 else 0)) =
      ∑' q : XiZeroCopy,
        if xiSpectralSqRe q = ω then ((Real.exp (-(a * xiSpectralSqRe q)) : ℝ) : ℂ) else 0 := by
    refine tsum_congr fun q => ?_
    simp only [sub_eq_zero, c]
    split_ifs <;> simp
  rw [← hval]
  exact hlim.congr' (hrepr.mono fun B hB => hB.symm)

/-- **The archimedean part has no vertical spectrum.**  For every `a > 0` and every `λ`, the Bohr
coefficient of `Arch(a + ib)` at frequency `λ` vanishes. -/
theorem tendsto_bohrCoeff_gaussianArchCriticalC {a : ℝ} (ha : 0 < a) (ω : ℝ) :
    Tendsto (fun B : ℝ => (1 / (B : ℂ)) *
        ∫ b in (0 : ℝ)..B, gaussianArchCriticalC ((a : ℂ) + b * I) * Complex.exp (I * ω * b))
      atTop (𝓝 0) := by
  set L : ℝ → ℂ := fun x => logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))
  have hL : Continuous L := continuous_logDeriv_archFactor_critical
  set g : ℝ → ℝ := fun x => Real.exp (-(a * x ^ 2)) * ‖L x‖
  have hg : Integrable g := by
    have h := (integrable_xiGaussianCenteredArchIntegrand ha 0).norm
    refine h.congr (Eventually.of_forall fun x => ?_)
    show ‖xiGaussianCenteredArchIntegrand a 0 x‖ = g x
    rw [xiGaussianCenteredArchIntegrand_eq, pow_zero, one_mul, norm_mul,
      norm_exp_neg_ofReal_mul_sq]
  -- Fubini on `[0, B] × ℝ`
  have hfub : ∀ B : ℝ, 0 ≤ B →
      (∫ b in (0 : ℝ)..B, gaussianArchCriticalC ((a : ℂ) + b * I) * Complex.exp (I * ω * b)) =
        ∫ x : ℝ, (Real.exp (-(a * x ^ 2)) : ℂ) * L x * ∫ b in (0 : ℝ)..B,
          Complex.exp (-(I * (x ^ 2 - ω : ℝ)) * b) := by
    intro B hB
    set F : ℝ → ℝ → ℂ := fun b x => Complex.exp (-((a : ℂ) + b * I) * (x : ℂ) ^ (2 : ℕ)) * L x *
      Complex.exp (I * ω * b)
    have hFeq : ∀ b x, F b x = (Real.exp (-(a * x ^ 2)) : ℂ) * L x *
        Complex.exp (-(I * (x ^ 2 - ω : ℝ)) * b) := by
      intro b x
      simp only [F]
      calc Complex.exp (-((a : ℂ) + b * I) * (x : ℂ) ^ (2 : ℕ)) * L x * Complex.exp (I * ω * b)
          = Complex.exp (-((a : ℂ) + b * I) * (x : ℂ) ^ (2 : ℕ) + I * ω * b) * L x := by
            rw [Complex.exp_add]; ring
        _ = Complex.exp (((-(a * x ^ 2) : ℝ) : ℂ) + -(I * ((x ^ 2 - ω : ℝ) : ℂ)) * b) * L x := by
            congr 2; push_cast; ring
        _ = _ := by rw [Complex.exp_add, Complex.ofReal_exp]; ring
    have hFcont : Continuous (Function.uncurry F) := by
      simp only [F]
      exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.exp (-((a : ℂ) + p.1 * I) * (p.2 : ℂ) ^ (2 : ℕ)))).mul
          (hL.comp continuous_snd) |>.mul (by fun_prop)
    have hFint : Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 B)).prod volume) := by
      have hprod : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * g p.2)
          ((volume.restrict (Ioc 0 B)).prod volume) :=
        (integrable_const (1 : ℝ)).mul_prod hg
      refine hprod.mono' hFcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      show ‖F p.1 p.2‖ ≤ 1 * g p.2
      rw [hFeq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), norm_exp_neg_I_mul_ofReal_mul, mul_one, one_mul]
    rw [intervalIntegral.integral_of_le hB]
    have hsw := integral_integral_swap hFint
    have h1 : (∫ b in Ioc 0 B, gaussianArchCriticalC ((a : ℂ) + b * I) * Complex.exp (I * ω * b)) =
        ∫ b in Ioc 0 B, ∫ x : ℝ, F b x := by
      refine setIntegral_congr_fun measurableSet_Ioc fun b _ => ?_
      simp only [F, gaussianArchCriticalC]
      rw [← integral_mul_const]
    rw [h1, hsw]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [intervalIntegral.integral_of_le hB, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc fun b _ => by rw [hFeq]
  -- dominated convergence in `x`
  have hlim : Tendsto (fun B : ℝ => ∫ x : ℝ, (Real.exp (-(a * x ^ 2)) : ℂ) * L x *
      fejerExp B (x ^ 2 - ω)) atTop (𝓝 (∫ x : ℝ, (0 : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hg ?_
    · refine Eventually.of_forall fun B => ?_
      have hcont : Continuous fun x : ℝ => fejerExp B (x ^ 2 - ω) :=
        (continuous_fejerExp B).comp (by fun_prop)
      exact ((by fun_prop : Continuous fun x : ℝ => ((Real.exp (-(a * x ^ 2)) : ℝ) : ℂ)).mul hL
        |>.mul hcont).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (by positivity) (norm_fejerExp_le hB _)
    · have hfin : ({x : ℝ | x ^ 2 - ω = 0} : Set ℝ).Finite := by
        have hsub : {x : ℝ | x ^ 2 - ω = 0} ⊆ {Real.sqrt ω, -Real.sqrt ω} := by
          intro x hx
          simp only [mem_setOf_eq, sub_eq_zero] at hx
          simp only [mem_insert_iff, mem_singleton_iff]
          by_cases h0 : 0 ≤ x
          · left; rw [← hx, Real.sqrt_sq h0]
          · right; rw [← hx, Real.sqrt_sq_eq_abs, abs_of_neg (not_le.1 h0), neg_neg]
        exact (Set.toFinite _).subset hsub
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ^ 2 - ω ≠ 0 := by
        rw [ae_iff]
        simp only [ne_eq, not_not]
        exact hfin.measure_zero volume
      filter_upwards [hae] with x hx
      have := (tendsto_fejerExp (x ^ 2 - ω)).const_mul ((Real.exp (-(a * x ^ 2)) : ℂ) * L x)
      rw [if_neg hx, mul_zero] at this
      exact this
  rw [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
  rw [hfub B hB, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [fejerExp]
  ring

/-- The pole has vertical spectrum only at `-1/4`. -/
theorem tendsto_bohrCoeff_gaussianArchPoleC {a ω : ℝ} (hω : ω ≠ -(1 / 4)) :
    Tendsto (fun B : ℝ => (1 / (B : ℂ)) *
        ∫ b in (0 : ℝ)..B, gaussianArchPoleC ((a : ℂ) + b * I) * Complex.exp (I * ω * b))
      atTop (𝓝 0) := by
  have hp : xiMassArchPole ^ (2 : ℕ) = -(1 / 4 : ℂ) := by
    rw [xiMassArchPole, div_pow, neg_pow, I_sq]; norm_num
  have heq : ∀ b : ℝ, gaussianArchPoleC ((a : ℂ) + b * I) * Complex.exp (I * ω * b) =
      (2 * Real.pi * Real.exp (a / 4) : ℂ) * Complex.exp (-(I * ((-(ω + 1 / 4)) : ℝ)) * b) := by
    intro b
    rw [gaussianArchPoleC, hp]
    calc 2 * (Real.pi : ℂ) * Complex.exp (-((a : ℂ) + b * I) * -(1 / 4 : ℂ)) * Complex.exp (I * ω * b)
        = 2 * (Real.pi : ℂ) * Complex.exp (-((a : ℂ) + b * I) * -(1 / 4 : ℂ) + I * ω * b) := by
          rw [Complex.exp_add]; ring
      _ = 2 * (Real.pi : ℂ) * Complex.exp (((a / 4 : ℝ) : ℂ) + -(I * ((-(ω + 1 / 4) : ℝ) : ℂ)) * b) := by
          congr 2; push_cast; ring
      _ = _ := by rw [Complex.exp_add, Complex.ofReal_exp]; ring
  have h := (tendsto_fejerExp (-(ω + 1 / 4))).const_mul (2 * Real.pi * Real.exp (a / 4) : ℂ)
  have hne : -(ω + 1 / 4) ≠ 0 := by intro h0; apply hω; linarith
  rw [if_neg hne, mul_zero] at h
  refine h.congr fun B => ?_
  simp only [fejerExp]
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- **Vertical spectral law for the prime chirp.**  Under RH, for every `a > 0` and `λ ≥ 0`, the
Bohr coefficient of `(π/τ)^{1/2} S(τ)` along `Re τ = a` at frequency `λ` is
`-π Σ_{q : λ_q = λ} e^{-aλ}`. -/
theorem tendsto_bohrCoeff_gaussianPrimeChirpC_of_rh (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 0 < a) {ω : ℝ} (hω : 0 ≤ ω) :
    Tendsto (fun B : ℝ => (1 / (B : ℂ)) *
        ∫ b in (0 : ℝ)..B, gaussianPrimeChirpC ((a : ℂ) + b * I) * Complex.exp (I * ω * b))
      atTop (𝓝 (-((Real.pi : ℂ) * ∑' q : XiZeroCopy,
        if xiSpectralSqRe q = ω then ((Real.exp (-(a * xiSpectralSqRe q)) : ℝ) : ℂ) else 0))) := by
  have hA := tendsto_bohrCoeff_gaussianArchCriticalC ha ω
  have hP := tendsto_bohrCoeff_gaussianArchPoleC (a := a) (ω := ω) (by linarith)
  have hN := (tendsto_bohrCoeff_xiGaussianHeatTraceC_of_rh hRH ha ω).const_mul (Real.pi : ℂ)
  have h := (hA.add hP).sub hN
  rw [zero_add, zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
  have hre : ∀ b : ℝ, 0 < ((a : ℂ) + b * I).re := fun b => by simpa using ha
  have hcontA : Continuous fun b : ℝ => gaussianArchCriticalC ((a : ℂ) + b * I) *
      Complex.exp (I * ω * b) := by
    refine Continuous.mul (continuous_iff_continuousAt.2 fun b => ?_) (by fun_prop)
    exact ContinuousAt.comp (g := gaussianArchCriticalC) (f := fun b : ℝ => (a : ℂ) + b * I)
      (differentiableAt_gaussianArchCriticalC (hre b)).continuousAt
      ((by fun_prop : Continuous fun b : ℝ => (a : ℂ) + b * I).continuousAt)
  have hcontP : Continuous fun b : ℝ => gaussianArchPoleC ((a : ℂ) + b * I) *
      Complex.exp (I * ω * b) := by
    unfold gaussianArchPoleC; fun_prop
  have hcontN : Continuous fun b : ℝ => xiGaussianHeatTraceC ((a : ℂ) + b * I) *
      Complex.exp (I * ω * b) :=
    (continuous_xiGaussianHeatTraceC_vertical ha).mul (by fun_prop)
  have hsplit : ∀ b : ℝ, gaussianPrimeChirpC ((a : ℂ) + b * I) * Complex.exp (I * ω * b) =
      gaussianArchCriticalC ((a : ℂ) + b * I) * Complex.exp (I * ω * b) +
        gaussianArchPoleC ((a : ℂ) + b * I) * Complex.exp (I * ω * b) -
          (Real.pi : ℂ) * (xiGaussianHeatTraceC ((a : ℂ) + b * I) * Complex.exp (I * ω * b)) := by
    intro b
    have := pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime (hre b)
    linear_combination (Complex.exp (I * ω * b)) * this
  simp_rw [hsplit]
  have hAP : IntervalIntegrable (fun b : ℝ => gaussianArchCriticalC ((a : ℂ) + b * I) *
      Complex.exp (I * ω * b) + gaussianArchPoleC ((a : ℂ) + b * I) * Complex.exp (I * ω * b))
      volume 0 B := (hcontA.add hcontP).intervalIntegrable _ _
  have hN' : IntervalIntegrable (fun b : ℝ => (Real.pi : ℂ) *
      (xiGaussianHeatTraceC ((a : ℂ) + b * I) * Complex.exp (I * ω * b))) volume 0 B :=
    (hcontN.const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hAP hN',
    intervalIntegral.integral_add (hcontA.intervalIntegrable _ _) (hcontP.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  ring

end

end RHTower
