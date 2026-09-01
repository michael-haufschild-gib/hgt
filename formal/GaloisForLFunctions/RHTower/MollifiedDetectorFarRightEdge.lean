import GaloisForLFunctions.RHTower.HalfPlaneDecayVerticalIntegral
import GaloisForLFunctions.RHTower.MollifiedDetectorFarRightDecay

/-!
# The far-right edge of the Littlewood rectangle is `O(1)`

Let `H` be analytic on an open half-plane and satisfy `‖H − 1‖ ≤ K e^{-α Re s}` there, with the
bound below `½` on the whole half-plane.  Then `F = Log H` is analytic there, obeys the same decay
up to a factor `2`, and its derivative is `logDeriv H`, with decay `2Ke^{α}e^{-α Re s}` by Cauchy's
estimate on the unit disc.

Feeding both into `norm_integral_vertical_le_of_halfPlane_decay` bounds the two far-right boundary
integrals of Littlewood's functional by absolute constants, independently of the window length.
This is what makes Levinson's budget `(L/2)·log c + o(L)` rather than `(L/2)·log c + Θ(L)`.
-/

open Complex Metric MeasureTheory Set Filter intervalIntegral Topology

noncomputable section

namespace RHTower

variable {H : ℂ → ℂ} {d₀ K α : ℝ}

/-- On the half-plane the principal logarithm of `H` is analytic. -/
theorem analyticOnNhd_clog_comp
    (hHana : ∀ z : ℂ, d₀ < z.re → AnalyticAt ℂ H z)
    (hHsmall : ∀ z : ℂ, d₀ < z.re → ‖H z - 1‖ ≤ 1 / 2) :
    AnalyticOnNhd ℂ (fun z => Complex.log (H z)) {z : ℂ | d₀ < z.re} := by
  have hopen : IsOpen {z : ℂ | d₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  intro z hz
  have hslit : H z ∈ Complex.slitPlane := mem_slitPlane_of_norm_sub_one_le (hHsmall z hz)
  exact ((Complex.differentiableAt_log hslit).comp z
    (hHana z hz).differentiableAt).differentiableWithinAt

/-- Its derivative is the logarithmic derivative of `H`. -/
theorem deriv_clog_comp {z : ℂ}
    (hHana : ∀ w : ℂ, d₀ < w.re → AnalyticAt ℂ H w)
    (hHsmall : ∀ w : ℂ, d₀ < w.re → ‖H w - 1‖ ≤ 1 / 2) (hz : d₀ < z.re) :
    deriv (fun w => Complex.log (H w)) z = logDeriv H z := by
  have hslit : H z ∈ Complex.slitPlane := mem_slitPlane_of_norm_sub_one_le (hHsmall z hz)
  have hne : H z ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hcomp := (Complex.hasDerivAt_log hslit).comp z
    ((hHana z hz).differentiableAt.hasDerivAt)
  have hcomp' : HasDerivAt (fun w => Complex.log (H w)) ((H z)⁻¹ * deriv H z) z := hcomp
  rw [hcomp'.deriv, logDeriv_apply]
  field_simp

/-- **The far-right logarithm integral is `O(1)`.** -/
theorem abs_integral_log_norm_farRight_le
    (hα : 0 < α) (hK : 0 ≤ K) {d T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) (hd : d₀ < d)
    (hHana : ∀ z : ℂ, d₀ < z.re → AnalyticAt ℂ H z)
    (hHdec : ∀ z : ℂ, d₀ < z.re → ‖H z - 1‖ ≤ K * Real.exp (-α * z.re))
    (hHsmall : ∀ z : ℂ, d₀ < z.re → ‖H z - 1‖ ≤ 1 / 2) :
    |∫ t in T₁..T₂, Real.log ‖H ((d : ℂ) + (t : ℂ) * I)‖|
      ≤ 2 * (2 * K * Real.exp (-α * d) / α) := by
  set F : ℂ → ℂ := fun z => Complex.log (H z) with hF
  have hFana : ∀ z : ℂ, d ≤ z.re → AnalyticAt ℂ F z := by
    intro z hz
    exact analyticOnNhd_clog_comp hHana hHsmall z (by simpa using lt_of_lt_of_le hd hz)
  have hFdec : ∀ z : ℂ, d ≤ z.re → ‖F z‖ ≤ (2 * K) * Real.exp (-α * z.re) := by
    intro z hz
    have hzd : d₀ < z.re := lt_of_lt_of_le hd hz
    have h1 := norm_clog_le_of_norm_sub_one_le (hHsmall z hzd)
    have h2 := hHdec z hzd
    have hnn : (0 : ℝ) ≤ Real.exp (-α * z.re) := (Real.exp_pos _).le
    calc ‖F z‖ ≤ 2 * ‖H z - 1‖ := h1
      _ ≤ 2 * (K * Real.exp (-α * z.re)) := by linarith
      _ = (2 * K) * Real.exp (-α * z.re) := by ring
  have hmain := norm_integral_vertical_le_of_halfPlane_decay (F := F) (d := d)
    (T₁ := T₁) (T₂ := T₂) (K := 2 * K) (α := α) hT hα (by linarith) hFana hFdec
  have hint : IntervalIntegrable (fun t : ℝ => F ((d : ℂ) + (t : ℂ) * I)) volume T₁ T₂ := by
    refine Continuous.intervalIntegrable ?_ T₁ T₂
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hre : d ≤ ((d : ℂ) + (t : ℂ) * I).re := by simp
    have hc : ContinuousAt (F ∘ (fun y : ℝ => (d : ℂ) + (y : ℂ) * I)) t :=
      ContinuousAt.comp ((hFana _ hre).continuousAt)
        (by fun_prop : ContinuousAt (fun y : ℝ => (d : ℂ) + (y : ℂ) * I) t)
    simpa [Function.comp_def] using hc
  have hre : (∫ t in T₁..T₂, Real.log ‖H ((d : ℂ) + (t : ℂ) * I)‖)
      = (∫ t in T₁..T₂, F ((d : ℂ) + (t : ℂ) * I)).re := by
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint
    have hcongr : (∫ t in T₁..T₂, Real.log ‖H ((d : ℂ) + (t : ℂ) * I)‖)
        = ∫ t in T₁..T₂, (F ((d : ℂ) + (t : ℂ) * I)).re := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hF]
      exact (Complex.log_re _).symm
    rw [hcongr]
    simpa using hcomm
  rw [hre]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  calc ‖∫ t in T₁..T₂, F ((d : ℂ) + (t : ℂ) * I)‖
      ≤ 2 * ((2 * K) * Real.exp (-α * d) / α) := hmain
    _ = 2 * (2 * K * Real.exp (-α * d) / α) := by ring


/-- **The far-right logarithmic-derivative integral is `O(1)`.** -/
theorem abs_integral_re_logDeriv_farRight_le
    (hα : 0 < α) (hK : 0 ≤ K) {d T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) (hd : d₀ + 1 < d)
    (hHana : ∀ z : ℂ, d₀ < z.re → AnalyticAt ℂ H z)
    (hHdec : ∀ z : ℂ, d₀ < z.re → ‖H z - 1‖ ≤ K * Real.exp (-α * z.re))
    (hHsmall : ∀ z : ℂ, d₀ < z.re → ‖H z - 1‖ ≤ 1 / 2) :
    |∫ t in T₁..T₂, (logDeriv H ((d : ℂ) + (t : ℂ) * I)).re|
      ≤ 2 * ((2 * K * Real.exp α) * Real.exp (-α * d) / α) := by
  set F : ℂ → ℂ := fun z => Complex.log (H z) with hF
  have hFall := analyticOnNhd_clog_comp hHana hHsmall
  have hFdec : ∀ z : ℂ, d₀ < z.re → ‖F z‖ ≤ (2 * K) * Real.exp (-α * z.re) := by
    intro z hz
    have h1 := norm_clog_le_of_norm_sub_one_le (hHsmall z hz)
    have h2 := hHdec z hz
    calc ‖F z‖ ≤ 2 * ‖H z - 1‖ := h1
      _ ≤ 2 * (K * Real.exp (-α * z.re)) := by linarith
      _ = (2 * K) * Real.exp (-α * z.re) := by ring
  set G : ℂ → ℂ := deriv F with hG
  have hGana : ∀ z : ℂ, d ≤ z.re → AnalyticAt ℂ G z := by
    intro z hz
    exact (hFall z (by simpa using lt_of_lt_of_le (by linarith : d₀ < d) hz)).deriv
  have hGdec : ∀ z : ℂ, d ≤ z.re → ‖G z‖ ≤ (2 * K * Real.exp α) * Real.exp (-α * z.re) := by
    intro z hz
    have hball : ∀ w : ℂ, ‖w - z‖ ≤ 1 → d₀ < w.re := by
      intro w hw
      have h := Complex.abs_re_le_norm (w - z)
      rw [Complex.sub_re] at h
      have habs : |w.re - z.re| ≤ 1 := le_trans h hw
      rw [abs_le] at habs
      linarith [habs.1]
    have hdcc : DiffContOnCl ℂ F (ball z 1) := by
      constructor
      · intro w hw
        rw [mem_ball, Complex.dist_eq] at hw
        exact ((hFall w (by simpa using hball w hw.le)).differentiableAt).differentiableWithinAt
      · rw [closure_ball z (by norm_num : (1 : ℝ) ≠ 0)]
        intro w hw
        rw [mem_closedBall, Complex.dist_eq] at hw
        exact ((hFall w (by simpa using hball w hw)).continuousAt).continuousWithinAt
    have hC : ∀ w ∈ sphere z (1 : ℝ),
        ‖F w‖ ≤ (2 * K * Real.exp α) * Real.exp (-α * z.re) := by
      intro w hw
      rw [mem_sphere, Complex.dist_eq] at hw
      have hwd : d₀ < w.re := hball w hw.le
      refine le_trans (hFdec w hwd) ?_
      have hwre : z.re - 1 ≤ w.re := by
        have h := Complex.abs_re_le_norm (w - z)
        rw [Complex.sub_re] at h
        have habs : |w.re - z.re| ≤ 1 := le_trans h hw.le
        rw [abs_le] at habs
        linarith [habs.1]
      have hmono : Real.exp (-α * w.re) ≤ Real.exp (-α * (z.re - 1)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hwre, hα]
      have hval : Real.exp (-α * (z.re - 1)) = Real.exp α * Real.exp (-α * z.re) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hKnn : (0 : ℝ) ≤ 2 * K := by linarith
      calc (2 * K) * Real.exp (-α * w.re)
          ≤ (2 * K) * Real.exp (-α * (z.re - 1)) := mul_le_mul_of_nonneg_left hmono hKnn
        _ = (2 * K * Real.exp α) * Real.exp (-α * z.re) := by rw [hval]; ring
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by norm_num : (0 : ℝ) < 1) hdcc hC
    simpa [hG] using hcauchy
  have hmain := norm_integral_vertical_le_of_halfPlane_decay (F := G) (d := d)
    (T₁ := T₁) (T₂ := T₂) (K := 2 * K * Real.exp α) (α := α) hT hα
    (by positivity) hGana hGdec
  have hint : IntervalIntegrable (fun t : ℝ => G ((d : ℂ) + (t : ℂ) * I)) volume T₁ T₂ := by
    refine Continuous.intervalIntegrable ?_ T₁ T₂
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hre : d ≤ ((d : ℂ) + (t : ℂ) * I).re := by simp
    have hc : ContinuousAt (G ∘ (fun y : ℝ => (d : ℂ) + (y : ℂ) * I)) t :=
      ContinuousAt.comp ((hGana _ hre).continuousAt)
        (by fun_prop : ContinuousAt (fun y : ℝ => (d : ℂ) + (y : ℂ) * I) t)
    simpa [Function.comp_def] using hc
  have hcongr : (∫ t in T₁..T₂, (logDeriv H ((d : ℂ) + (t : ℂ) * I)).re)
      = ∫ t in T₁..T₂, (G ((d : ℂ) + (t : ℂ) * I)).re := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hre : d₀ < ((d : ℂ) + (t : ℂ) * I).re := by simpa using (by linarith : d₀ < d)
    rw [hG, deriv_clog_comp hHana hHsmall hre]
  rw [hcongr]
  have hre2 : (∫ t in T₁..T₂, (G ((d : ℂ) + (t : ℂ) * I)).re)
      = (∫ t in T₁..T₂, G ((d : ℂ) + (t : ℂ) * I)).re := by
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint
    simpa using hcomm
  rw [hre2]
  exact le_trans (Complex.abs_re_le_norm _) hmain

end RHTower

end
