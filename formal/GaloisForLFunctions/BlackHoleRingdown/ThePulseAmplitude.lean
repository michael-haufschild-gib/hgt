import GaloisForLFunctions.BlackHoleRingdown.TheImageFieldOfAPulse

/-!
# The amplitude of a pulse

A compact pulse has the entire amplitude `a(w) = (2π)⁻¹ ∫ h(S) e^{-iwS} dS`. Integrating by parts gives
`a_{h'}(w) = iw a_h(w)`, so `a` decays faster than every power on each horizontal strip. Fourier inversion
applied to `h(S) e^{-cS}` recovers the pulse on every vertical line of `u = iw`:

`h(S) = ∫ a(-iu) e^{uS} dy`,   `u = c + iy`,

and `∫ h(S) e^{-wS} dS = 2π a(-iw)` by definition.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

/-- An entire amplitude decaying faster than every power on each horizontal strip. -/
structure RapidAmplitude (a : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ a
  decay : ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.im| ≤ A → ‖a w‖ * (1 + |w.re|) ^ n ≤ C

/-- The integrable weight `(1+|ξ|)^{-2}`. -/
theorem integrable_inv_one_add_abs_sq : Integrable fun ξ : ℝ => ((1 + |ξ|) ^ 2)⁻¹ := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
    (by simp [Module.finrank_self])
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity)]
  norm_num

/-- A rapid amplitude against a polynomial is dominated by `(1+|Re w|)^{-2}`. -/
theorem RapidAmplitude.exists_mul_poly_le {a : ℂ → ℂ} (ha : RapidAmplitude a) (A : ℝ) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.im| ≤ A →
      ‖a w‖ * (1 + |w.re|) ^ M ≤ C * ((1 + |w.re|) ^ 2)⁻¹ := by
  obtain ⟨C, hC, h⟩ := ha.decay A (M + 2)
  refine ⟨C, hC, fun w hw => ?_⟩
  have hp : 0 < (1 + |w.re|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_assoc, ← pow_add]
  exact h w hw

theorem fourierInv_eq_integral_exp (g : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ g x = ∫ v : ℝ, Complex.exp (((2 * Real.pi * v * x : ℝ)) * Complex.I) • g v := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  have harg : (-2 * Real.pi * v * (-x) : ℝ) = (2 * Real.pi * v * x : ℝ) := by ring
  simp only [smul_eq_mul]
  rw [harg]

/-- The amplitude of a pulse. -/
def pulseAmplitude (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ S : ℝ, h S * Complex.exp (-(I * w * (S : ℂ)))

namespace CompactPulse

variable (h : CompactPulse)

theorem continuous_toFun : Continuous h.toFun := h.smooth.continuous

theorem integrable_mul_cexp (w : ℂ) :
    Integrable fun S : ℝ => h S * Complex.exp (-(I * w * (S : ℂ))) := by
  refine Continuous.integrable_of_hasCompactSupport (h.continuous_toFun.mul (by fun_prop)) ?_
  exact h.compact.mul_right

theorem integrable_toFun : Integrable h.toFun :=
  h.continuous_toFun.integrable_of_hasCompactSupport h.compact

/-- The kernel is bounded on the support. -/
theorem norm_mul_cexp_le {S₀ : ℝ} (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) (w : ℂ) (S : ℝ) :
    ‖h S * Complex.exp (-(I * w * (S : ℂ)))‖ ≤ ‖h S‖ * Real.exp (|w.im| * S₀) := by
  by_cases hs : S₀ < |S|
  · rw [hS₀ S hs]
    simp
  · rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : (-(I * w * (S : ℂ))).re = w.im * S := by simp
    rw [hre]
    calc w.im * S ≤ |w.im * S| := le_abs_self _
      _ = |w.im| * |S| := abs_mul _ _
      _ ≤ |w.im| * S₀ := mul_le_mul_of_nonneg_left (not_lt.mp hs) (abs_nonneg _)

/-- The amplitude is bounded on horizontal strips. -/
theorem exists_norm_amplitude_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.im| ≤ A → ‖pulseAmplitude h w‖ ≤ C := by
  obtain ⟨S₀, hS0, hS₀⟩ := h.exists_support_bound
  have hA : Integrable fun S : ℝ => ‖h S‖ := h.integrable_toFun.norm
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨(2 * Real.pi)⁻¹ * ((∫ S : ℝ, ‖h S‖) * Real.exp (|A| * S₀)),
    mul_nonneg (by positivity) (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (by positivity)),
    fun w hw => ?_⟩
  rw [pulseAmplitude, norm_mul]
  have h1 : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hG : Integrable fun S : ℝ => ‖h S‖ * Real.exp (|A| * S₀) := hA.mul_const _
  refine (norm_integral_le_of_norm_le hG (Eventually.of_forall fun S => ?_)).trans
    (le_of_eq (integral_mul_const _ _))
  refine (h.norm_mul_cexp_le hS₀ w S).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hS0)
  exact hw.trans (le_abs_self A)

/-- **Integration by parts.** -/
theorem amplitude_D (w : ℂ) : pulseAmplitude h.D w = I * w * pulseAmplitude h w := by
  have hv : ∀ S : ℝ, HasDerivAt (fun q : ℝ => Complex.exp (-(I * w * (q : ℂ))))
      (Complex.exp (-(I * w * (S : ℂ))) * (-(I * w))) S := by
    intro S
    have h1 : HasDerivAt (fun q : ℝ => -(I * w * (q : ℂ))) (-(I * w)) S := by
      have h0 := (Complex.ofRealCLM.hasDerivAt (x := S)).const_mul (-(I * w))
      refine (h0.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
      simp only [Complex.ofRealCLM_apply]
      ring
    exact h1.cexp
  have hcomp : Continuous fun S : ℝ => Complex.exp (-(I * w * (S : ℂ))) := by fun_prop
  have huv : Integrable ((h : ℝ → ℂ) * fun S : ℝ => Complex.exp (-(I * w * (S : ℂ)))) :=
    h.integrable_mul_cexp w
  have huv' : Integrable ((h : ℝ → ℂ) * fun S : ℝ =>
      Complex.exp (-(I * w * (S : ℂ))) * (-(I * w))) := by
    have := (h.integrable_mul_cexp w).mul_const (-(I * w))
    refine this.congr (Eventually.of_forall fun S => ?_)
    simp only [Pi.mul_apply]
    ring
  have hu'v : Integrable ((h.D : ℝ → ℂ) * fun S : ℝ => Complex.exp (-(I * w * (S : ℂ)))) :=
    h.D.integrable_mul_cexp w
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable (u := (h : ℝ → ℂ)) (u' := h.D)
    (v := fun S : ℝ => Complex.exp (-(I * w * (S : ℂ))))
    (v' := fun S : ℝ => Complex.exp (-(I * w * (S : ℂ))) * (-(I * w)))
    (fun S _ => h.hasDerivAt S) (fun S _ => hv S) huv' hu'v huv
  have hleft : ∫ S : ℝ, h S * (Complex.exp (-(I * w * (S : ℂ))) * (-(I * w))) =
      (-(I * w)) * ∫ S : ℝ, h S * Complex.exp (-(I * w * (S : ℂ))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun S => ?_)
    simp only
    ring
  rw [hleft] at hparts
  rw [pulseAmplitude, pulseAmplitude]
  linear_combination ((2 * Real.pi : ℂ)⁻¹) * hparts

/-- **The amplitude of a pulse is entire.** -/
theorem differentiable_amplitude : Differentiable ℂ (pulseAmplitude h) := by
  intro w₀
  obtain ⟨S₀, hS0, hS₀⟩ := h.exists_support_bound
  set B := |w₀.im| + 1 with hB
  have hbound : ∀ w ∈ Metric.ball w₀ 1, ∀ S : ℝ,
      ‖h S * ((-(I * (S : ℂ))) * Complex.exp (-(I * w * (S : ℂ))))‖ ≤
        ‖h S‖ * (S₀ * Real.exp (B * S₀)) := by
    intro w hw S
    by_cases hs : S₀ < |S|
    · rw [hS₀ S hs]
      simp
    · have hS : |S| ≤ S₀ := not_lt.mp hs
      have him : |w.im| ≤ B := by
        have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
          have := Complex.abs_im_le_norm (w - w₀)
          simpa using this
        have h2 : ‖w - w₀‖ < 1 := by simpa [dist_eq_norm] using hw
        have h3 := abs_sub_abs_le_abs_sub w.im w₀.im
        rw [hB]
        linarith
      rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_exp]
      refine mul_le_mul_of_nonneg_left (mul_le_mul hS (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hS0)
        (norm_nonneg _)
      have hre : (-(I * w * (S : ℂ))).re = w.im * S := by simp
      rw [hre]
      calc w.im * S ≤ |w.im * S| := le_abs_self _
        _ = |w.im| * |S| := abs_mul _ _
        _ ≤ B * S₀ := mul_le_mul him hS (abs_nonneg _) (by positivity)
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable
      (fun S : ℝ => h S * Complex.exp (-(I * w * (S : ℂ)))) volume := fun w =>
    (h.integrable_mul_cexp w).aestronglyMeasurable
  have hderivMeas : AEStronglyMeasurable
      (fun S : ℝ => h S * ((-(I * (S : ℂ))) * Complex.exp (-(I * w₀ * (S : ℂ))))) volume :=
    (h.continuous_toFun.mul (by fun_prop)).aestronglyMeasurable
  have hdiff := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (S : ℝ) => h S * Complex.exp (-(I * w * (S : ℂ))))
    (F' := fun (w : ℂ) (S : ℝ) => h S * ((-(I * (S : ℂ))) * Complex.exp (-(I * w * (S : ℂ)))))
    (x₀ := w₀) (s := Metric.ball w₀ 1) (bound := fun S => ‖h S‖ * (S₀ * Real.exp (B * S₀)))
    (Metric.ball_mem_nhds _ one_pos) (Eventually.of_forall hmeas) (h.integrable_mul_cexp w₀)
    hderivMeas (Eventually.of_forall fun S w hw => hbound w hw S)
    (h.integrable_toFun.norm.mul_const _) (Eventually.of_forall fun S w _ => ?_)).2
  · exact (hdiff.differentiableAt.const_mul _)
  · have h1 : HasDerivAt (fun v : ℂ => -(I * v * (S : ℂ))) (-(I * (S : ℂ))) w := by
      have h0 := (hasDerivAt_id w).const_mul (-(I * (S : ℂ)))
      refine (h0.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
      simp only [id]
      ring
    have h2 := h1.cexp.const_mul (h S)
    refine h2.congr_deriv ?_
    ring

/-- The bound `‖a(w)‖ (1+‖w‖)^n ≤ C` on strips, by induction on `n` over all pulses. -/
theorem exists_amplitude_mul_pow_le (A : ℝ) (n : ℕ) : ∀ h : CompactPulse,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.im| ≤ A → ‖pulseAmplitude h w‖ * (1 + ‖w‖) ^ n ≤ C := by
  induction n with
  | zero =>
    intro h
    obtain ⟨C, hC, hb⟩ := h.exists_norm_amplitude_le A
    exact ⟨C, hC, fun w hw => by simpa using hb w hw⟩
  | succ n ih =>
    intro h
    obtain ⟨C₁, hC₁, h₁⟩ := ih h
    obtain ⟨C₂, hC₂, h₂⟩ := ih h.D
    refine ⟨C₁ + C₂, by positivity, fun w hw => ?_⟩
    have hD : ‖pulseAmplitude h.D w‖ = ‖w‖ * ‖pulseAmplitude h w‖ := by
      rw [h.amplitude_D, norm_mul, norm_mul, Complex.norm_I, one_mul]
    have h2 := h₂ w hw
    rw [hD] at h2
    calc ‖pulseAmplitude h w‖ * (1 + ‖w‖) ^ (n + 1)
        = ‖pulseAmplitude h w‖ * (1 + ‖w‖) ^ n + ‖w‖ * ‖pulseAmplitude h w‖ * (1 + ‖w‖) ^ n := by
          rw [pow_succ]
          ring
      _ ≤ C₁ + C₂ := add_le_add (h₁ w hw) h2

/-- **The amplitude of a pulse is rapid.** -/
theorem rapidAmplitude : RapidAmplitude (pulseAmplitude h) where
  entire := h.differentiable_amplitude
  decay := fun A n => by
    obtain ⟨C, hC, hb⟩ := exists_amplitude_mul_pow_le A n h
    refine ⟨C, hC, fun w hw => ?_⟩
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hb w hw)
    refine pow_le_pow_left₀ (by positivity) ?_ n
    linarith [Complex.abs_re_le_norm w]

/-- The Laplace transform of the pulse is the amplitude. -/
theorem integral_mul_cexp_eq (w : ℂ) :
    ∫ S : ℝ, h S * Complex.exp (-w * (S : ℂ)) = 2 * Real.pi * pulseAmplitude h (-I * w) := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [pulseAmplitude, mul_inv_cancel_left₀ hpi]
  refine integral_congr_ae (Eventually.of_forall fun S => ?_)
  simp only
  congr 2
  linear_combination (-(w * (S : ℂ))) * I_sq

/-- The damped pulse `h(S) e^{-cS}`. -/
def damped (c : ℝ) (S : ℝ) : ℂ := h S * Complex.exp (-(c : ℂ) * (S : ℂ))

theorem continuous_damped (c : ℝ) : Continuous (h.damped c) :=
  h.continuous_toFun.mul (by fun_prop)

theorem integrable_damped (c : ℝ) : Integrable (h.damped c) :=
  (h.continuous_damped c).integrable_of_hasCompactSupport h.compact.mul_right

/-- The Fourier transform of the damped pulse is the amplitude on a shifted line. -/
theorem fourier_damped (c ξ : ℝ) :
    𝓕 (h.damped c) ξ = 2 * Real.pi * pulseAmplitude h (((2 * Real.pi * ξ : ℝ) : ℂ) - c * I) := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [Real.fourier_real_eq_integral_exp_smul, pulseAmplitude, mul_inv_cancel_left₀ hpi]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [damped, smul_eq_mul]
  have he : Complex.exp ((-2 * Real.pi * v * ξ : ℝ) * I) * Complex.exp (-(c : ℂ) * (v : ℂ)) =
      Complex.exp (-(I * (((2 * Real.pi * ξ : ℝ) : ℂ) - c * I) * (v : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(c : ℂ) * (v : ℂ)) * I_sq
  rw [← he]
  ring

/-- The amplitude on a horizontal line is integrable. -/
theorem integrable_amplitude_line (c : ℝ) :
    Integrable fun y : ℝ => pulseAmplitude h ((y : ℂ) - c * I) := by
  obtain ⟨C, hC, hb⟩ := h.rapidAmplitude.exists_mul_poly_le |c| 0
  have hcont : Continuous fun y : ℝ => pulseAmplitude h ((y : ℂ) - c * I) :=
    h.differentiable_amplitude.continuous.comp (by fun_prop)
  refine (integrable_inv_one_add_abs_sq.const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have him : ((y : ℂ) - c * I).im = -c := by simp
  have hre : ((y : ℂ) - c * I).re = y := by simp
  have := hb ((y : ℂ) - c * I) (by rw [him, abs_neg])
  rw [hre, pow_zero, mul_one] at this
  exact this

/-- **Fourier inversion on a line.** -/
theorem eq_integral_amplitude_line (c S : ℝ) :
    h S = ∫ y : ℝ, pulseAmplitude h (-I * ((c : ℂ) + (y : ℂ) * I)) *
      Complex.exp (((c : ℂ) + (y : ℂ) * I) * (S : ℂ)) := by
  have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi0
  have hFi : Integrable (𝓕 (h.damped c)) := by
    have h1 := ((h.integrable_amplitude_line c).comp_mul_left' hpi0).const_mul (2 * Real.pi : ℂ)
    refine h1.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [h.fourier_damped]
  have hinv := (h.continuous_damped c).fourierInv_fourier_eq (h.integrable_damped c) hFi
  have hS := congrFun hinv S
  rw [fourierInv_eq_integral_exp] at hS
  have hsub : ∫ ξ : ℝ, Complex.exp ((2 * Real.pi * ξ * S : ℝ) * I) • 𝓕 (h.damped c) ξ =
      ∫ y : ℝ, pulseAmplitude h ((y : ℂ) - c * I) * Complex.exp (I * (y : ℂ) * (S : ℂ)) := by
    have hg := Measure.integral_comp_mul_left
      (fun y : ℝ => pulseAmplitude h ((y : ℂ) - c * I) * Complex.exp (I * (y : ℂ) * (S : ℂ)))
      (2 * Real.pi)
    have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
    rw [habs, Complex.real_smul] at hg
    have hrw : ∀ ξ : ℝ, Complex.exp ((2 * Real.pi * ξ * S : ℝ) * I) • 𝓕 (h.damped c) ξ =
        (2 * Real.pi : ℂ) * (pulseAmplitude h (((2 * Real.pi * ξ : ℝ) : ℂ) - c * I) *
          Complex.exp (I * ((2 * Real.pi * ξ : ℝ) : ℂ) * (S : ℂ))) := by
      intro ξ
      rw [h.fourier_damped, smul_eq_mul]
      have he : Complex.exp ((2 * Real.pi * ξ * S : ℝ) * I) =
          Complex.exp (I * ((2 * Real.pi * ξ : ℝ) : ℂ) * (S : ℂ)) := by
        congr 1
        push_cast
        ring
      rw [he]
      ring
    simp_rw [hrw]
    rw [integral_const_mul, hg]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  rw [hsub] at hS
  have hexp : h S = Complex.exp ((c : ℂ) * (S : ℂ)) * h.damped c S := by
    rw [damped, mul_left_comm, ← Complex.exp_add]
    have : (c : ℂ) * (S : ℂ) + -(c : ℂ) * (S : ℂ) = 0 := by ring
    rw [this, Complex.exp_zero, mul_one]
  rw [hexp, ← hS, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  have harg : -I * ((c : ℂ) + (y : ℂ) * I) = (y : ℂ) - c * I := by
    linear_combination (-(y : ℂ)) * I_sq
  have he : Complex.exp (((c : ℂ) + (y : ℂ) * I) * (S : ℂ)) =
      Complex.exp ((c : ℂ) * (S : ℂ)) * Complex.exp (I * (y : ℂ) * (S : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [harg, he]
  ring

end CompactPulse

end GaloisForLFunctions.BlackHoleRingdown

end
