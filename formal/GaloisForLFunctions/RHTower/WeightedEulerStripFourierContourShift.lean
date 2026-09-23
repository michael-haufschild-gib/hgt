import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Contour shift and high-frequency vanishing of the strip Fourier transform

For an entire `g` with the two-ray
bound `‖g z‖ ≤ K e^{-ε|Re z| + τ|Im z|}`, the Fourier transform at a real
frequency can be evaluated on any horizontal line (rectangle contour shift;
the vertical sides vanish exponentially in the width), and shifting the line
to `∓∞` kills every frequency beyond the type:

`stripFourier g w = 0`  for real `|w| > τ`.

Together with `analyticOnNhd_stripFourier` and the identity theorem this
forces `stripFourier g ≡ 0` on the strip, hence `g ≡ 0` by Fourier inversion —
assembled in the follow-up module.  Everything is unconditional.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set Filter Topology

variable {g : ℂ → ℂ} {K ε τ : ℝ}

/-- The horizontally shifted strip Fourier transform. -/
def stripFourierShifted (g : ℂ → ℂ) (w y : ℝ) : ℂ :=
  ∫ x : ℝ, g ((x : ℂ) + (y : ℂ) * I) *
    Complex.exp (-(I * (w : ℂ) * ((x : ℂ) + (y : ℂ) * I)))

theorem stripFourierShifted_zero (g : ℂ → ℂ) (w : ℝ) :
    stripFourierShifted g w 0 = stripFourier g (w : ℂ) := by
  unfold stripFourierShifted stripFourier
  simp

/-- Real part of the shifted Fourier phase. -/
theorem re_shifted_phase (w x y : ℝ) :
    (-(I * (w : ℂ) * ((x : ℂ) + (y : ℂ) * I))).re = w * y := by
  simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- Points of the closed segment `uIoc 0 y` are no larger than `|y|`. -/
theorem abs_le_abs_of_mem_uIoc {t y : ℝ} (ht : t ∈ Set.uIoc 0 y) :
    |t| ≤ |y| := by
  rcases Set.mem_uIoc.1 ht with h | h
  · rw [abs_of_pos h.1]
    exact le_trans h.2 (le_abs_self y)
  · rw [abs_of_nonpos h.2]
    calc -t ≤ -y := neg_le_neg h.1.le
      _ ≤ |y| := neg_le_abs y

/-- Pointwise bound for the shifted integrand. -/
theorem norm_shifted_integrand_le
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    (w x y : ℝ) :
    ‖g ((x : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(I * (w : ℂ) * ((x : ℂ) + (y : ℂ) * I)))‖
      ≤ (K * Real.exp (τ * |y| + w * y)) * Real.exp (-(ε * |x|)) := by
  have hz1 : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have hz2 : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have hb := hbound ((x : ℂ) + (y : ℂ) * I)
  rw [hz1, hz2] at hb
  rw [norm_mul, Complex.norm_exp, re_shifted_phase]
  calc ‖g ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (w * y)
      ≤ (K * Real.exp (-(ε * |x|) + τ * |y|)) * Real.exp (w * y) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = (K * Real.exp (τ * |y| + w * y)) * Real.exp (-(ε * |x|)) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- The shifted kernel is integrable at every height. -/
theorem integrable_shifted_kernel (hgc : Continuous g)
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    (hε : 0 < ε) (w y : ℝ) :
    Integrable fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I) *
      Complex.exp (-(I * (w : ℂ) * ((x : ℂ) + (y : ℂ) * I))) := by
  apply Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hε).const_mul (K * Real.exp (τ * |y| + w * y)))
  · apply Continuous.aestronglyMeasurable
    exact (hgc.comp (by fun_prop)).mul (Complex.continuous_exp.comp (by fun_prop))
  · exact ae_of_all _ fun x => norm_shifted_integrand_le hbound w x y

/-- Norm bound for the shifted transform. -/
theorem norm_stripFourierShifted_le
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    (hε : 0 < ε) (w y : ℝ) :
    ‖stripFourierShifted g w y‖
      ≤ (K * Real.exp (τ * |y| + w * y)) * ∫ x : ℝ, Real.exp (-(ε * |x|)) := by
  unfold stripFourierShifted
  rw [← MeasureTheory.integral_const_mul]
  apply norm_integral_le_of_norm_le
  · exact (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hε).const_mul _
  · exact ae_of_all _ fun x => norm_shifted_integrand_le hbound w x y

/-- **Contour shift**: at a real frequency the strip Fourier transform equals
its evaluation on any horizontal line. -/
theorem stripFourierShifted_eq (hg : Differentiable ℂ g)
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    (hε : 0 < ε) (hτ : 0 ≤ τ) (w y : ℝ) :
    stripFourierShifted g w y = stripFourier g (w : ℂ) := by
  have hgc : Continuous g := hg.continuous
  have hK0 : 0 ≤ K := le_trans (norm_nonneg (g 0)) (by simpa using hbound 0)
  set F : ℂ → ℂ := fun z => g z * Complex.exp (-(I * (w : ℂ) * z)) with hF
  have hFdiff : Differentiable ℂ F :=
    hg.mul (Complex.differentiable_exp.comp
      ((differentiable_id.const_mul (I * (w : ℂ))).neg))
  -- the rectangle identity at half-width T
  have hrect : ∀ T : ℝ,
      (∫ x : ℝ in (-T)..T, F (x : ℂ))
        - (∫ x : ℝ in (-T)..T, F ((x : ℂ) + (y : ℂ) * I))
        + I • (∫ t : ℝ in (0:ℝ)..y, F ((T : ℂ) + (t : ℂ) * I))
        - I • (∫ t : ℝ in (0:ℝ)..y, F (-(T : ℂ) + (t : ℂ) * I)) = 0 := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      ((-T : ℝ) : ℂ) (((T : ℝ) : ℂ) + (y : ℂ) * I)
      hFdiff.differentiableOn
    simpa using h
  -- the two horizontal limits
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in (-T)..T, F (x : ℂ)) atTop
      (𝓝 (stripFourier g (w : ℂ))) := by
    have hint : Integrable fun x : ℝ => F (x : ℂ) := by
      have h0 := integrable_shifted_kernel hgc hbound hε w 0
      apply h0.congr
      refine ae_of_all _ fun x => ?_
      simp [hF]
    have h := MeasureTheory.intervalIntegral_tendsto_integral hint
      Filter.tendsto_neg_atTop_atBot tendsto_id
    have hval : (∫ x : ℝ, F (x : ℂ)) = stripFourier g (w : ℂ) := by
      unfold stripFourier
      rfl
    rwa [hval] at h
  have htop : Tendsto (fun T : ℝ =>
      ∫ x : ℝ in (-T)..T, F ((x : ℂ) + (y : ℂ) * I)) atTop
      (𝓝 (stripFourierShifted g w y)) := by
    have hint : Integrable fun x : ℝ => F ((x : ℂ) + (y : ℂ) * I) :=
      integrable_shifted_kernel hgc hbound hε w y
    have h := MeasureTheory.intervalIntegral_tendsto_integral hint
      Filter.tendsto_neg_atTop_atBot tendsto_id
    have hval : (∫ x : ℝ, F ((x : ℂ) + (y : ℂ) * I))
        = stripFourierShifted g w y := by
      unfold stripFourierShifted
      rfl
    rwa [hval] at h
  -- generic pointwise bound on vertical segments
  have hFpt : ∀ a t : ℝ, |t| ≤ |y| →
      ‖F ((a : ℂ) + (t : ℂ) * I)‖
        ≤ K * Real.exp ((τ + |w|) * |y|) * Real.exp (-(ε * |a|)) := by
    intro a t htabs
    have h := norm_shifted_integrand_le hbound w a t
    rw [hF]
    refine le_trans h ?_
    rw [mul_assoc K, ← Real.exp_add, mul_assoc K, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hK0
    apply Real.exp_le_exp.2
    have h1 : τ * |t| ≤ τ * |y| := mul_le_mul_of_nonneg_left htabs hτ
    have h2 : w * t ≤ |w| * |y| := by
      calc w * t ≤ |w * t| := le_abs_self _
        _ = |w| * |t| := abs_mul _ _
        _ ≤ |w| * |y| := mul_le_mul_of_nonneg_left htabs (abs_nonneg w)
    nlinarith [abs_nonneg a]
  -- decay of the width-parameterized exponential
  have hexp0 : Tendsto (fun T : ℝ => Real.exp (-(ε * T))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact Filter.tendsto_neg_atTop_atBot.comp
      (Filter.Tendsto.const_mul_atTop hε tendsto_id)
  -- both vertical sides vanish
  have hg0 : Tendsto (fun T : ℝ => K * Real.exp ((τ + |w|) * |y|) * |y| *
      Real.exp (-(ε * T))) atTop (𝓝 0) := by
    simpa using hexp0.const_mul (K * Real.exp ((τ + |w|) * |y|) * |y|)
  have hsideR : Tendsto (fun T : ℝ =>
      ∫ t : ℝ in (0:ℝ)..y, F ((T : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hg0
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have hbd : ∀ t ∈ Set.uIoc (0:ℝ) y,
        ‖F ((T : ℂ) + (t : ℂ) * I)‖
          ≤ K * Real.exp ((τ + |w|) * |y|) * Real.exp (-(ε * T)) := by
      intro t ht
      have := hFpt T t (abs_le_abs_of_mem_uIoc ht)
      rwa [abs_of_nonneg hT] at this
    calc ‖∫ t : ℝ in (0:ℝ)..y, F ((T : ℂ) + (t : ℂ) * I)‖
        ≤ K * Real.exp ((τ + |w|) * |y|) * Real.exp (-(ε * T)) * |y - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ = K * Real.exp ((τ + |w|) * |y|) * |y| * Real.exp (-(ε * T)) := by
          rw [sub_zero]
          ring
  have hsideL : Tendsto (fun T : ℝ =>
      ∫ t : ℝ in (0:ℝ)..y, F (-(T : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hg0
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have hbd : ∀ t ∈ Set.uIoc (0:ℝ) y,
        ‖F (-(T : ℂ) + (t : ℂ) * I)‖
          ≤ K * Real.exp ((τ + |w|) * |y|) * Real.exp (-(ε * T)) := by
      intro t ht
      have h := hFpt (-T) t (abs_le_abs_of_mem_uIoc ht)
      rw [abs_neg, abs_of_nonneg hT] at h
      rwa [show ((-T : ℝ) : ℂ) = -(T : ℂ) from by push_cast; ring] at h
    calc ‖∫ t : ℝ in (0:ℝ)..y, F (-(T : ℂ) + (t : ℂ) * I)‖
        ≤ K * Real.exp ((τ + |w|) * |y|) * Real.exp (-(ε * T)) * |y - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ = K * Real.exp ((τ + |w|) * |y|) * |y| * Real.exp (-(ε * T)) := by
          rw [sub_zero]
          ring
  -- pass to the limit in the rectangle identity
  have hcomb := ((hbot.sub htop).add (hsideR.const_smul I)).sub
    (hsideL.const_smul I)
  rw [funext hrect] at hcomb
  have hval := tendsto_nhds_unique hcomb tendsto_const_nhds
  have hfin : stripFourier g (w : ℂ) - stripFourierShifted g w y = 0 := by
    simpa using hval
  exact (sub_eq_zero.1 hfin).symm

/-- **High-frequency vanishing** (Paley–Wiener half): a two-ray-decaying
entire function has vanishing strip Fourier transform at every real frequency
beyond the exponential type. -/
theorem stripFourier_eq_zero_of_abs_gt (hg : Differentiable ℂ g)
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    (hε : 0 < ε) (hτ : 0 ≤ τ) {w : ℝ} (hw : τ < |w|) :
    stripFourier g (w : ℂ) = 0 := by
  have hgc : Continuous g := hg.continuous
  have hK0 : 0 ≤ K := le_trans (norm_nonneg (g 0)) (by simpa using hbound 0)
  set Cε : ℝ := ∫ x : ℝ, Real.exp (-(ε * |x|)) with hCε
  have hCε0 : 0 ≤ Cε := integral_nonneg fun x => Real.exp_nonneg _
  -- choose the shift direction according to the sign of `w`
  have hkey : ∀ s : ℝ, ‖stripFourier g (w : ℂ)‖
      ≤ K * Real.exp (τ * |s| + w * s) * Cε := by
    intro s
    rw [← stripFourierShifted_eq hg hbound hε hτ w s]
    exact norm_stripFourierShifted_le hbound hε w s
  have hlim : Tendsto (fun n : ℝ =>
      K * Real.exp (-((|w| - τ) * n)) * Cε) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℝ => Real.exp (-((|w| - τ) * n))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact Filter.tendsto_neg_atTop_atBot.comp
        (Filter.Tendsto.const_mul_atTop (by linarith) tendsto_id)
    have := (h1.const_mul K).mul_const Cε
    simpa using this
  have hnorm_le : ∀ n : ℝ, 0 ≤ n → ‖stripFourier g (w : ℂ)‖
      ≤ K * Real.exp (-((|w| - τ) * n)) * Cε := by
    intro n hn
    rcases le_or_gt 0 w with hw0 | hw0
    · -- `w = |w|`, shift down: `s = -n`
      have h := hkey (-n)
      rw [show τ * |(-n)| + w * (-n) = -((w - τ) * n) from by
        rw [abs_neg, abs_of_nonneg hn]; ring] at h
      rw [abs_of_nonneg hw0]
      exact h
    · -- `w = -|w|`, shift up: `s = n`
      have h := hkey n
      rw [show τ * |n| + w * n = -((-w - τ) * n) from by
        rw [abs_of_nonneg hn]; ring] at h
      rw [abs_of_neg hw0]
      exact h
  have hle0 : ‖stripFourier g (w : ℂ)‖ ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0:ℝ)] with n hn
    exact hnorm_le n hn
  exact norm_le_zero_iff.1 hle0

end RHTower
