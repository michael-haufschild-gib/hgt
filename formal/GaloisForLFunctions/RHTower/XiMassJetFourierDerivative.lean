import GaloisForLFunctions.RHTower.XiMassJetIntegrand

/-!
# Differentiating the jet Fourier transform in the height

Every frequency derivative of the jet Fourier transform is again an integral of the same shape with
one more factor of `-ix`, and the majorant of that factor is a polynomial times the strip
exponential.  Differentiation under the integral sign therefore applies at every order.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- The `j`-th frequency derivative of the `k`-th jet Fourier transform, as an integral. -/
def xiMassJetFourierDeriv (a : ℝ) (k j : ℕ) (τ : ℂ) (h : ℝ) : ℂ :=
  ∫ x : ℝ, (-(I * (x : ℂ))) ^ j * xiMassJetIntegrand a k τ h x

theorem xiMassJetFourierDeriv_zero (a : ℝ) (k : ℕ) (τ : ℂ) (h : ℝ) :
    xiMassJetFourierDeriv a k 0 τ h = ∫ x : ℝ, xiMassJetIntegrand a k τ h x := by
  rw [xiMassJetFourierDeriv]
  simp

theorem continuous_phasePow_mul_jetIntegrand {a : ℝ} (ha : 0 < a) (k j : ℕ) (τ : ℂ) (h : ℝ) :
    Continuous (fun x : ℝ => (-(I * (x : ℂ))) ^ j * xiMassJetIntegrand a k τ h x) := by
  have h1 : Continuous (fun x : ℝ => (-(I * (x : ℂ))) ^ j) := by fun_prop
  exact h1.mul (continuous_xiMassJetIntegrand ha k τ h)

theorem integrable_phasePow_mul_jetIntegrand {a : ℝ} (ha : 0 < a) (k j : ℕ) {τ : ℂ}
    (hτ : 0 < τ.re) (h : ℝ) :
    Integrable (fun x : ℝ => (-(I * (x : ℂ))) ^ j * xiMassJetIntegrand a k τ h x) := by
  refine Integrable.mono' (integrable_polyPow_abs_mul_exp a k j hτ)
    (continuous_phasePow_mul_jetIntegrand ha k j τ h).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hnn : (0 : ℝ) ≤ (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ j * Real.exp (-(τ.re * |x|)) := by
    have : (0 : ℝ) ≤ x ^ 2 + 4 * a ^ 4 := by positivity
    positivity
  have hphase : ‖(-(I * (x : ℂ))) ^ j‖ = |x| ^ j := by
    rw [norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  rw [norm_mul, hphase]
  calc |x| ^ j * ‖xiMassJetIntegrand a k τ h x‖
      ≤ |x| ^ j * ((x ^ 2 + 4 * a ^ 4) ^ k * Real.exp (-(τ.re * |x|))) :=
        mul_le_mul_of_nonneg_left (norm_xiMassJetIntegrand_le ha k hτ.le h x) (by positivity)
    _ = (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ j * Real.exp (-(τ.re * |x|)) := by ring

/-- **Differentiation under the integral in the height.** -/
theorem hasDerivAt_xiMassJetFourierDeriv {a : ℝ} (ha : 0 < a) (k j : ℕ) {τ : ℂ}
    (hτ : 0 < τ.re) (h : ℝ) :
    HasDerivAt (fun t : ℝ => xiMassJetFourierDeriv a k j τ t)
      (xiMassJetFourierDeriv a k (j + 1) τ h) h := by
  have hpoint : ∀ x : ℝ, ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => (-(I * (x : ℂ))) ^ j * xiMassJetIntegrand a k τ s x)
        ((-(I * (x : ℂ))) ^ (j + 1) * xiMassJetIntegrand a k τ t x) t := by
    intro x t
    have hz : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have hlin : HasDerivAt (fun s : ℝ => -(I * (s : ℂ) * (x : ℂ))) (-(I * (x : ℂ))) t := by
      have h1 : HasDerivAt (fun s : ℝ => I * (s : ℂ) * (x : ℂ)) (I * (x : ℂ)) t := by
        have h2 := (hz.const_mul I).mul_const ((x : ℂ))
        simpa using h2
      exact h1.neg
    have hexp := hlin.cexp
    have hconst := hexp.const_mul
      ((-(I * (x : ℂ))) ^ j * (((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) ^ k *
        xiMassAnalyticTest a τ (x : ℂ)))
    have hgoal : HasDerivAt
        (fun s : ℝ => (-(I * (x : ℂ))) ^ j * xiMassJetIntegrand a k τ s x)
        ((-(I * (x : ℂ))) ^ j * (((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) ^ k *
          xiMassAnalyticTest a τ (x : ℂ)) *
          (Complex.exp (-(I * (t : ℂ) * (x : ℂ))) * (-(I * (x : ℂ))))) t := by
      refine hconst.congr_of_eventuallyEq ?_
      refine Filter.Eventually.of_forall fun s => ?_
      simp only [xiMassJetIntegrand]
      ring
    refine hgoal.congr_deriv ?_
    simp only [xiMassJetIntegrand, pow_succ]
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := fun t : ℝ => fun x : ℝ =>
      (-(I * (x : ℂ))) ^ j * xiMassJetIntegrand a k τ t x)
    (F' := fun t : ℝ => fun x : ℝ =>
      (-(I * (x : ℂ))) ^ (j + 1) * xiMassJetIntegrand a k τ t x)
    (x₀ := h) (s := Set.univ)
    (bound := fun x : ℝ => (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ (j + 1) * Real.exp (-(τ.re * |x|)))
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      (continuous_phasePow_mul_jetIntegrand ha k j τ t).aestronglyMeasurable)
    (integrable_phasePow_mul_jetIntegrand ha k j hτ h)
    (continuous_phasePow_mul_jetIntegrand ha k (j + 1) τ h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => fun t _ => by
      have hnn : (0 : ℝ) ≤ (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ (j + 1) * Real.exp (-(τ.re * |x|)) := by
        have : (0 : ℝ) ≤ x ^ 2 + 4 * a ^ 4 := by positivity
        positivity
      have hphase : ‖(-(I * (x : ℂ))) ^ (j + 1)‖ = |x| ^ (j + 1) := by
        rw [norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs]
      rw [norm_mul, hphase]
      calc |x| ^ (j + 1) * ‖xiMassJetIntegrand a k τ t x‖
          ≤ |x| ^ (j + 1) * ((x ^ 2 + 4 * a ^ 4) ^ k * Real.exp (-(τ.re * |x|))) :=
            mul_le_mul_of_nonneg_left (norm_xiMassJetIntegrand_le ha k hτ.le t x)
              (by positivity)
        _ = (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ (j + 1) * Real.exp (-(τ.re * |x|)) := by ring)
    (integrable_polyPow_abs_mul_exp a k (j + 1) hτ)
    (Filter.Eventually.of_forall fun x => fun t _ => hpoint x t)
  exact hmain.2

/-! ## The dispersion recursion on the Fourier side -/

theorem integrable_xiMassJetIntegrand' {a : ℝ} (ha : 0 < a) (k : ℕ) {τ : ℂ} (hτ : 0 < τ.re)
    (h : ℝ) : Integrable (xiMassJetIntegrand a k τ h) := by
  have h0 := integrable_phasePow_mul_jetIntegrand ha k 0 hτ h
  simpa using h0

/-- One step of the dispersion recursion, pointwise on the real axis. -/
theorem xiMassJetIntegrand_succ (a : ℝ) (k : ℕ) (τ : ℂ) (h x : ℝ) :
    xiMassJetIntegrand a (k + 1) τ h x
      = 4 * (a : ℂ) ^ 4 * xiMassJetIntegrand a k τ h x
        - (-(I * (x : ℂ))) ^ 2 * xiMassJetIntegrand a k τ h x := by
  have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
  simp only [xiMassJetIntegrand, pow_succ]
  linear_combination ((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) ^ k *
    xiMassAnalyticTest a τ (x : ℂ) * Complex.exp (-(I * (h : ℂ) * (x : ℂ))) * (x : ℂ) ^ 2 * hI

/-- **The dispersion recursion.**  Raising the jet order multiplies by `4a⁴ − ∂_h²`. -/
theorem xiMassJetFourierDeriv_succ {a : ℝ} (ha : 0 < a) (k : ℕ) {τ : ℂ} (hτ : 0 < τ.re)
    (h : ℝ) :
    xiMassJetFourierDeriv a (k + 1) 0 τ h
      = 4 * (a : ℂ) ^ 4 * xiMassJetFourierDeriv a k 0 τ h
        - xiMassJetFourierDeriv a k 2 τ h := by
  rw [xiMassJetFourierDeriv_zero, xiMassJetFourierDeriv_zero, xiMassJetFourierDeriv]
  have hsplit : (∫ x : ℝ, xiMassJetIntegrand a (k + 1) τ h x)
      = ∫ x : ℝ, (4 * (a : ℂ) ^ 4 * xiMassJetIntegrand a k τ h x
          - (-(I * (x : ℂ))) ^ 2 * xiMassJetIntegrand a k τ h x) :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => xiMassJetIntegrand_succ a k τ h x)
  rw [hsplit, MeasureTheory.integral_sub
    ((integrable_xiMassJetIntegrand' ha k hτ h).const_mul _)
    (integrable_phasePow_mul_jetIntegrand ha k 2 hτ h),
    MeasureTheory.integral_const_mul]

end

end RHTower
