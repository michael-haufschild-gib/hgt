import Mathlib

/-!
# Plancherel for Mellin transforms of smooth compactly supported functions

For `f : ℝ → ℂ` smooth with support in `[a, b]`, `0 < a`, and real `σ`,

`∫_ℝ |𝓜f(σ + it)|² dt = 2π ∫_ℝ |e^{−σv} f(e^{−v})|² dv`

(`integral_norm_sq_mellin_eq`): on a vertical line the Mellin transform is the Fourier transform of
`v ↦ e^{−σv} f(e^{−v})` at `t/2π` (`mellin_eq_fourier`), this function is a Schwartz function
(smooth with compact support), and the Fourier transform is an `L²` isometry on Schwartz functions
(`SchwartzMap.integral_norm_sq_fourier`).  In particular, if `|f| ≤ B` and `σ ≥ 0`, then
`∫ |𝓜f(σ + it)|² dt ≤ 2π B² b^{2σ} log(b/a)` (`integral_norm_sq_mellin_le`).
-/

open Real Complex Set MeasureTheory Function
open scoped FourierTransform ContDiff SchwartzMap

noncomputable section

namespace GaloisForLFunctions.HTGeometry.MellinPlancherel

/-- The function whose Fourier transform is the Mellin transform on `Re s = σ`. -/
def logPull (f : ℝ → ℂ) (σ : ℝ) (v : ℝ) : ℂ := Real.exp (-σ * v) • f (Real.exp (-v))

theorem contDiff_logPull {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (σ : ℝ) :
    ContDiff ℝ ∞ (logPull f σ) := by
  unfold logPull
  have h1 : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ * v)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have h2 : ContDiff ℝ ∞ (fun v : ℝ => f (Real.exp (-v))) :=
    hf.comp (Real.contDiff_exp.comp contDiff_neg)
  exact h1.smul h2

theorem logPull_eq_zero {f : ℝ → ℂ} {a b : ℝ} (ha : 0 < a) (hsupp : support f ⊆ Icc a b) (σ : ℝ)
    {v : ℝ} (hv : v ∉ Icc (-Real.log b) (-Real.log a)) : logPull f σ v = 0 := by
  unfold logPull
  have : f (Real.exp (-v)) = 0 := by
    by_contra h
    have hm := hsupp h
    apply hv
    have hb : 0 < b := lt_of_lt_of_le ha (hm.1.trans hm.2)
    constructor
    · have := Real.log_le_log (Real.exp_pos _) hm.2
      rw [Real.log_exp] at this; linarith
    · have := Real.log_le_log ha hm.1
      rw [Real.log_exp] at this; linarith
  rw [this, smul_zero]

theorem hasCompactSupport_logPull {f : ℝ → ℂ} {a b : ℝ} (ha : 0 < a)
    (hsupp : support f ⊆ Icc a b) (σ : ℝ) : HasCompactSupport (logPull f σ) :=
  HasCompactSupport.intro (isCompact_Icc (a := -Real.log b) (b := -Real.log a))
    fun _ hv => logPull_eq_zero ha hsupp σ hv

/-- **Mellin–Plancherel.** -/
theorem integral_norm_sq_mellin_eq {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {a b : ℝ} (ha : 0 < a)
    (hsupp : support f ⊆ Icc a b) (σ : ℝ) :
    ∫ t : ℝ, ‖mellin f ((σ : ℂ) + t * I)‖ ^ 2 = 2 * π * ∫ v : ℝ, ‖logPull f σ v‖ ^ 2 := by
  set G : 𝓢(ℝ, ℂ) := (hasCompactSupport_logPull ha hsupp σ).toSchwartzMap (contDiff_logPull hf σ)
  have hG : ∀ v, G v = logPull f σ v := fun v => rfl
  have hmel : ∀ t : ℝ, mellin f ((σ : ℂ) + t * I) = 𝓕 (G : ℝ → ℂ) (t / (2 * π)) := by
    intro t
    rw [mellin_eq_fourier]
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have him : ((σ : ℂ) + t * I).im = t := by simp
    rw [hre, him]
    congr 1
  simp_rw [hmel]
  have hcv := Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 (G : ℝ → ℂ) ξ‖ ^ 2) (2 * π)
  rw [hcv, abs_of_pos (by positivity), smul_eq_mul]
  have hpl := SchwartzMap.integral_norm_sq_fourier G
  rw [SchwartzMap.fourier_coe] at hpl
  rw [hpl]
  rfl

/-- The `L²` bound on a vertical line. -/
theorem integral_norm_sq_mellin_le {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hsupp : support f ⊆ Icc a b) {σ : ℝ} (hσ : 0 ≤ σ) {B : ℝ}
    (hB : ∀ u, ‖f u‖ ≤ B) :
    ∫ t : ℝ, ‖mellin f ((σ : ℂ) + t * I)‖ ^ 2 ≤
      2 * π * (B ^ 2 * b ^ (2 * σ) * (Real.log b - Real.log a)) := by
  rw [integral_norm_sq_mellin_eq hf ha hsupp σ]
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set K : Set ℝ := Icc (-Real.log b) (-Real.log a)
  have hbound : ∀ v, ‖logPull f σ v‖ ^ 2 ≤ K.indicator (fun _ => B ^ 2 * b ^ (2 * σ)) v := by
    intro v
    by_cases hv : v ∈ K
    · rw [Set.indicator_of_mem hv]
      unfold logPull
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
      have h1 : Real.exp (-σ * v) ^ 2 ≤ b ^ (2 * σ) := by
        rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hb]
        apply Real.exp_le_exp.mpr
        have : -v ≤ Real.log b := by linarith [hv.1]
        push_cast; nlinarith
      have h2 : ‖f (Real.exp (-v))‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hB _) 2
      calc Real.exp (-σ * v) ^ 2 * ‖f (Real.exp (-v))‖ ^ 2 ≤ b ^ (2 * σ) * B ^ 2 :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = B ^ 2 * b ^ (2 * σ) := by ring
    · rw [Set.indicator_of_notMem hv, logPull_eq_zero ha hsupp σ hv]; simp
  have hint : Integrable (K.indicator (fun _ : ℝ => B ^ 2 * b ^ (2 * σ))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∫ v, ‖logPull f σ v‖ ^ 2 ≤ ∫ v, K.indicator (fun _ => B ^ 2 * b ^ (2 * σ)) v :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity) hint
          (Filter.Eventually.of_forall hbound)
    _ = B ^ 2 * b ^ (2 * σ) * (Real.log b - Real.log a) := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Real.volume_real_Icc]
        rw [max_eq_left (by linarith [Real.log_le_log ha hab])]
        ring

end GaloisForLFunctions.HTGeometry.MellinPlancherel
