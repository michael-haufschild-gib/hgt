import GaloisForLFunctions.RHTower.CCM.CCMParityFreeOddGroundFourier
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-!
# Compact Fourier zero transfer from fixed-support mean-square convergence

This file supplies the analytic limit step needed after the finite-dimensional
CCM odd-ground theorem.  On a fixed compact interval, mean-square convergence
of continuous sources implies locally uniform convergence of their entire
compact Fourier transforms.  Consequently, a nonzero limit of transforms whose
zeros all lie on the real axis again has only real zeros.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Interval

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Fixed-support mean-square control of the compact Fourier transform. -/
theorem norm_compactFourier_sub_le_meanSquare
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) (z : ℂ) :
    ‖compactFourier f a b z - compactFourier g a b z‖ ≤
      Real.exp (max |a| |b| * |z.im|) * Real.sqrt (b - a) *
        Real.sqrt (∫ x in a..b, ‖f x - g x‖ ^ (2 : ℕ)) := by
  let D : ℝ → ℂ := fun x => f x - g x
  have hD : Continuous D := hf.sub hg
  have hdiff :
      compactFourier f a b z - compactFourier g a b z =
        ∫ x in a..b, D x * Complex.exp (Complex.I * (z * (x : ℂ))) := by
    have hfi : IntervalIntegrable
        (fun x : ℝ => f x * Complex.exp (Complex.I * (z * (x : ℂ)))) volume a b :=
      (continuous_compactFourier_integrand hf z).intervalIntegrable a b
    have hgi : IntervalIntegrable
        (fun x : ℝ => g x * Complex.exp (Complex.I * (z * (x : ℂ)))) volume a b :=
      (continuous_compactFourier_integrand hg z).intervalIntegrable a b
    rw [compactFourier, compactFourier, ← intervalIntegral.integral_sub hfi hgi]
    apply intervalIntegral.integral_congr
    intro x _
    simp [D]
    ring
  rw [hdiff]
  have hpoint : ∀ x ∈ Set.Ioc a b,
      ‖D x * Complex.exp (Complex.I * (z * (x : ℂ)))‖ ≤
        ‖D x‖ * Real.exp (max |a| |b| * |z.im|) := by
    intro x hx
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have hxu : x ∈ Set.uIoc a b := by rwa [Set.uIoc_of_le hab]
    have hxR : |x| ≤ max |a| |b| := abs_le_max_abs_of_mem_uIoc hxu
    have hre : (Complex.I * (z * (x : ℂ))).re = -(z.im * x) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    calc
      -(z.im * x) ≤ |z.im * x| := neg_le_abs _
      _ = |z.im| * |x| := abs_mul _ _
      _ ≤ |z.im| * max |a| |b| :=
        mul_le_mul_of_nonneg_left hxR (abs_nonneg _)
      _ = max |a| |b| * |z.im| := by ring
  have hint : IntervalIntegrable
      (fun x => ‖D x‖ * Real.exp (max |a| |b| * |z.im|)) volume a b :=
    (hD.norm.mul continuous_const).intervalIntegrable a b
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun x hx => hpoint x hx) hint
  have hfirst := integral_norm_le_sqrt_length_mul_sqrt_meanSquare hD hab
  calc
    ‖∫ x in a..b, D x * Complex.exp (Complex.I * (z * (x : ℂ)))‖ ≤
        ∫ x in a..b, ‖D x‖ * Real.exp (max |a| |b| * |z.im|) := hnorm
    _ = Real.exp (max |a| |b| * |z.im|) * (∫ x in a..b, ‖D x‖) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ ≤ Real.exp (max |a| |b| * |z.im|) *
          (Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, ‖D x‖ ^ (2 : ℕ))) := by
      exact mul_le_mul_of_nonneg_left hfirst (Real.exp_pos _).le
    _ = Real.exp (max |a| |b| * |z.im|) * Real.sqrt (b - a) *
          Real.sqrt (∫ x in a..b, ‖f x - g x‖ ^ (2 : ℕ)) := by
      simp [D, mul_assoc]

/-- Mean-square convergence on one fixed interval implies locally uniform
convergence of the associated compact Fourier transforms on `ℂ`. -/
theorem compactFourier_tendstoLocallyUniformly_of_meanSquare
    (fseq : ℕ → ℝ → ℂ) (f : ℝ → ℂ)
    (hfseq : ∀ n, Continuous (fseq n)) (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b)
    (hmean : Tendsto
      (fun n => ∫ x in a..b, ‖fseq n x - f x‖ ^ (2 : ℕ)) atTop (nhds 0)) :
    TendstoLocallyUniformly
      (fun n z => compactFourier (fseq n) a b z)
      (compactFourier f a b) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro eps heps z₀
  refine ⟨Metric.ball z₀ 1, Metric.ball_mem_nhds z₀ one_pos, ?_⟩
  let q : ℕ → ℝ := fun n => ∫ x in a..b, ‖fseq n x - f x‖ ^ (2 : ℕ)
  have hq : Tendsto q atTop (nhds 0) := hmean
  have hsqrt : Tendsto (fun n => Real.sqrt (q n)) atTop (nhds 0) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hq using 1 <;>
      simp [Function.comp_def]
  let R : ℝ := max |a| |b|
  let B : ℝ := |z₀.im| + 1
  let C : ℝ := Real.exp (R * B) * Real.sqrt (b - a)
  have hscaled : Tendsto (fun n => C * Real.sqrt (q n)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hsqrt
  have hsmall : ∀ᶠ n in atTop, C * Real.sqrt (q n) < eps :=
    hscaled.eventually (Iio_mem_nhds heps)
  filter_upwards [hsmall] with n hn
  intro z hz
  have hdist : ‖z - z₀‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have himDiff : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
    have := Complex.abs_im_le_norm (z - z₀)
    simpa using this
  have him : |z.im| ≤ B := by
    calc
      |z.im| = |(z.im - z₀.im) + z₀.im| := by ring_nf
      _ ≤ |z.im - z₀.im| + |z₀.im| := abs_add_le _ _
      _ ≤ ‖z - z₀‖ + |z₀.im| := add_le_add himDiff le_rfl
      _ ≤ B := by dsimp [B]; linarith
  have hR : 0 ≤ R := le_trans (abs_nonneg a) (le_max_left _ _)
  have hbound := norm_compactFourier_sub_le_meanSquare (hfseq n) hf hab z
  calc
    dist (compactFourier f a b z) (compactFourier (fseq n) a b z) =
        ‖compactFourier (fseq n) a b z - compactFourier f a b z‖ := by
          rw [dist_eq_norm, norm_sub_rev]
    _ ≤ Real.exp (R * |z.im|) * Real.sqrt (b - a) * Real.sqrt (q n) := by
      simpa [R, q] using hbound
    _ ≤ Real.exp (R * B) * Real.sqrt (b - a) * Real.sqrt (q n) := by
      have hexp : Real.exp (R * |z.im|) ≤ Real.exp (R * B) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left him hR)
      have hsqrtLen : 0 ≤ Real.sqrt (b - a) := Real.sqrt_nonneg _
      have hsqrtQ : 0 ≤ Real.sqrt (q n) := Real.sqrt_nonneg _
      gcongr
    _ = C * Real.sqrt (q n) := by simp [C, mul_assoc]
    _ < eps := hn

/-- Closed-real-zero transfer for a nonzero compact Fourier limit obtained by
fixed-support mean-square approximation. -/
theorem compactFourier_limit_zero_im_eq_zero_of_meanSquare
    (fseq : ℕ → ℝ → ℂ) (f : ℝ → ℂ)
    (hfseq : ∀ n, Continuous (fseq n)) (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b)
    (hmean : Tendsto
      (fun n => ∫ x in a..b, ‖fseq n x - f x‖ ^ (2 : ℕ)) atTop (nhds 0))
    (hreal : ∀ n z, compactFourier (fseq n) a b z = 0 → z.im = 0)
    {w z : ℂ} (hw : compactFourier f a b w ≠ 0)
    (hz : compactFourier f a b z = 0) :
    z.im = 0 := by
  have hconv := compactFourier_tendstoLocallyUniformly_of_meanSquare
    fseq f hfseq hf hab hmean
  have hF : AnalyticOnNhd ℂ (compactFourier f a b) Set.univ :=
    (differentiable_compactFourier hf a b).differentiableOn.analyticOnNhd isOpen_univ
  have hFn : ∀ᶠ n in atTop, Differentiable ℂ (compactFourier (fseq n) a b) :=
    Filter.Eventually.of_forall fun n => differentiable_compactFourier (hfseq n) a b
  have hzero : ∀ᶠ n in atTop, ∀ u, compactFourier (fseq n) a b u = 0 →
      u ∈ {q : ℂ | q.im = 0} := by
    exact Filter.Eventually.of_forall fun n u hu => hreal n u hu
  exact zero_mem_closed_of_tendstoLocallyUniformly hconv hF hFn
    (isClosed_eq Complex.continuous_im continuous_const) hzero hw hz

end

end RHTower
