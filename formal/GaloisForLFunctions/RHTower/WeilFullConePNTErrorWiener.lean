import GaloisForLFunctions.RHTower.WeilFullConeSquareRootPNT
import GaloisForLFunctions.HTGeometry.CharFunWienerLemma
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# The prime number theorem error of a Weil-positive system detects its atoms

Let `lam` be full-cone Weil-positive with boundary measure `μ_lam`, let `K = f ⋆ f̃`
(`f` `C²` with compact support), and let `ν_f = |f̂|² μ_lam` be the Bochner measure of `f`.

**Theorem** (`tendsto_mean_normSq_weilFullFunctional_transl`).  The mean square of the translated
Weil functional tends to the atomic energy of `ν_f`:

`(1/2Y) ∫_{−Y}^{Y} |W_lam(K_y)|² dy → (ν_f ⊗ ν_f)(diagonal) = Σ_a |f̂(a)|⁴ μ_lam({a})²`.

**Theorem** (`tendsto_pntError_add_weilFullFunctional`).  The normalized error of the smoothed
prime number theorem,
`E(y) = Σ_{n≥2} lam(n) n^{−1/2} K(log n − y) − e^{y/2} K̂(−i/2)`,
satisfies `E(y) + W_lam(K_y) → 0` as `y → ∞`.

So the `√x`-normalized PNT error of every producer has mean square tending to the atomic energy
of `|f̂|² μ_lam`.  It oscillates at full size iff `μ_lam` has atoms where `f̂ ≠ 0`; for continuous
`μ_lam` it decays in mean square.

**Proof.**  `W_lam(K_y) = charFun ν_f (y)` (Bochner), and Wiener's lemma
(`HTGeometry.tendsto_mean_normSq_charFun`).  By the explicit formula on `K_y`
(`primeSum_transl_sub_main_eq`), `E(y) + W_lam(K_y) = e^{−y/2}K̂(i/2) + arch(K_y)`, where the
first term decays and the second tends to `0` by Riemann–Lebesgue.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-- **Wiener law for the translated Weil functional.** -/
theorem tendsto_mean_normSq_weilFullFunctional_transl {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ν = (boundaryMeasure hW).withDensity (fun r => (specDensity f r : ENNReal)) ∧
      Tendsto (fun Y : ℝ => (1 / (2 * Y)) *
          ∫ y in (-Y)..Y, ‖weilFullFunctional lam (transl y (EF.weilTest f f))‖ ^ 2) atTop
        (𝓝 ((ν.prod ν).real {p : ℝ × ℝ | p.1 = p.2})) := by
  obtain ⟨ν, hν, hνK⟩ := exists_spectralMeasure hW hf hfc
  refine ⟨ν, hν, eq_withDensity_boundaryMeasure hW hf hfc hνK, ?_⟩
  have h := GaloisForLFunctions.HTGeometry.tendsto_mean_normSq_charFun ν
  refine h.congr fun Y => ?_
  congr 2
  funext y
  rw [hνK y, spectralKernel]

/-- The archimedean part of a translated admissible test tends to `0` (Riemann–Lebesgue). -/
theorem tendsto_archPart_transl {K : ℝ → ℂ} :
    Tendsto (fun y : ℝ => archPart (transl y K)) atTop (𝓝 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact
    (fun r : ℝ => paperFT K r * (EF.gammaBracket r : ℂ))
  have hmap : Tendsto (fun y : ℝ => -(y / (2 * π))) atTop (cocompact ℝ) := by
    refine Tendsto.mono_right ?_ atBot_le_cocompact
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by positivity))
  have h := (hRL.comp hmap).const_mul (1 / (2 * π) : ℂ)
  rw [mul_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_def, archPart]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [paperFT_transl, Circle.smul_def, Real.fourierChar_apply]
  have : (2 * π * -(r * -(y / (2 * π))) : ℝ) = r * y := by field_simp
  rw [smul_eq_mul, show ((2 * π * -(r * -(y / (2 * π))) : ℝ) : ℂ) * I = I * (r : ℂ) * y by
    rw [this]; push_cast; ring]
  ring

/-- **The PNT error is `−W_lam(K_y) + o(1)`.** -/
theorem tendsto_pntError_add_weilFullFunctional {lam : ℕ → ℝ} {K : ℝ → ℂ} {R : ℝ}
    (hR : ∀ u, K u ≠ 0 → |u| ≤ R) :
    Tendsto (fun y : ℝ =>
      ((∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * K (Real.log n - y)) -
        ((Real.exp (y / 2) : ℝ) : ℂ) * paperFT K (-I / 2)) +
        weilFullFunctional lam (transl y K)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun y : ℝ => ((Real.exp (-(y / 2)) : ℝ) : ℂ) * paperFT K (I / 2)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Real.exp (-(y / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.atTop_div_const (by norm_num)))
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
    rw [Complex.ofReal_zero] at h2
    simpa using h2.mul_const (paperFT K (I / 2))
  have h := hexp.add (tendsto_archPart_transl (K := K))
  rw [add_zero] at h
  refine h.congr' ((eventually_gt_atTop R).mono fun y hy => ?_)
  dsimp only
  linear_combination -(primeSum_transl_sub_main_eq lam hR hy)

end RHTower.WeilSpectral

end
