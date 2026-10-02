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

/-- Cesàro means of a continuous function tending to `0` tend to `0`. -/
theorem tendsto_mean_of_tendsto_zero {g : ℝ → ℂ} (hg : Continuous g)
    (hlim : Tendsto g atTop (𝓝 0)) (R₀ : ℝ) :
    Tendsto (fun Y : ℝ => (1 / Y : ℂ) * ∫ y in R₀..Y, g y) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (by positivity)
  set M' := max M (max R₀ 0) with hM'
  have hM'0 : 0 ≤ M' := le_trans (le_max_right R₀ 0) (le_max_right _ _)
  set A : ℝ := ‖∫ y in R₀..M', g y‖ with hA
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * A / ε + M' + 1)
  refine ⟨max N 1, fun Y hY => ?_⟩
  have hY1 : (1 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  have hYN : (N : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hY0 : 0 < Y := by linarith
  have hA0' : 0 ≤ 2 * A / ε := div_nonneg (by rw [hA]; positivity) hε.le
  have hYM : M' ≤ Y := by linarith
  rw [dist_zero_right, intervalIntegral.integral_add_adjacent_intervals
    ((hg.intervalIntegrable R₀ M')) (hg.intervalIntegrable M' Y) |>.symm, mul_add]
  have h1 : ‖(1 / Y : ℂ) * ∫ y in R₀..M', g y‖ ≤ A / Y := by
    rw [norm_mul, show ‖(1 / Y : ℂ)‖ = 1 / Y by
      rw [show (1 / Y : ℂ) = ((1 / Y : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)], hA]
    rw [one_div_mul_eq_div]
  have h2 : ‖(1 / Y : ℂ) * ∫ y in M'..Y, g y‖ ≤ ε / 2 := by
    rw [norm_mul, show ‖(1 / Y : ℂ)‖ = 1 / Y by
      rw [show (1 / Y : ℂ) = ((1 / Y : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]]
    have hb : ‖∫ y in M'..Y, g y‖ ≤ ε / 2 * |Y - M'| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => by
        rw [uIoc_of_le hYM] at hy
        have := hM y (le_trans (le_max_left _ _) hy.1.le)
        rw [dist_zero_right] at this
        exact this.le
    rw [abs_of_nonneg (by linarith)] at hb
    calc 1 / Y * ‖∫ y in M'..Y, g y‖ ≤ 1 / Y * (ε / 2 * (Y - M')) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ ε / 2 := by
          rw [one_div_mul_eq_div, div_le_iff₀ hY0]
          nlinarith
  have hA0 : 0 ≤ A := norm_nonneg _
  have h3 : A / Y < ε / 2 := by
    rw [div_lt_iff₀ hY0]
    have : 2 * A / ε < Y := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  calc ‖(1 / Y : ℂ) * (∫ y in R₀..M', g y) + (1 / Y : ℂ) * ∫ y in M'..Y, g y‖
      ≤ ‖(1 / Y : ℂ) * ∫ y in R₀..M', g y‖ + ‖(1 / Y : ℂ) * ∫ y in M'..Y, g y‖ := norm_add_le _ _
    _ < ε := by linarith


/-- **Bohr spectrum of the PNT error.**  For a full-cone producer and every large starting point
`R₀`, the Cesàro mean at frequency `a` of the normalized PNT error,
`(1/Y)∫_{R₀}^{Y} (Σ lam(n)n^{−1/2}K(log n − y) − e^{y/2}K̂(−i/2)) e^{−iay} dy`,
tends to `−ν_f({a}) = −|f̂(a)|² μ_lam({a})`.  The Bohr spectrum of the error is the atomic part of
`|f̂|² μ_lam`. -/
theorem tendsto_mean_pntError_mul_exp {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (a : ℝ) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ν = (boundaryMeasure hW).withDensity (fun r => (specDensity f r : ENNReal)) ∧
      ∀ᶠ R₀ in atTop, Tendsto (fun Y : ℝ => (1 / Y : ℂ) * ∫ y in R₀..Y,
        ((∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
            EF.weilTest f f (Real.log n - y)) -
          ((Real.exp (y / 2) : ℝ) : ℂ) * paperFT (EF.weilTest f f) (-I / 2)) *
          cexp (-(y * a * I))) atTop (𝓝 (-(ν.real {a} : ℂ))) := by
  obtain ⟨ν, hν, hνK⟩ := exists_spectralMeasure hW hf hfc
  refine ⟨ν, hν, eq_withDensity_boundaryMeasure hW hf hfc hνK, ?_⟩
  set K := EF.weilTest f f with hKdef
  have hK := admissible_weilTest hf hfc
  obtain ⟨R, hR⟩ := exists_abs_bound_of_hasCompactSupport hK.supp
  filter_upwards [eventually_gt_atTop R] with R₀ hR₀
  -- the decaying part
  set δ : ℝ → ℂ := fun y => ((Real.exp (-(y / 2)) : ℝ) : ℂ) * paperFT K (I / 2) +
    archPart (transl y K) with hδ
  have hδc : Continuous δ := by
    refine Continuous.add ?_ (continuous_archPart_transl hK)
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).mul
      continuous_const
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Real.exp (-(y / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.atTop_div_const (by norm_num)))
    have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).mul_const (paperFT K (I / 2))
    rw [Complex.ofReal_zero, zero_mul] at h2
    have h3 := h2.add (tendsto_archPart_transl (K := K))
    rw [zero_add] at h3
    exact h3
  have hcf : Continuous fun y : ℝ => charFun ν y := continuous_charFun
  set e : ℝ → ℂ := fun y => cexp (-(y * a * I)) with he
  have hec : Continuous e := by fun_prop
  -- on `[R₀, Y]` the error is `δ − charFun ν`
  have hid : ∀ y : ℝ, R < y →
      ((∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * K (Real.log n - y)) -
        ((Real.exp (y / 2) : ℝ) : ℂ) * paperFT K (-I / 2)) = δ y - charFun ν y := by
    intro y hy
    rw [primeSum_transl_sub_main_eq lam hR hy, hνK y, spectralKernel]
  have hsplit : ∀ Y : ℝ, R₀ ≤ Y → (∫ y in R₀..Y,
      ((∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * K (Real.log n - y)) -
        ((Real.exp (y / 2) : ℝ) : ℂ) * paperFT K (-I / 2)) * e y) =
      (∫ y in R₀..Y, δ y * e y) - ((∫ y in (0 : ℝ)..Y, charFun ν y * e y) -
        ∫ y in (0 : ℝ)..R₀, charFun ν y * e y) := by
    intro Y hY
    have hF : ∀ a b : ℝ, IntervalIntegrable (fun y => charFun ν y * e y) volume a b :=
      fun a b => (hcf.mul hec).intervalIntegrable a b
    have hG : ∀ a b : ℝ, IntervalIntegrable (fun y => δ y * e y) volume a b :=
      fun a b => (hδc.mul hec).intervalIntegrable a b
    have h1 := intervalIntegral.integral_interval_sub_left (hF 0 Y) (hF 0 R₀)
    have h2 := intervalIntegral.integral_sub (hG R₀ Y) (hF R₀ Y)
    rw [h1, ← h2]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => ?_)
    rw [uIoc_of_le hY] at hy
    rw [hid y (lt_trans hR₀ hy.1)]
    ring
  have hen : ∀ y : ℝ, ‖e y‖ = 1 := fun y => by
    rw [he]
    simp only
    rw [show -((y : ℂ) * a * I) = ((-(y * a) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hδe : Tendsto (fun y => δ y * e y) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := hδlim.norm
    rw [norm_zero] at this
    refine this.congr fun y => ?_
    rw [norm_mul, hen, mul_one]
  have hA := tendsto_mean_of_tendsto_zero (hδc.mul hec) hδe R₀
  have hB := GaloisForLFunctions.HTGeometry.tendsto_oneSided_mean_charFun_mul ν a
  have hinv : Tendsto (fun Y : ℝ => (1 / Y : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    rw [Complex.ofReal_zero] at h
    refine h.congr fun Y => ?_
    simp
  have hC := hinv.mul_const (∫ y in (0 : ℝ)..R₀, charFun ν y * e y)
  rw [zero_mul] at hC
  have hall := hA.sub (hB.sub hC)
  rw [sub_zero, zero_sub] at hall
  refine hall.congr' ((eventually_ge_atTop R₀).mono fun Y hY => ?_)
  have hs := hsplit Y hY
  simp only [he] at hs
  simp only [Pi.mul_apply, he]
  rw [hs]
  ring

end RHTower.WeilSpectral

end
