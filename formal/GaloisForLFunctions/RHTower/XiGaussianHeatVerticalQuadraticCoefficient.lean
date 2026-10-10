import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalVinogradovKorobovGrowth

/-!
# The quadratic growth coefficient of the vertical heat trace

On the vertical line `Re τ = a` the heat trace `ν(a+ib) = Σ_q exp(-(a+ib) z_q²)` has three growth
regimes, governed by three functionals of the zeros `ρ = β + iγ`:

* sublinear exponent `log ‖ν‖ = o(|b|)` ⇔ RH (`riemannHypothesis_iff_xiGaussianHeatTraceC_subexponential`);
* linear exponent, exponential type `κ` ⇔ `sup 2|γ||β - 1/2| ≤ κ`
  (`xiGaussianHeatTraceC_exponentialType_iff_xi_zeros`);
* quadratic exponent: governed by the asymptotic deviation `Δ∞ = limsup_{|γ|→∞} |β - 1/2|`.

**Theorem** (`exists_norm_xiGaussianHeatTraceC_le_quadratic`).  If every zero above some height `H`
satisfies `|β - 1/2| ≤ Δ`, then for every `θ ∈ (0, 1)` and `ε > 0`
`‖ν(a+ib)‖ ≤ C exp((Δ²/θ + ε) b²/a)`.

Hence `limsup log‖ν(a+ib)‖ / b² ≤ Δ∞²/a`.  Finitely many zeros below `H` cost only `e^{H|b|}`,
which is absorbed into `ε b²/a`.

The matching lower bound `limsup ≥ Δ∞²/a` is the open part of the quadratic law.  It requires that
the terms near the saddle height `|γ| ≈ |b|Δ/a` do not cancel, a Turán power-sum type
non-cancellation.  Unconditionally `Δ∞ ≤ 1/2`, and the zero-free regions only give
`Δ∞ ≤ 1/2` again (their widths tend to `0`).
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- **Quadratic upper bound from an asymptotic deviation bound.** -/
theorem exists_norm_xiGaussianHeatTraceC_le_quadratic {a Δ H θ ε : ℝ} (ha : 0 < a)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (hzeros : ∀ q : XiZeroCopy, H ≤ |(xiSpectralPoint q).re| → |(xiSpectralPoint q).im| ≤ Δ) :
    ∃ C : ℝ, ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤
      C * Real.exp ((Δ ^ 2 / θ + ε) * b ^ 2 / a) := by
  set K := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  have hK : 0 ≤ K := tsum_nonneg fun _ => by positivity
  set c : ℝ := (1 - θ) * a
  have hc : 0 < c := by simp only [c]; nlinarith
  set H' : ℝ := max H 0
  set L : ℝ := H' ^ 2 * a / (4 * ε)
  set Q : ℝ := Δ ^ 2 / θ + ε
  set A : ℝ := Real.exp (a / 4 + L + c / 4) / c
  have hA : 0 ≤ A := by positivity
  refine ⟨A * K, fun b => ?_⟩
  have hτ : 0 < ((a : ℂ) + b * I).re := by simpa using ha
  have hterm : ∀ q : XiZeroCopy, ‖xiGaussianHeatTermC ((a : ℂ) + b * I) q‖ ≤
      A * Real.exp (Q * b ^ 2 / a) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro q
    obtain ⟨h4, hzf⟩ := xiSpectralPoint_im_le_zeroFree q
    set x := (xiSpectralPoint q).re
    set y := (xiSpectralPoint q).im
    have hy : |y| ≤ 1 / 2 := by
      have : 0 < 1 / 58 / Real.log |x| := by
        have : 0 < Real.log |x| := Real.log_pos (by linarith)
        positivity
      linarith
    have hy2 : y ^ 2 ≤ 1 / 4 := by
      have := sq_le_sq' (abs_le.1 hy).1 (abs_le.1 hy).2
      linarith
    have hN : ‖xiSpectralPoint q‖ ^ (2 : ℕ) = x ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hx16 : 16 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have hNpos : 0 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y]
    rw [norm_xiGaussianHeatTermC, hN]
    have hre : ((a : ℂ) + b * I).re = a := by simp
    have him : ((a : ℂ) + b * I).im = b := by simp
    have hw_re : (xiSpectralPoint q ^ (2 : ℕ)).re = x ^ 2 - y ^ 2 := by
      rw [pow_two, Complex.mul_re]; ring
    have hw_im : (xiSpectralPoint q ^ (2 : ℕ)).im = 2 * x * y := by
      rw [pow_two, Complex.mul_im]; ring
    rw [hre, him, hw_re, hw_im]
    have hbxy : b * (2 * x * y) ≤ 2 * |b| * |x| * |y| := by
      calc b * (2 * x * y) ≤ |b * (2 * x * y)| := le_abs_self _
        _ = 2 * |b| * |x| * |y| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    have hb2 : |b| ^ 2 = b ^ 2 := sq_abs b
    have hQsplit : Q * b ^ 2 / a = Δ ^ 2 / θ * b ^ 2 / a + ε * b ^ 2 / a := by
      simp only [Q]; ring
    have hL0 : 0 ≤ L := by positivity
    -- the exponent: Gaussian decay `-c x²` plus a bounded part
    have hay : a * y ^ 2 ≤ a / 4 := by nlinarith
    have hcx' : c * x ^ 2 = a * x ^ 2 - θ * a * x ^ 2 := by simp only [c]; ring
    have hεb : 0 ≤ ε * b ^ 2 / a := by positivity
    have hΔb : 0 ≤ Δ ^ 2 / θ * b ^ 2 / a := by positivity
    have hlin : -(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)) = -(a * x ^ 2) + a * y ^ 2 + b * (2 * x * y) := by
      ring
    have hsplitE : -(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)) ≤
        a / 4 + L + Q * b ^ 2 / a - c * x ^ 2 := by
      rw [hlin, hQsplit]
      rcases le_or_gt H |x| with hhigh | hlow
      · have hyΔ : |y| ≤ Δ := hzeros q hhigh
        have h1 : 2 * |b| * |x| * |y| ≤ 2 * |b| * |x| * Δ :=
          mul_le_mul_of_nonneg_left hyΔ (by positivity)
        have hθa : 0 < θ * a := by positivity
        have h2 : 2 * |b| * |x| * Δ ≤ θ * a * x ^ 2 + Δ ^ 2 / θ * b ^ 2 / a := by
          have key := sq_nonneg (θ * a * |x| - Δ * |b|)
          have e2 : (θ * a * |x| - Δ * |b|) ^ 2 =
              θ ^ 2 * a ^ 2 * |x| ^ 2 - 2 * θ * a * Δ * |x| * |b| + Δ ^ 2 * |b| ^ 2 := by ring
          rw [e2, hx2, hb2] at key
          have e : θ * a * x ^ 2 + Δ ^ 2 / θ * b ^ 2 / a =
              (θ ^ 2 * a ^ 2 * x ^ 2 + Δ ^ 2 * b ^ 2) / (θ * a) := by field_simp
          rw [e, le_div_iff₀ hθa]
          linarith
        linarith
      · have hxH : |x| ≤ H' := hlow.le.trans (le_max_left _ _)
        have h1 : 2 * |b| * |x| * |y| ≤ |b| * H' := by
          have h2y : 2 * |y| ≤ 1 := by linarith
          calc 2 * |b| * |x| * |y| = |b| * |x| * (2 * |y|) := by ring
            _ ≤ |b| * |x| * 1 := mul_le_mul_of_nonneg_left h2y (by positivity)
            _ ≤ |b| * H' := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hxH (abs_nonneg b)
        have h2 : |b| * H' ≤ ε * b ^ 2 / a + L := by
          have key := sq_nonneg (2 * ε * |b| - H' * a)
          have e2 : (2 * ε * |b| - H' * a) ^ 2 =
              4 * ε ^ 2 * |b| ^ 2 - 4 * ε * a * (|b| * H') + H' ^ 2 * a ^ 2 := by ring
          rw [e2, hb2] at key
          have hεa : 0 < 4 * ε * a := by positivity
          have e : ε * b ^ 2 / a + L = (4 * ε ^ 2 * b ^ 2 + H' ^ 2 * a ^ 2) / (4 * ε * a) := by
            simp only [L]; field_simp
          rw [e, le_div_iff₀ hεa]
          linarith
        have hθx : 0 ≤ θ * a * x ^ 2 := by positivity
        linarith
    have hcN : 0 < c * (x ^ 2 + y ^ 2) := by positivity
    calc Real.exp (-(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)))
        ≤ Real.exp ((a / 4 + L + c / 4) + Q * b ^ 2 / a + -(c * (x ^ 2 + y ^ 2))) := by
          have hcy : c * y ^ 2 ≤ c / 4 := by nlinarith
          apply Real.exp_le_exp.2; linarith
      _ = Real.exp (a / 4 + L + c / 4) * Real.exp (Q * b ^ 2 / a) *
            Real.exp (-(c * (x ^ 2 + y ^ 2))) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (a / 4 + L + c / 4) * Real.exp (Q * b ^ 2 / a) *
            (1 / (c * (x ^ 2 + y ^ 2))) :=
          mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos hcN) (by positivity)
      _ = A * Real.exp (Q * b ^ 2 / a) * (1 / (x ^ 2 + y ^ 2)) := by
          simp only [A]; field_simp
  calc ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖
      ≤ ∑' q : XiZeroCopy, A * Real.exp (Q * b ^ 2 / a) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
        (norm_tsum_le_tsum_norm (summable_norm_xiGaussianHeatTermC hτ)).trans
          (Summable.tsum_le_tsum hterm (summable_norm_xiGaussianHeatTermC hτ)
            (xiSpectralPoint_inv_sq_summable.mul_left _))
    _ = A * K * Real.exp (Q * b ^ 2 / a) := by
        rw [tsum_mul_left]; ring

/-- **Quadratic coefficient bound.**  If every zero above height `H` satisfies `|β - 1/2| ≤ Δ`, then
for every `ε > 0`, `‖ν(a+ib)‖ ≤ C exp((Δ² + ε) b²/a)`.  Hence `limsup log‖ν(a+ib)‖/b² ≤ Δ∞²/a`. -/
theorem exists_norm_xiGaussianHeatTraceC_le_quadratic_coefficient {a Δ H ε : ℝ} (ha : 0 < a)
    (hε : 0 < ε)
    (hzeros : ∀ q : XiZeroCopy, H ≤ |(xiSpectralPoint q).re| → |(xiSpectralPoint q).im| ≤ Δ) :
    ∃ C : ℝ, ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤
      C * Real.exp ((Δ ^ 2 + ε) * b ^ 2 / a) := by
  set θ : ℝ := (Δ ^ 2 + ε / 4) / (Δ ^ 2 + ε / 2)
  have hden : 0 < Δ ^ 2 + ε / 2 := by positivity
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by
    rw [div_lt_one hden]; linarith
  obtain ⟨C, hC⟩ := exists_norm_xiGaussianHeatTraceC_le_quadratic (H := H) ha hθ0 hθ1
    (by positivity : (0 : ℝ) < ε / 2) hzeros
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have : 0 < Real.exp ((Δ ^ 2 / θ + ε / 2) * 0 ^ 2 / a) := Real.exp_pos _
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg this
    linarith [norm_nonneg (xiGaussianHeatTraceC ((a : ℂ) + (0 : ℝ) * I))]
  refine ⟨C, fun b => (hC b).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0)⟩
  have hΔθ : Δ ^ 2 / θ ≤ Δ ^ 2 + ε / 2 := by
    simp only [θ]
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg Δ]
  have hb : 0 ≤ b ^ 2 / a := by positivity
  have : (Δ ^ 2 / θ + ε / 2) * b ^ 2 / a ≤ (Δ ^ 2 + ε) * b ^ 2 / a := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hb
  exact this

end

end RHTower
