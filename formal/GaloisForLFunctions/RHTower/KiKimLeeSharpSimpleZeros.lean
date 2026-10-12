import GaloisForLFunctions.RHTower.KiKimLeeSharpHorizon
import GaloisForLFunctions.RHTower.KiKimLeeSimpleZeros

/-!
# The sharp heat horizon: zeros are real and simple

**Theorem** (`riemannHeat_zeros_real_simple_sharp`). For every `ε > 0` there is `X₀` such that for
all `0 < t ≤ 1/8`, every zero `z` of `H_t` with `|Re z| ≥ X₀` and
`|Re z| ≥ 2π e^{(1 + √3/2 + ε)/t}` is real and simple.

This is the Ki–Kim–Lee statement (real and simple) at the convexity constant `1 + √3/2`, with one
height `X₀` uniform in `t`.

**Proof.** Reality is `riemannHeat_zeros_real_sharp`. For simplicity, differentiate the reflection
split `H_t(X + iy) = Q(−y) + conj Q(y)` at `y = 0`. At a real zero `Re Q(0) = 0` and
`H_t'(X) = 0` would force `Im Q'(0) = 0`. Then `Re(Q'(0) conj Q(0)) = 0`, contradicting the window
slope positivity at `v = 0` (`re_slope_pos_sharp_window`). Negative real parts follow from
`H_t(−z) = H_t(z)`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- **Simplicity from slope positivity.** If the window slope pairing is positive at `v = 0`, a real
zero `X` of `H_t` is simple. -/
theorem deriv_riemannHeat_ne_zero_of_re_slope_pos_zero {t X : ℝ} (ht : 0 < t)
    (hpos0 : 0 < ((∫ w in Ioi (0 : ℝ), (((w - 0) / (2 * t) * gaussDensity t (w - 0) : ℝ) : ℂ) *
      xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) 0)).re)
    (hzero : riemannHeat t X = 0) : deriv (riemannHeat t) X ≠ 0 := by
  intro hderiv
  set Q := halfGaussTransform t (xiLine X) with hQ
  set D₀ := ∫ w in Ioi (0 : ℝ), (((w - 0) / (2 * t) * gaussDensity t (w - 0) : ℝ) : ℂ) *
    xiLine X w with hD₀
  have hQd : HasDerivAt Q D₀ 0 := hasDerivAt_halfGaussTransform ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) 0
  have hsplit : ∀ y : ℝ, riemannHeat t ((X : ℂ) + I * y) = Q (-y) + starRingEnd ℂ (Q y) :=
    fun y => riemannHeat_eq_halfGaussAverage ht X y
  have hL : HasDerivAt (fun y : ℝ => riemannHeat t ((X : ℂ) + I * y))
      (deriv (riemannHeat t) X * I) 0 := by
    have hd := (differentiable_riemannHeat ht.le ((X : ℂ) + I * ((0 : ℝ) : ℂ))).hasDerivAt
    have hin : HasDerivAt (fun w : ℂ => (X : ℂ) + I * w) I ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul I).const_add (X : ℂ)
    have h2 := (hd.comp ((0 : ℝ) : ℂ) hin).comp_ofReal
    simpa using h2
  have hR : HasDerivAt (fun y : ℝ => Q (-y) + starRingEnd ℂ (Q y)) (-D₀ + starRingEnd ℂ D₀) 0 := by
    have h1 : HasDerivAt (fun y : ℝ => Q (-y)) (-D₀) 0 := by
      have hQd' : HasDerivAt Q D₀ (-(0 : ℝ)) := by rw [neg_zero]; exact hQd
      have := hQd'.scomp 0 (hasDerivAt_neg (0 : ℝ))
      simpa [Function.comp_def] using this
    exact h1.add hQd.star
  have hfun : (fun y : ℝ => riemannHeat t ((X : ℂ) + I * y)) =
      fun y : ℝ => Q (-y) + starRingEnd ℂ (Q y) := funext hsplit
  rw [hfun] at hL
  have heq := hL.unique hR
  rw [hderiv, zero_mul] at heq
  have hz := hsplit 0
  simp only [ofReal_zero, mul_zero, add_zero, neg_zero] at hz
  rw [hzero] at hz
  have hre : (Q 0).re = 0 := by
    have := congrArg Complex.re hz
    simp at this
    linarith
  have him : D₀.im = 0 := by
    have := congrArg Complex.im heq
    simp at this
    linarith
  have hprod : (D₀ * starRingEnd ℂ (Q 0)).re = D₀.re * (Q 0).re + D₀.im * (Q 0).im := by
    simp [Complex.mul_re]
  rw [hprod, hre, him] at hpos0
  simp at hpos0

/-- **The sharp heat horizon, real and simple.** For every `ε > 0` there is `X₀` such that for all
`0 < t ≤ 1/8`, every zero `z` of `H_t` with `|Re z| ≥ X₀` and `|Re z| ≥ 2π e^{(1 + √3/2 + ε)/t}` is
real and simple. -/
theorem riemannHeat_zeros_real_simple_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      2 * Real.pi * Real.exp ((1 + Real.sqrt 3 / 2 + ε) / t) ≤ |z.re| →
        z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0 := by
  set c₀ := 1 + Real.sqrt 3 / 2 + ε with hc₀def
  obtain ⟨X₁, hX₁⟩ := riemannHeat_zeros_real_sharp hε
  obtain ⟨η, m, hη, hη4, hm, hmc, -, hc₀, hδ⟩ := exists_sharp_params (c₀ := c₀) (by linarith)
  obtain ⟨K, hKpos, hK⟩ := exists_norm_xiLine_le_strip_convexity hη (by linarith)
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp
    (eventually_sharp_errors_small (c₀ := c₀) (K := K) (b := 9 / 2 * (1 / η + 3)) hη hm hδ)
  refine ⟨max X₁ (2 * Real.pi * Real.exp (2 * max α₀ 160)),
    fun t ht ht8 z hz hX₀ hXc => ?_⟩
  have hreal : z.im = 0 := hX₁ t ht ht8 z hz ((le_max_left _ _).trans hX₀) hXc
  refine ⟨hreal, ?_⟩
  have hX₂ : 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ |z.re| := (le_max_right _ _).trans hX₀
  have hsimple : ∀ x : ℝ, 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ x →
      2 * Real.pi * Real.exp (c₀ / t) ≤ x → riemannHeat t x = 0 →
        deriv (riemannHeat t) x ≠ 0 := fun x hx hxc hzx =>
    deriv_riemannHeat_ne_zero_of_re_slope_pos_zero ht
      (re_slope_pos_sharp_window hη hη4 hm hmc hc₀ hK hKpos.le hα₀ ht ht8 hx hxc 0 (by simp)) hzx
  have hzre : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hreal]
  rcases le_or_gt 0 z.re with h0 | h0
  · rw [abs_of_nonneg h0] at hX₂ hXc
    rw [hzre]
    exact hsimple z.re hX₂ hXc (by rw [← hzre]; exact hz)
  · rw [abs_of_neg h0] at hX₂ hXc
    have hz' : riemannHeat t ((-z.re : ℝ) : ℂ) = 0 := by
      rw [ofReal_neg, riemannHeat_neg ht.le, ← hzre]; exact hz
    have := hsimple (-z.re) hX₂ hXc hz'
    rw [ofReal_neg, deriv_riemannHeat_neg ht.le, ← hzre] at this
    exact fun h => this (by rw [h, neg_zero])

end

end RHTower.DeBruijn
