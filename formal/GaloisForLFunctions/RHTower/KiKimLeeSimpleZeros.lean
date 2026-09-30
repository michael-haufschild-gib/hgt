import GaloisForLFunctions.RHTower.KiKimLeeFiniteness

/-!
# Ki–Kim–Lee: the zeros of large height are simple

Differentiating the reflection split `H_t(X + iy) = Q(−y) + conj Q(y)` at `y = 0` gives

`H_t(X) = 2 Re Q(0)`,   `i H_t'(X) = −Q'(0) + conj Q'(0) = −2i Im Q'(0)`.

At a real zero `Re Q(0) = 0`, so the positivity `Re(Q'(0) conj Q(0)) = Im Q'(0) Im Q(0) > 0` of the
large-height window forces `Im Q'(0) ≠ 0`, i.e. `H_t'(X) ≠ 0` (`eventually_deriv_riemannHeat_ne_zero`).
With the finiteness of the non-real zeros: for `0 < t ≤ 1/8`, all but finitely many zeros of `H_t`
are real and simple (`riemannHeat_nonreal_or_multiple_zeros_finite`).
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-- **Simple zeros at large height.** -/
theorem eventually_deriv_riemannHeat_ne_zero {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) :
    ∀ᶠ X : ℝ in atTop, riemannHeat t X = 0 → deriv (riemannHeat t) X ≠ 0 := by
  filter_upwards [eventually_re_slope_mul_conj_pos ht ht8] with X hpos hzero hderiv
  set Q := halfGaussTransform t (xiLine X) with hQ
  set D₀ := ∫ w in Ioi (0 : ℝ), (((w - 0) / (2 * t) * gaussDensity t (w - 0) : ℝ) : ℂ) *
    xiLine X w with hD₀
  have hQd : HasDerivAt Q D₀ 0 := hasDerivAt_halfGaussTransform ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) 0
  have hpos0 : 0 < (D₀ * starRingEnd ℂ (Q 0)).re := hpos 0 (by simp)
  have hsplit : ∀ y : ℝ, riemannHeat t ((X : ℂ) + I * y) = Q (-y) + starRingEnd ℂ (Q y) :=
    fun y => riemannHeat_eq_halfGaussAverage ht X y
  -- the derivative of the left side along the vertical line
  have hL : HasDerivAt (fun y : ℝ => riemannHeat t ((X : ℂ) + I * y))
      (deriv (riemannHeat t) X * I) 0 := by
    have hd := (differentiable_riemannHeat ht.le ((X : ℂ) + I * ((0 : ℝ) : ℂ))).hasDerivAt
    have hin : HasDerivAt (fun w : ℂ => (X : ℂ) + I * w) I ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul I).const_add (X : ℂ)
    have h2 := (hd.comp ((0 : ℝ) : ℂ) hin).comp_ofReal
    simpa using h2
  -- the derivative of the right side
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
  -- `Re Q(0) = 0` from the zero
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

theorem deriv_riemannHeat_neg {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    deriv (riemannHeat t) (-z) = -deriv (riemannHeat t) z := by
  have hd := (differentiable_riemannHeat ht (-z)).hasDerivAt
  have h := hd.comp z (hasDerivAt_neg z)
  have hfun : (riemannHeat t ∘ fun w => -w) = riemannHeat t := by
    funext w; exact riemannHeat_neg ht w
  rw [hfun] at h
  have := h.unique (differentiable_riemannHeat ht z).hasDerivAt
  rw [← this]
  ring

/-- **Large-height simplicity.** For `0 < t ≤ 1/8` there is `X₀` such that every real zero of `H_t`
with `|x| ≥ X₀` is simple. -/
theorem exists_riemannHeat_zeros_simple {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ |x| → riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0 := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventually_deriv_riemannHeat_ne_zero ht ht8)
  refine ⟨max X₀ 0, fun x hx hz => ?_⟩
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    exact hX₀ x (le_of_max_le_left hx) hz
  · rw [abs_of_neg h0] at hx
    have hz' : riemannHeat t ((-x : ℝ) : ℂ) = 0 := by
      rw [ofReal_neg, riemannHeat_neg ht.le]; exact hz
    have := hX₀ (-x) (le_of_max_le_left hx) hz'
    rw [ofReal_neg, deriv_riemannHeat_neg ht.le] at this
    exact fun h => this (by rw [h, neg_zero])

/-- **Ki–Kim–Lee.** For `0 < t ≤ 1/8`, all but finitely many zeros of `H_t` are real and simple. -/
theorem riemannHeat_nonreal_or_multiple_zeros_finite {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) :
    {z : ℂ | riemannHeat t z = 0 ∧ (z.im ≠ 0 ∨ deriv (riemannHeat t) z = 0)}.Finite := by
  obtain ⟨X₁, hX₁⟩ := exists_riemannHeat_zeros_real ht
  obtain ⟨X₂, hX₂⟩ := exists_riemannHeat_zeros_simple ht ht8
  have hdiff := differentiable_riemannHeat ht.le
  have hiso : ∀ z ∈ (univ : Set ℂ), ¬ (∀ᶠ w in 𝓝 z, riemannHeat t w = 0) := by
    intro z _ h
    have := (hdiff.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) h (mem_univ 0)
    exact riemannHeat_zero_ne ht.le this
  set R := max |X₁| |X₂| + 1 with hR
  have hfin := GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact isOpen_univ
    hdiff.differentiableOn hiso (isCompact_closedBall (0 : ℂ) R) (subset_univ _)
  refine hfin.subset fun z ⟨hz, hbad⟩ => ⟨?_, hz⟩
  have him2 : z.im ^ 2 ≤ 1 / 4 :=
    (riemannHeat_zeros_im_sq_le ht hz).trans (max_le (by linarith) (by norm_num))
  have him' : |z.im| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  have hre : |z.re| ≤ max |X₁| |X₂| := by
    rcases hbad with hne | hd
    · by_contra h
      push Not at h
      exact hne (hX₁ z hz ((le_abs_self X₁).trans ((le_max_left _ _).trans h.le)))
    · by_contra h
      push Not at h
      have hzre : z = (z.re : ℂ) := by
        have : z.im = 0 := hX₁ z hz ((le_abs_self X₁).trans ((le_max_left _ _).trans h.le))
        apply Complex.ext <;> simp [this]
      rw [hzre] at hz hd
      exact hX₂ z.re ((le_abs_self X₂).trans ((le_max_right _ _).trans h.le)) hz hd
  rw [mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ R := by rw [hR]; linarith

end

end RHTower.DeBruijn
