import Mathlib

open Filter Topology Set

/-!
# Monotone decay of Fourier modes and the cusp tail

A solution of `a'' = (k² - λ/y²) a` on `y > 0` that tends to `0` has `|a|²` nonincreasing on
`[y₀, ∞)` once `λ ≤ k² y₀²` (`normSq_antitoneOn`): `(|a|²)'' = 2|a'|² + 2(k² - λ/y²)|a|² ≥ 0` there, and a
convex function tending to `0` cannot increase (`deriv_nonpos_of_monotone_tendsto`). For such a profile
the hyperbolic tail mass is controlled by the bulk mass,
`(Y - y₁) ∫_Y^∞ G/y² ≤ y₁ ∫_{y₁}^Y G/y²` (`tail_le_bulk`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXueCuspTail

theorem hasDerivAt_re {a : ℝ → ℂ} {a' : ℂ} {y : ℝ} (h : HasDerivAt a a' y) :
    HasDerivAt (fun t => (a t).re) a'.re y := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h

theorem hasDerivAt_im {a : ℝ → ℂ} {a' : ℂ} {y : ℝ} (h : HasDerivAt a a' y) :
    HasDerivAt (fun t => (a t).im) a'.im y := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h

/-- A convex function on `[y₀, ∞)` that tends to `0` is nonincreasing there (derivative form). -/
theorem deriv_nonpos_of_monotone_tendsto {G G' : ℝ → ℝ} {y₀ : ℝ}
    (hG : ∀ y, y₀ ≤ y → HasDerivAt G (G' y) y) (hmono : MonotoneOn G' (Ici y₀))
    (hlim : Tendsto G atTop (𝓝 0)) (hnn : ∀ y, y₀ ≤ y → 0 ≤ G y) :
    ∀ y, y₀ ≤ y → G' y ≤ 0 := by
  intro y₁ hy₁
  by_contra hpos
  push Not at hpos
  -- G(y) ≥ G(y₁) + G'(y₁)(y - y₁) for y ≥ y₁
  have hlow : ∀ y, y₁ ≤ y → G y₁ + G' y₁ * (y - y₁) ≤ G y := by
    intro y hy
    -- mean value on [y₁, y]: the function G - G'(y₁) t is monotone
    have hm : MonotoneOn (fun t => G t - G' y₁ * t) (Icc y₁ y) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc y₁ y)
      · intro t ht
        exact ((hG t (hy₁.trans ht.1)).continuousAt.sub (continuousAt_const.mul continuousAt_id)).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact ((hG t (hy₁.trans ht.1.le)).sub ((hasDerivAt_id t).const_mul (G' y₁))).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have hd : HasDerivAt (fun t => G t - G' y₁ * t) (G' t - G' y₁) t := by
          have := (hG t (hy₁.trans ht.1.le)).sub ((hasDerivAt_id t).const_mul (G' y₁))
          simp only [mul_one] at this
          exact this
        rw [hd.deriv]
        have := hmono (show y₁ ∈ Ici y₀ from hy₁) (show t ∈ Ici y₀ from hy₁.trans ht.1.le) ht.1.le
        linarith
    have := hm (left_mem_Icc.mpr hy) (right_mem_Icc.mpr hy) hy
    simp only at this; linarith
  -- contradiction with the limit
  have hev := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < G y₁ + 1 by linarith [hnn y₁ hy₁])))
  obtain ⟨A, hA⟩ := eventually_atTop.mp hev
  set y := max A (y₁ + 1 / G' y₁ + 1)
  have hy : y₁ ≤ y := by
    have : 0 < 1 / G' y₁ := by positivity
    have : y₁ ≤ y₁ + 1 / G' y₁ + 1 := by linarith
    exact this.trans (le_max_right _ _)
  have h1 := hlow y hy
  have h2 := hA y (le_max_left _ _)
  have h3 : G' y₁ * (y - y₁) ≥ 1 := by
    have : y - y₁ ≥ 1 / G' y₁ := by
      have := le_max_right A (y₁ + 1 / G' y₁ + 1)
      linarith
    calc G' y₁ * (y - y₁) ≥ G' y₁ * (1 / G' y₁) := by gcongr
      _ = 1 := by field_simp
  linarith

/-- **Monotone decay of a modal coefficient.** If `a'' = (k² - λ/y²) a` on `y > 0` and `a → 0`, then
`|a|²` is nonincreasing on `[y₀, ∞)` whenever `λ ≤ k² y₀²`: there `|a|²` is convex and tends to `0`. -/
theorem normSq_antitoneOn {a : ℝ → ℂ} {k lam y₀ : ℝ} (hy₀ : 0 < y₀) (hk : lam ≤ k ^ 2 * y₀ ^ 2)
    (h1 : ∀ y, 0 < y → HasDerivAt a (deriv a y) y)
    (h2 : ∀ y, 0 < y → HasDerivAt (deriv a) (deriv (deriv a) y) y)
    (hode : ∀ y : ℝ, 0 < y → -((y : ℝ) : ℂ) ^ 2 * (deriv (deriv a) y - ((k : ℂ)) ^ 2 * a y) = (lam : ℂ) * a y)
    (hdec : Tendsto a atTop (𝓝 0)) :
    AntitoneOn (fun y => Complex.normSq (a y)) (Ici y₀) := by
  set G : ℝ → ℝ := fun y => (a y).re ^ 2 + (a y).im ^ 2
  set G' : ℝ → ℝ := fun y => 2 * ((a y).re * (deriv a y).re + (a y).im * (deriv a y).im)
  set G'' : ℝ → ℝ := fun y => 2 * ((deriv a y).re ^ 2 + (a y).re * (deriv (deriv a) y).re +
    ((deriv a y).im ^ 2 + (a y).im * (deriv (deriv a) y).im))
  have hGd : ∀ y, 0 < y → HasDerivAt G (G' y) y := by
    intro y hy
    have hr := hasDerivAt_re (h1 y hy)
    have hi := hasDerivAt_im (h1 y hy)
    have := (hr.pow 2).add (hi.pow 2)
    have e : G' y = ((2 : ℕ) : ℝ) * (a y).re ^ (2 - 1) * (deriv a y).re +
        ((2 : ℕ) : ℝ) * (a y).im ^ (2 - 1) * (deriv a y).im := by
      simp only [G']; norm_num; ring
    rw [e]; exact this
  have hG'd : ∀ y, 0 < y → HasDerivAt G' (G'' y) y := by
    intro y hy
    have hr := hasDerivAt_re (h1 y hy)
    have hi := hasDerivAt_im (h1 y hy)
    have hr' := hasDerivAt_re (h2 y hy)
    have hi' := hasDerivAt_im (h2 y hy)
    have := ((hr.mul hr').add (hi.mul hi')).const_mul 2
    have e : G'' y = 2 * ((deriv a y).re * (deriv a y).re + (a y).re * (deriv (deriv a) y).re +
        ((deriv a y).im * (deriv a y).im + (a y).im * (deriv (deriv a) y).im)) := by
      simp only [G'']; ring
    rw [e]; exact this
  have hacc : ∀ y, 0 < y → deriv (deriv a) y = ((k ^ 2 - lam / y ^ 2 : ℝ) : ℂ) * a y := by
    intro y hy
    have h := hode y hy
    have hy2 : ((y : ℝ) : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hy 2).ne'
    have hm : deriv (deriv a) y * ((y : ℝ) : ℂ) ^ 2 = ((k : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ 2 - lam) * a y := by
      linear_combination (-1 : ℂ) * h
    rw [← eq_div_iff hy2] at hm
    rw [hm]
    push_cast
    have hc : (lam : ℂ) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ 2 = lam := div_mul_cancel₀ _ hy2
    rw [div_eq_iff hy2]
    linear_combination (a y) * hc
  have hG''nn : ∀ y, y₀ ≤ y → 0 ≤ G'' y := by
    intro y hy
    have hypos : 0 < y := hy₀.trans_le hy
    have hc : 0 ≤ k ^ 2 - lam / y ^ 2 := by
      rw [sub_nonneg, div_le_iff₀ (by positivity)]
      have := pow_le_pow_left₀ hy₀.le hy 2
      nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg k)]
    simp only [G'']
    rw [hacc y hypos]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      add_zero]
    nlinarith [sq_nonneg (deriv a y).re, sq_nonneg (deriv a y).im, mul_nonneg hc (sq_nonneg (a y).re),
      mul_nonneg hc (sq_nonneg (a y).im)]
  have hmono : MonotoneOn G' (Ici y₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici y₀)
    · intro y hy; exact (hG'd y (hy₀.trans_le hy)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hG'd y (hy₀.trans hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hG'd y (hy₀.trans hy)).deriv]
      exact hG''nn y hy.le
  have hlim : Tendsto G atTop (𝓝 0) := by
    have : Tendsto (fun y => Complex.normSq (a y)) atTop (𝓝 (Complex.normSq 0)) :=
      (Complex.continuous_normSq.tendsto 0).comp hdec
    simpa [G, Complex.normSq_apply, pow_two] using this
  have hnn : ∀ y, y₀ ≤ y → 0 ≤ G y := fun y _ => by positivity
  have hG'np := deriv_nonpos_of_monotone_tendsto (fun y hy => hGd y (hy₀.trans_le hy)) hmono hlim hnn
  have hanti : AntitoneOn G (Ici y₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici y₀)
    · intro y hy; exact (hGd y (hy₀.trans_le hy)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hGd y (hy₀.trans hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hGd y (hy₀.trans hy)).deriv]
      exact hG'np y hy.le
  intro u hu v hv huv
  have := hanti hu hv huv
  simpa [G, Complex.normSq_apply, pow_two] using this

open MeasureTheory

theorem integrableOn_inv_sq {Y : ℝ} (hY : 0 < Y) : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ioi Y) := by
  have := integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hY
  refine this.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy : 0 < y := hY.trans hy
  show y ^ (-2 : ℝ) = 1 / y ^ 2
  rw [Real.rpow_neg hy.le, one_div, Real.rpow_two]

theorem integral_Ioi_inv_sq {Y : ℝ} (hY : 0 < Y) : ∫ y in Ioi Y, 1 / y ^ 2 = 1 / Y := by
  have := integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hY
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one] at this
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun y hy => by
    have hy : 0 < y := hY.trans hy
    show y ^ (-2 : ℝ) = 1 / y ^ 2
    rw [Real.rpow_neg hy.le, one_div, Real.rpow_two])]
  rw [this]; field_simp

/-- **Tail against bulk.** For `G ≥ 0` nonincreasing on `[y₁, ∞)`,
`(Y - y₁) ∫_Y^∞ G/y² ≤ y₁ ∫_{y₁}^Y G/y²`. -/
theorem tail_le_bulk {G : ℝ → ℝ} {y₁ Y : ℝ} (hy₁ : 0 < y₁) (hY : y₁ < Y)
    (hanti : AntitoneOn G (Ici y₁)) (hnn : ∀ y, y₁ ≤ y → 0 ≤ G y)
    (hint : IntegrableOn (fun y => G y / y ^ 2) (Ioi y₁)) :
    (Y - y₁) * ∫ y in Ioi Y, G y / y ^ 2 ≤ y₁ * ∫ y in Ioc y₁ Y, G y / y ^ 2 := by
  have hY0 : 0 < Y := hy₁.trans hY
  have hGY := hnn Y hY.le
  -- tail
  have htail : ∫ y in Ioi Y, G y / y ^ 2 ≤ G Y / Y := by
    calc ∫ y in Ioi Y, G y / y ^ 2 ≤ ∫ y in Ioi Y, G Y * (1 / y ^ 2) := by
          apply setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hY.le))
            ((integrableOn_inv_sq hY0).const_mul _) measurableSet_Ioi
          intro y hy
          have hy' : Y ≤ y := le_of_lt hy
          have := hanti (show Y ∈ Ici y₁ from hY.le) (show y ∈ Ici y₁ from hY.le.trans hy') hy'
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = G Y / Y := by rw [integral_const_mul, integral_Ioi_inv_sq hY0]; ring
  -- bulk
  have hbulk : G Y * (1 / y₁ - 1 / Y) ≤ ∫ y in Ioc y₁ Y, G y / y ^ 2 := by
    have hint2 : IntegrableOn (fun y => G y / y ^ 2) (Ioc y₁ Y) := hint.mono_set Ioc_subset_Ioi_self
    have hc : IntegrableOn (fun y : ℝ => G Y * (1 / y ^ 2)) (Ioc y₁ Y) :=
      ((integrableOn_inv_sq hy₁).mono_set Ioc_subset_Ioi_self).const_mul _
    have hval : ∫ y in Ioc y₁ Y, G Y * (1 / y ^ 2) = G Y * (1 / y₁ - 1 / Y) := by
      rw [integral_const_mul]
      congr 1
      have h1 := integral_Ioi_inv_sq hy₁
      have h2 := integral_Ioi_inv_sq hY0
      have hsplit : ∫ y in Ioi y₁, 1 / y ^ 2 = (∫ y in Ioc y₁ Y, 1 / y ^ 2) + ∫ y in Ioi Y, 1 / y ^ 2 := by
        rw [← Ioc_union_Ioi_eq_Ioi hY.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          ((integrableOn_inv_sq hy₁).mono_set Ioc_subset_Ioi_self)
          ((integrableOn_inv_sq hy₁).mono_set (Ioi_subset_Ioi hY.le))]
      linarith
    rw [← hval]
    apply setIntegral_mono_on hc hint2 measurableSet_Ioc
    intro y hy
    have := hanti (show y ∈ Ici y₁ from hy.1.le) (show Y ∈ Ici y₁ from hY.le) hy.2
    have hy0 : 0 < y := hy₁.trans hy.1
    calc G Y * (1 / y ^ 2) ≤ G y * (1 / y ^ 2) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = G y / y ^ 2 := by ring
  have hfrac : (Y - y₁) * (G Y / Y) = y₁ * (G Y * (1 / y₁ - 1 / Y)) := by
    field_simp
  calc (Y - y₁) * ∫ y in Ioi Y, G y / y ^ 2 ≤ (Y - y₁) * (G Y / Y) :=
        mul_le_mul_of_nonneg_left htail (by linarith)
    _ = y₁ * (G Y * (1 / y₁ - 1 / Y)) := hfrac
    _ ≤ _ := mul_le_mul_of_nonneg_left hbulk hy₁.le

end GaloisForLFunctions.RHTower.SarnakXueCuspTail
