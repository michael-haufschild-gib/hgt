import Mathlib

/-!
# Descent lemmas for the completed C5 centre numerator

Three self-contained real-analysis lemmas used to reduce the sign of the completed fixed-action
centre numerator `H` and the velocity floor `v ≥ 2Φ` to sign facts about the completed curvature
`c = −(log Θ)''` (card `theta-c5-completed-compensation-direct-gate.md`).

* **Monotone l'Hospital, strict form.**  If `N(0) = D(0) = 0`, `D' > 0` and `N'/D'` is strictly
  decreasing on `(0, t]`, then `N'(t)D(t) < N(t)D'(t)`, and `N/D` is strictly decreasing.
  The centre numerator is `H = 4(N'D − ND')` for `N = O`, `D = tE`, so two applications reduce
  `H < 0` to strict decrease of the local ratio `o'/(2e + te')`.
* **Two-point curvature gain.**  For `c` with `c > 0`, `c' ≥ 0`, `c'' ≥ 0` and
  `c'c'' ≥ c c'''` wherever `c''' ≥ 0`, the quantity
  `Q(y, x) = 3(c'(x)² − c'(y)²) − 2(c''(x) − c''(y))(c(x) + c(y))` is nonnegative for `x ≥ y`.
  This is exactly the `t`-free part of the derivative criterion for `o'/(2e + te')`.
* **Chord bound for a convex primitive.**  If `E` is convex on `[0, t]` with `E(0) = 0`, then
  `2∫₀ᵗ E ≤ t·E(t)`; with `E = Φ_t/2` this is the velocity floor `v = tΦ_t ≥ 2Φ`.
-/

open Set

namespace RHTower

/-- **Cauchy mean value in cross form.**  `N'(t) D(t) < N(t) D'(t)` when `N(0) = D(0) = 0`,
`D' > 0` and `N'/D'` is strictly decreasing on `(0, t]`. -/
theorem deriv_cross_lt_of_strictAnti_derivRatio {N D N' D' : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hN0 : N 0 = 0) (hD0 : D 0 = 0)
    (hNc : ContinuousOn N (Icc 0 t)) (hDc : ContinuousOn D (Icc 0 t))
    (hN : ∀ s ∈ Ioo 0 t, HasDerivAt N (N' s) s) (hD : ∀ s ∈ Ioo 0 t, HasDerivAt D (D' s) s)
    (hD' : ∀ s ∈ Ioc 0 t, 0 < D' s)
    (hanti : StrictAntiOn (fun s => N' s / D' s) (Ioc 0 t)) :
    N' t * D t < N t * D' t := by
  obtain ⟨ξ, hξ, hcauchy⟩ := exists_ratio_hasDerivAt_eq_ratio_slope N N' ht hNc hN D D' hDc hD
  rw [hN0, hD0, sub_zero, sub_zero] at hcauchy
  -- `D t > 0` by the mean value theorem
  obtain ⟨η, hη, hslope⟩ := exists_hasDerivAt_eq_slope D D' ht hDc hD
  have hDt : 0 < D t := by
    rw [hD0, sub_zero, sub_zero] at hslope
    have hη' : 0 < D' η := hD' η ⟨hη.1, hη.2.le⟩
    have : D t = D' η * t := by rw [hslope, div_mul_cancel₀ _ ht.ne']
    rw [this]; positivity
  have hD'ξ : 0 < D' ξ := hD' ξ ⟨hξ.1, hξ.2.le⟩
  have hD't : 0 < D' t := hD' t ⟨ht, le_rfl⟩
  have hlt : N' t / D' t < N' ξ / D' ξ := hanti ⟨hξ.1, hξ.2.le⟩ ⟨ht, le_rfl⟩ hξ.2
  have hratio : N' ξ / D' ξ = N t / D t := by
    rw [div_eq_div_iff hD'ξ.ne' hDt.ne']
    linarith [hcauchy]
  rw [hratio, div_lt_div_iff₀ hD't hDt] at hlt
  linarith

/-- **Monotone l'Hospital, strict form.**  Under the same hypotheses, `N/D` is strictly decreasing
on `(0, t]`. -/
theorem strictAntiOn_ratio_of_strictAnti_derivRatio {N D N' D' : ℝ → ℝ} {t : ℝ} (_ht : 0 < t)
    (hN0 : N 0 = 0) (hD0 : D 0 = 0)
    (hNc : ContinuousOn N (Icc 0 t)) (hDc : ContinuousOn D (Icc 0 t))
    (hN : ∀ s ∈ Ioo 0 t, HasDerivAt N (N' s) s) (hD : ∀ s ∈ Ioo 0 t, HasDerivAt D (D' s) s)
    (hD' : ∀ s ∈ Ioc 0 t, 0 < D' s)
    (hanti : StrictAntiOn (fun s => N' s / D' s) (Ioc 0 t)) :
    StrictAntiOn (fun s => N s / D s) (Ioc 0 t) := by
  -- `D > 0` on `(0, t]`
  have hDpos : ∀ s ∈ Ioc 0 t, 0 < D s := by
    intro s hs
    obtain ⟨η, hη, hslope⟩ := exists_hasDerivAt_eq_slope D D' hs.1
      (hDc.mono (Icc_subset_Icc le_rfl hs.2))
      (fun x hx => hD x ⟨hx.1, lt_of_lt_of_le hx.2 hs.2⟩)
    rw [hD0, sub_zero, sub_zero] at hslope
    have hη' : 0 < D' η := hD' η ⟨hη.1, hη.2.le.trans hs.2⟩
    have : D s = D' η * s := by rw [hslope, div_mul_cancel₀ _ hs.1.ne']
    rw [this]; exact mul_pos hη' hs.1
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 t) ?_ ?_
  · -- continuity of the quotient on `(0, t]`
    refine ContinuousOn.div (hNc.mono Ioc_subset_Icc_self) (hDc.mono Ioc_subset_Icc_self) ?_
    intro s hs; exact (hDpos s hs).ne'
  · intro s hs
    rw [interior_Ioc] at hs
    have hs' : s ∈ Ioc 0 t := ⟨hs.1, hs.2.le⟩
    have hderiv : HasDerivAt (fun x => N x / D x)
        ((N' s * D s - N s * D' s) / (D s) ^ (2 : ℕ)) s :=
      (hN s hs).div (hD s hs) (hDpos s hs').ne'
    rw [hderiv.deriv]
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (hDpos s hs'))
    have hcross := deriv_cross_lt_of_strictAnti_derivRatio (N := N) (D := D) (N' := N') (D' := D')
      hs.1 hN0 hD0 (hNc.mono (Icc_subset_Icc le_rfl hs.2.le)) (hDc.mono (Icc_subset_Icc le_rfl hs.2.le))
      (fun x hx => hN x ⟨hx.1, hx.2.trans hs.2⟩) (fun x hx => hD x ⟨hx.1, hx.2.trans hs.2⟩)
      (fun x hx => hD' x ⟨hx.1, hx.2.trans hs.2.le⟩) (hanti.mono (Ioc_subset_Ioc le_rfl hs.2.le))
    linarith

/-- The two-point curvature gain `Q(y, x) = 3(c'(x)² − c'(y)²) − 2(c''(x) − c''(y))(c(x) + c(y))`. -/
def twoPointCurvatureGain (c c₁ c₂ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  3 * (c₁ x * c₁ x - c₁ y * c₁ y) - 2 * ((c₂ x - c₂ y) * (c x + c y))

/-- **Two-point curvature gain is nonnegative.**  Hypotheses on `[y, ∞)`: `c` differentiable with
derivative `c₁`, `c₁` with derivative `c₂`, `c₂` with derivative `c₃`; `0 < c`, `0 ≤ c₁`,
`0 ≤ c₂`, and `c c₃ ≤ c₁ c₂` wherever `0 ≤ c₃`. -/
theorem twoPointCurvatureGain_nonneg {c c₁ c₂ c₃ : ℝ → ℝ} {y : ℝ}
    (hc : ∀ x, y ≤ x → HasDerivAt c (c₁ x) x)
    (hc₁ : ∀ x, y ≤ x → HasDerivAt c₁ (c₂ x) x)
    (hc₂ : ∀ x, y ≤ x → HasDerivAt c₂ (c₃ x) x)
    (hpos : ∀ x, y ≤ x → 0 < c x) (h₁ : ∀ x, y ≤ x → 0 ≤ c₁ x) (h₂ : ∀ x, y ≤ x → 0 ≤ c₂ x)
    (hE : ∀ x, y ≤ x → 0 ≤ c₃ x → c x * c₃ x ≤ c₁ x * c₂ x) :
    ∀ x, y ≤ x → 0 ≤ twoPointCurvatureGain c c₁ c₂ y x := by
  -- `c` is monotone on `[y, ∞)`
  have hmono : MonotoneOn c (Ici y) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici y) ?_ ?_ ?_
    · intro x hx; exact (hc x hx).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Ici] at hx; exact (hc x hx.le).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Ici] at hx; rw [(hc x hx.le).deriv]; exact h₁ x hx.le
  have hQmono : MonotoneOn (twoPointCurvatureGain c c₁ c₂ y) (Ici y) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici y) ?_ ?_ ?_
    · intro x hx
      have hd : HasDerivAt (twoPointCurvatureGain c c₁ c₂ y)
          (3 * (2 * c₁ x * c₂ x) - 2 * (c₃ x * (c x + c y) + (c₂ x - c₂ y) * c₁ x)) x := by
        unfold twoPointCurvatureGain
        have h1 := ((hc₁ x hx).mul (hc₁ x hx)).sub_const (c₁ y * c₁ y)
        have h2 := ((hc₂ x hx).sub_const (c₂ y)).mul ((hc x hx).add_const (c y))
        have := (h1.const_mul 3).sub (h2.const_mul 2)
        exact this.congr_deriv (by ring)
      exact hd.continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Ici] at hx
      have hd : HasDerivAt (twoPointCurvatureGain c c₁ c₂ y)
          (3 * (2 * c₁ x * c₂ x) - 2 * (c₃ x * (c x + c y) + (c₂ x - c₂ y) * c₁ x)) x := by
        unfold twoPointCurvatureGain
        have h1 := ((hc₁ x hx.le).mul (hc₁ x hx.le)).sub_const (c₁ y * c₁ y)
        have h2 := ((hc₂ x hx.le).sub_const (c₂ y)).mul ((hc x hx.le).add_const (c y))
        have := (h1.const_mul 3).sub (h2.const_mul 2)
        exact this.congr_deriv (by ring)
      exact hd.differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Ici] at hx
      have hd : HasDerivAt (twoPointCurvatureGain c c₁ c₂ y)
          (3 * (2 * c₁ x * c₂ x) - 2 * (c₃ x * (c x + c y) + (c₂ x - c₂ y) * c₁ x)) x := by
        unfold twoPointCurvatureGain
        have h1 := ((hc₁ x hx.le).mul (hc₁ x hx.le)).sub_const (c₁ y * c₁ y)
        have h2 := ((hc₂ x hx.le).sub_const (c₂ y)).mul ((hc x hx.le).add_const (c y))
        have := (h1.const_mul 3).sub (h2.const_mul 2)
        exact this.congr_deriv (by ring)
      rw [hd.deriv]
      have hcy : c y ≤ c x := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hx.le) hx.le
      have hcyp : 0 < c y := hpos y le_rfl
      have hc₁x := h₁ x hx.le
      have hc₂x := h₂ x hx.le
      have hc₂y := h₂ y le_rfl
      rcases le_or_gt 0 (c₃ x) with h3 | h3
      · have hE' := hE x hx.le h3
        nlinarith [mul_nonneg h3 (sub_nonneg.2 hcy), mul_nonneg hc₁x hc₂y]
      · nlinarith [mul_nonneg hc₁x hc₂x, mul_nonneg hc₁x hc₂y,
          mul_pos (neg_pos.2 h3) (add_pos (hpos x hx.le) hcyp)]
  intro x hx
  have h0 : twoPointCurvatureGain c c₁ c₂ y y = 0 := by
    unfold twoPointCurvatureGain; ring
  have := hQmono (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  rw [h0] at this
  exact this

/-- **Chord bound.**  If `E` is convex on `[0, t]` with `E(0) = 0` (and continuous there), then
`2 ∫₀ᵗ E ≤ t E(t)`. -/
theorem two_mul_integral_le_mul_of_convexOn {E : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hE0 : E 0 = 0)
    (hconv : ConvexOn ℝ (Icc 0 t) E) (hcont : ContinuousOn E (Icc 0 t)) :
    2 * ∫ s in (0 : ℝ)..t, E s ≤ t * E t := by
  have hchord : ∀ s ∈ Icc (0 : ℝ) t, E s ≤ s / t * E t := by
    intro s hs
    have hθ0 : 0 ≤ s / t := div_nonneg hs.1 ht.le
    have hθ1 : s / t ≤ 1 := (div_le_one ht).2 hs.2
    have hab : (1 - s / t) + s / t = 1 := by ring
    have hcv := hconv.2 (Set.left_mem_Icc.2 ht.le) (Set.right_mem_Icc.2 ht.le)
      (sub_nonneg.2 hθ1) hθ0 hab
    simp only [smul_eq_mul, mul_zero, zero_add, hE0] at hcv
    have hst : s / t * t = s := div_mul_cancel₀ s ht.ne'
    rw [hst] at hcv
    linarith
  have hint : (∫ s in (0 : ℝ)..t, E s) ≤ ∫ s in (0 : ℝ)..t, s / t * E t := by
    refine intervalIntegral.integral_mono_on ht.le ?_ ?_ ?_
    · exact hcont.intervalIntegrable_of_Icc ht.le
    · exact (by fun_prop : Continuous fun s : ℝ => s / t * E t).intervalIntegrable _ _
    · exact hchord
  have hval : (∫ s in (0 : ℝ)..t, s / t * E t) = t * E t / 2 := by
    have : (fun s : ℝ => s / t * E t) = fun s => (E t / t) * s := by funext s; ring
    rw [this, intervalIntegral.integral_const_mul, integral_id]
    field_simp; ring
  linarith

end RHTower
