import GaloisForLFunctions.RHTower.XiSliceLargeRadiusArcBounds
import GaloisForLFunctions.RHTower.XiHorizontalSliceTaylorPositivityConverse


/-!
# Route 3 reduced to finitely many slice coefficients per height

The Taylor coefficients `c_n(t)` of `g_t(x) = ξ(½+x+it) ξ(½−x+it)` at `x = 0` are all nonnegative if
and only if the Riemann hypothesis holds.  This file proves that all coefficients of order
`2k ≥ 2 max(K, κ log t)` are positive unconditionally, so that

```
RH  ⟺  ∀ t ≥ 0, ∀ k < max(K, κ log t) :  c_{2k}(t) ≥ 0.
```

The odd coefficients vanish because `g_t` is even, and negative heights are covered by the
conjugate pairing of zeros.  High-order positivity comes in two regimes:

* `κ log t ≤ k ≤ (t log t)/8`, where the saddle radius is at most `t/2`
  (`exists_xiSliceCoeff_pos_window`);
* `k ≥ max(K₀, (t log t)/8)`, where the saddle radius is at least `max(R*, t/5)`.  Here the scale is
  `log R`, the near arc `θ ≤ π/3` is controlled by the Stirling split in `Re ≥ R/4`, and the far arc
  by the crude comparison `Γ(R/4+2)` against `Γ((½+R)/2)` (`exists_xiSliceCoeff_pos_large_order`).

Both regimes share one abstract assembly, `quarter_integral_pos_of_arc_bounds`: saddle-arc bounds
on `[0, 1/4]` and a uniform tail bound on `[1/1000, π/2]` make the quarter-arc integral positive.
-/

open Complex Real Metric intervalIntegral

namespace RHTower

noncomputable section

/-- **Positivity of a quarter-arc integral from saddle-arc bounds.**  Let `S` be continuous on
`[0, π/2]` and suppose that on `[0, 1/4]` it satisfies the two saddle-arc bounds with slope `F₁`,
radius `R` and disc constant `D`, where `(9/10) ℓ ≤ F₁ ≤ 2ℓ`, `0 ≤ D ≤ ℓ`, and that `|S| ≤ E` on
`[1/1000, π/2]`.  If the scales `0 < δ₀ ≤ δ ≤ 1/1000` satisfy `Λδ₀² ≤ 1`, `43Λδ³ ≤ 1/2`,
`(1/1000) exp(−Λδ²/8) ≤ δ₀/20` and `(π/2)E ≤ δ₀/10` (`Λ = Rℓ`), then `∫₀^{π/2} Re S > 0`. -/
theorem quarter_integral_pos_of_arc_bounds {S : ℝ → ℂ} (hSc : Continuous S)
    {R ℓ F₁ D δ₀ δ E : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) (hF₁lo : 9 / 10 * ℓ ≤ F₁)
    (hF₁hi : F₁ ≤ 2 * ℓ) (hD : D ≤ ℓ) (hD0 : 0 ≤ D)
    (hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 →
      ‖S θ‖ ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3) ≤ (S θ).re))
    (htail : ∀ θ : ℝ, 1 / 1000 ≤ θ → θ ≤ Real.pi / 2 → ‖S θ‖ ≤ E)
    (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ : δ ≤ 1 / 1000)
    (hcore : R * ℓ * δ₀ ^ 2 ≤ 1) (hphase : 43 * (R * ℓ) * δ ^ 3 ≤ 1 / 2)
    (hmid : 1 / 1000 * Real.exp (-(R * ℓ) * δ ^ 2 / 8) ≤ δ₀ / 20)
    (hE : Real.pi / 2 * E ≤ δ₀ / 10) :
    0 < ∫ θ in (0 : ℝ)..(Real.pi / 2), (S θ).re := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = R * ℓ := ⟨_, rfl⟩
  rw [← hΛ] at hcore hphase hmid
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  have hF₁0 : 0 ≤ F₁ := by linarith
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => (S θ).re) MeasureTheory.volume a b :=
    fun a b => (Complex.continuous_re.comp hSc).intervalIntegrable a b
  have hpi : (1 / 1000 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  -- core: on `[0, δ]` the phase is at most `1/2`
  have hcoreθ : ∀ θ ∈ Set.Icc 0 δ,
      7 / 8 * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) ≤ (S θ).re := by
    intro θ hθ
    have hθ4 : θ ≤ 1 / 4 := by linarith [hθ.2]
    have hθ3 : θ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ hθ.1 hθ.2 3
    have hθ3' : 0 ≤ θ ^ 3 := pow_nonneg hθ.1 3
    have h1 : |F₁| * R * θ ^ 3 / 6 ≤ Λ / 3 * θ ^ 3 := by
      rw [abs_of_nonneg hF₁0, hΛ]
      have := mul_le_mul_of_nonneg_right hF₁hi (mul_nonneg hR.le hθ3')
      nlinarith
    have h2 : 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * Λ * θ ^ 3 := by
      rw [hΛ]
      have := mul_le_mul_of_nonneg_left hD hR.le
      nlinarith
    have h3 : 43 * Λ * θ ^ 3 ≤ 43 * Λ * δ ^ 3 := by gcongr
    have hc3 : 0 ≤ 128 / 3 * (R * D) * θ ^ 3 := by positivity
    have ha : 0 ≤ |F₁| * R * θ ^ 3 / 6 := by positivity
    set φ := |F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3 with hφdef
    have hφ : φ ≤ 1 / 2 := by rw [hφdef]; linarith
    have hφ0 : 0 ≤ φ := by rw [hφdef]; linarith
    have hlow := (hb θ hθ.1 hθ4).2 (by linarith [Real.pi_gt_three])
    have hcos : 7 / 8 ≤ Real.cos φ := by
      have := Real.one_sub_sq_div_two_le_cos (x := φ); nlinarith
    have hexp : Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2)
        ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3) := by
      apply Real.exp_le_exp.mpr
      have := hφ; rw [hφdef] at this; linarith
    calc 7 / 8 * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2)
        ≤ Real.cos φ * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3) :=
          mul_le_mul hcos hexp (Real.exp_pos _).le (by linarith)
      _ = Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3) * Real.cos φ := by
          ring
      _ ≤ _ := hlow
  have hI1 : 7 / 40 * δ₀ ≤ ∫ θ in (0 : ℝ)..δ₀, (S θ).re := by
    have := intervalIntegral.integral_mono_on hδ₀.le
      (continuous_const.intervalIntegrable 0 δ₀) (hi 0 δ₀)
      (fun θ hθ => (show (7 / 40 : ℝ) ≤ (S θ).re from by
        have hc := hcoreθ θ ⟨hθ.1, hθ.2.trans hδ₀δ⟩
        have hθ2 : θ ^ 2 ≤ δ₀ ^ 2 := pow_le_pow_left₀ hθ.1 hθ.2 2
        have hq : F₁ * R * (1 - Real.cos θ) ≤ 1 := by
          have h1 := one_sub_cos_le_half_sq θ
          have h0 : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
          calc F₁ * R * (1 - Real.cos θ) ≤ (2 * ℓ) * R * (θ ^ 2 / 2) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right hF₁hi hR.le) h1 h0 (by positivity)
            _ = Λ * θ ^ 2 := by rw [hΛ]; ring
            _ ≤ Λ * δ₀ ^ 2 := by gcongr
            _ ≤ 1 := hcore
        have he : 1 / 5 ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) := by
          have h5 := exp_three_halves_le_five
          have : Real.exp (-(3 / 2)) ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) :=
            Real.exp_le_exp.mpr (by linarith)
          rw [Real.exp_neg] at this
          have hpos := Real.exp_pos (3 / 2)
          calc (1 / 5 : ℝ) ≤ (Real.exp (3 / 2))⁻¹ := by
                rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hpos h5
            _ ≤ _ := this
        linarith))
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  have hI2 : 0 ≤ ∫ θ in δ₀..δ, (S θ).re :=
    intervalIntegral.integral_nonneg hδ₀δ (fun θ hθ =>
      le_trans (by positivity) (hcoreθ θ ⟨hδ₀.le.trans hθ.1, hθ.2⟩))
  have hI3 : -(1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) ≤ ∫ θ in δ..(1 / 1000), (S θ).re := by
    have := intervalIntegral.integral_mono_on hδ
      (continuous_const.intervalIntegrable δ (1 / 1000)) (hi δ (1 / 1000))
      (fun θ hθ => (show -Real.exp (-Λ * δ ^ 2 / 8) ≤ (S θ).re from by
        have hθ0 : 0 ≤ θ := hδ₀.le.trans (hδ₀δ.trans hθ.1)
        have hn := (hb θ hθ0 (by linarith [hθ.2])).1
        have hre := neg_abs_le (S θ).re
        have hab := Complex.abs_re_le_norm (S θ)
        have hcos := one_sub_cos_ge_sq_div_five (θ := θ)
          (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_gt_three, hθ.2])
        have h1 : 9 / 10 * ℓ * R * (θ ^ 2 / 5) ≤ F₁ * R * (1 - Real.cos θ) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hF₁lo hR.le) hcos (by positivity)
          nlinarith
        have h2 : 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (R * ℓ) * θ ^ 2 * (1 / 1000) := by
          have : θ ^ 3 = θ ^ 2 * θ := by ring
          rw [this]
          have hDR : R * D ≤ R * ℓ := mul_le_mul_of_nonneg_left hD hR.le
          have hθ2 : 0 ≤ θ ^ 2 := sq_nonneg θ
          calc 128 / 3 * (R * D) * (θ ^ 2 * θ) ≤ 128 / 3 * (R * ℓ) * (θ ^ 2 * θ) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
            _ ≤ 128 / 3 * (R * ℓ) * (θ ^ 2 * (1 / 1000)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left hθ.2 hθ2
            _ = _ := by ring
        have hδθ : δ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (hδ₀.le.trans hδ₀δ) hθ.1 2
        have hexp : Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
            ≤ Real.exp (-Λ * δ ^ 2 / 8) := by
          apply Real.exp_le_exp.mpr; rw [hΛ]
          have hΛθ : 0 ≤ R * ℓ * θ ^ 2 := by positivity
          nlinarith
        linarith))
    have hlen : (1 / 1000 - δ) * -Real.exp (-Λ * δ ^ 2 / 8) ≥ -(1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) := by
      have hδ0 : 0 ≤ δ := hδ₀.le.trans hδ₀δ
      nlinarith [Real.exp_pos (-Λ * δ ^ 2 / 8)]
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hI4 : -(Real.pi / 2 * E) ≤ ∫ θ in (1 / 1000)..(Real.pi / 2), (S θ).re := by
    have := intervalIntegral.integral_mono_on hpi
      (continuous_const.intervalIntegrable (1 / 1000) (Real.pi / 2)) (hi (1 / 1000) (Real.pi / 2))
      (fun θ hθ => (show -E ≤ (S θ).re from by
        have hn := htail θ hθ.1 hθ.2
        have hre := neg_abs_le (S θ).re
        have hab := Complex.abs_re_le_norm (S θ)
        linarith))
    have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (htail (1 / 1000) le_rfl hpi)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    nlinarith [Real.pi_pos]
  have hsplit : ∫ θ in (0 : ℝ)..(Real.pi / 2), (S θ).re
      = (∫ θ in (0 : ℝ)..δ₀, (S θ).re) + (∫ θ in δ₀..δ, (S θ).re)
        + (∫ θ in δ..(1 / 1000), (S θ).re) + ∫ θ in (1 / 1000)..(Real.pi / 2), (S θ).re := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 δ₀) (hi δ₀ δ),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 δ) (hi δ (1 / 1000)),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 (1 / 1000)) (hi (1 / 1000) (Real.pi / 2))]
  rw [hsplit]
  have hmid' : 1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8) ≤ δ₀ / 20 := hmid
  linarith only [hI1, hI2, hI3, hI4, hmid', hE, hδ₀]

/-- **Tail of a large circle.**  For `R ≥ R₁` (far-arc threshold), `R ≥ 8`, `0 ≤ t ≤ 5R`,
`log(R/4π) ≥ 0` and `1/1000 ≤ θ ≤ π/2`:
`|S(θ)| ≤ 16e^{31} exp(−R log(R/4π)/(5·10⁶)) + exp(−(R/8) log R)`. -/
theorem sliceArc_norm_tail_large {R₁ : ℝ}
    (hfar : ∀ R t θ : ℝ, R₁ ≤ R → 0 ≤ t → t ≤ 5 * R → Real.pi / 3 ≤ θ → θ ≤ Real.pi / 2 →
      ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
        ≤ ‖xiSliceProduct t (R : ℂ)‖ * Real.exp (-(R / 8) * Real.log R))
    {t R θ : ℝ} (k : ℕ) (hR1 : R₁ ≤ R) (hR : 8 ≤ R) (ht0 : 0 ≤ t) (htR : t ≤ 5 * R)
    (hlog : 0 ≤ Real.log (R / (4 * Real.pi))) (hθ1 : 1 / 1000 ≤ θ) (hθ2 : θ ≤ Real.pi / 2) :
    ‖sliceArc t R k θ‖ ≤ 16 * Real.exp 31 * Real.exp (-(R * Real.log (R / (4 * Real.pi))) / 5000000)
      + Real.exp (-(R / 8) * Real.log R) := by
  have hgR : 0 < ‖xiSliceProduct t (R : ℂ)‖ :=
    norm_pos_iff.mpr (xiSliceProduct_ne_zero_of_re (by simp; linarith))
  rw [norm_sliceArc_eq, div_le_iff₀ hgR]
  have h1pos : 0 ≤ 16 * Real.exp 31 * Real.exp (-(R * Real.log (R / (4 * Real.pi))) / 5000000) := by
    positivity
  have h2pos : 0 ≤ Real.exp (-(R / 8) * Real.log R) := (Real.exp_pos _).le
  rcases le_or_gt θ (Real.pi / 3) with hθ | hθ
  · have hb := norm_xiSliceProduct_circle_le_large (t := t) hR (by linarith) hθ
    have hθ0 : 0 ≤ θ := by linarith
    have hc := one_sub_cos_ge_sq_div_five (θ := θ)
      (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_pos])
    have hθsq : (1 / 1000 : ℝ) ^ 2 ≤ θ ^ 2 := by gcongr
    have hcos1 : 1 - Real.cos θ ≤ 1 / 2 := by
      have : Real.cos (Real.pi / 3) ≤ Real.cos θ :=
        Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos]) hθ
      rw [Real.cos_pi_div_three] at this; linarith
    have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hθπ : θ ≤ 21 / 20 := by linarith [Real.pi_lt_d2]
    have hgain : R * Real.log (R / (4 * Real.pi)) / 5000000
        ≤ R * (1 - Real.cos θ) * Real.log (R / (4 * Real.pi)) := by
      have h1 : 1 / 5000000 ≤ 1 - Real.cos θ := by nlinarith
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ R))
        hlog
      linarith
    have hexp : Real.exp (-(R * (1 - Real.cos θ)) * Real.log (R / (4 * Real.pi))
          + 12 * (1 - Real.cos θ + Real.sin θ) + 6 * θ)
        ≤ Real.exp 31 * Real.exp (-(R * Real.log (R / (4 * Real.pi))) / 5000000) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have e1 : -(R * (1 - Real.cos θ)) * Real.log (R / (4 * Real.pi))
          = -(R * (1 - Real.cos θ) * Real.log (R / (4 * Real.pi))) := by ring
      have e2 : -(R * Real.log (R / (4 * Real.pi))) / 5000000
          = -(R * Real.log (R / (4 * Real.pi)) / 5000000) := by ring
      rw [e1, e2]
      linarith
    calc ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
        ≤ ‖xiSliceProduct t (R : ℂ)‖ * 16 * Real.exp (-(R * (1 - Real.cos θ))
            * Real.log (R / (4 * Real.pi)) + 12 * (1 - Real.cos θ + Real.sin θ) + 6 * θ) := hb
      _ ≤ ‖xiSliceProduct t (R : ℂ)‖ * 16
            * (Real.exp 31 * Real.exp (-(R * Real.log (R / (4 * Real.pi))) / 5000000)) := by gcongr
      _ ≤ _ := by nlinarith
  · have hb := hfar R t θ hR1 ht0 htR hθ.le hθ2
    calc ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
        ≤ ‖xiSliceProduct t (R : ℂ)‖ * Real.exp (-(R / 8) * Real.log R) := hb
      _ ≤ _ := by nlinarith

/-- **Saddle radius on large circles.** -/
theorem exists_saddle_radius_large {t a b : ℝ} (ht0 : 0 ≤ t) (ha8 : 8 ≤ a) (hab : a ≤ b)
    (hta : t ≤ 5 * a) {k : ℕ}
    (hlo : a * (Real.log (4 * a) + 2 * xiLogDerivStirlingConstant) ≤ 2 * (k : ℝ))
    (hhi : 2 * (k : ℝ) ≤ b * (Real.log (b / 2) - 2 * xiLogDerivStirlingConstant)) :
    ∃ R ∈ Set.Icc a b, (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * (k : ℝ) := by
  set φ : ℝ → ℝ := fun R => R * (xiSliceLogDeriv t R).re with hφ
  have hcont : ContinuousOn φ (Set.Icc a b) := by
    have hL : ContinuousOn (fun R : ℝ => xiSliceLogDeriv t (R : ℂ)) (Set.Icc a b) := by
      refine (differentiableOn_xiSliceLogDeriv t).continuousOn.comp
        Complex.continuous_ofReal.continuousOn ?_
      intro R hR
      show 1 / 2 < ((R : ℂ)).re
      simp; linarith [hR.1]
    exact continuousOn_id.mul (Complex.continuous_re.comp_continuousOn hL)
  have ha : φ a ≤ 2 * k := by
    obtain ⟨-, -, hhia⟩ := xiSliceLogDeriv_real_bounds_large (t := t) ha8 ht0 hta
    simp only [hφ]
    have := mul_le_mul_of_nonneg_left hhia (by linarith : (0 : ℝ) ≤ a)
    linarith
  have hb : 2 * k ≤ φ b := by
    obtain ⟨-, hlob, -⟩ := xiSliceLogDeriv_real_bounds_large (t := t) (R := b) (by linarith) ht0
      (by linarith)
    simp only [hφ]
    have := mul_le_mul_of_nonneg_left hlob (by linarith : (0 : ℝ) ≤ b)
    linarith
  obtain ⟨R, hR, hRk⟩ := intermediate_value_Icc hab hcont ⟨ha, hb⟩
  refine ⟨R, hR, ?_⟩
  rw [re_scaledLogDeriv_xiSliceProduct_ofReal (by linarith [hR.1])]
  exact hRk

open scoped ComplexOrder in
/-- **Large-order positivity of the slice coefficients.**  There is `K₀` such that for every height
`t ≥ 0` and every `k ≥ K₀` with `k ≥ (t log t)/8`, the Taylor coefficient `c_{2k}(t)` is strictly
positive.  The saddle radius is then at least `max(R*, t/5)`, the scale is `log R`, and the
quarter-arc integral is positive by the saddle-arc bounds on the disc `|w − R| ≤ R/2`, the near-arc
decay for `θ ≤ π/3` and the far-arc decay `exp(−(R/8) log R)` beyond. -/
theorem exists_xiSliceCoeff_pos_large_order :
    ∃ K₀ : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, K₀ ≤ k → t * Real.log t / 8 ≤ k →
      0 < xiSliceCoeff t (2 * k) := by
  obtain ⟨C, hC⟩ : ∃ C, C = xiLogDerivStirlingConstant := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = Real.log 16 + Real.pi + 4 * C := ⟨_, rfl⟩
  have hC0 : 0 < C := hC ▸ xiLogDerivStirlingConstant_pos
  have hl16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hpi0 := Real.pi_pos
  have hB0 : 0 < B := by rw [hB]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl4pi : 0 < Real.log (4 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  -- thresholds in `Λ`
  have e1 := (tendsto_order.1 tendsto_rpow_half_mul_exp_neg_fifth_root).2 50 (by norm_num)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2
    (1 / 1000) (by norm_num)
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (1 / 86) (by norm_num)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and e4))
  -- thresholds in `R` for the tail
  have r1 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 5000000)
    (by norm_num))).2 (1 / (10 * Real.pi * (16 * Real.exp 31))) (by positivity)
  have r2 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 8)
    (by norm_num))).2 (1 / (10 * Real.pi)) (by positivity)
  obtain ⟨Rr, hRr⟩ := Filter.eventually_atTop.mp (r1.and r2)
  obtain ⟨R₁, hR₁8, hfar⟩ := exists_far_arc_bound_large
  obtain ⟨L, hL⟩ : ∃ L, L = 10 * (Real.log 2 + Real.log 4 + Real.pi / 2 + 2 * C + 2 * B + 1
    + Real.log (4 * Real.pi)) + 8 * C := ⟨_, rfl⟩
  have hL10 : 10 ≤ L := by rw [hL]; linarith only [hl2, hl4, hpi0, hC0, hB0, hl4pi]
  obtain ⟨Rs, hRs⟩ : ∃ Rs, Rs = max (max (max 8 R₁) (max Λ₀ Rr)) (Real.exp L) := ⟨_, rfl⟩
  have hRs8 : 8 ≤ Rs := by
    rw [hRs]; apply le_max_of_le_left; apply le_max_of_le_left; exact le_max_left _ _
  have hRsR₁ : R₁ ≤ Rs := by
    rw [hRs]; apply le_max_of_le_left; apply le_max_of_le_left; exact le_max_right _ _
  have hRsΛ : Λ₀ ≤ Rs := by
    rw [hRs]; apply le_max_of_le_left; apply le_max_of_le_right; exact le_max_left _ _
  have hRsr : Rr ≤ Rs := by
    rw [hRs]; apply le_max_of_le_left; apply le_max_of_le_right; exact le_max_right _ _
  have hRsL : Real.exp L ≤ Rs := by rw [hRs]; exact le_max_right _ _
  have hlogRs : L ≤ Real.log Rs := by
    rw [← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) hRsL
  refine ⟨Rs * (Real.log (4 * Rs) + 2 * C) + Real.exp (1 + 2 * C) + 1, ?_⟩
  intro t ht0 k hkK hkt
  have hRs0 : 0 < Rs := by linarith
  have hlog4Rs : 1 ≤ Real.log (4 * Rs) := by
    have := Real.log_le_log (by positivity) (show Rs ≤ 4 * Rs by linarith)
    linarith only [this, hlogRs, hL10]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkRs : Rs ≤ k := by
    have : Rs ≤ Rs * (Real.log (4 * Rs) + 2 * C) := by nlinarith
    linarith only [this, hkK, Real.exp_pos (1 + 2 * C)]
  have hkexp : Real.exp (1 + 2 * C) ≤ k := by
    have : 0 ≤ Rs * (Real.log (4 * Rs) + 2 * C) := by positivity
    linarith only [this, hkK]
  have hk1 : 0 < (k : ℝ) := by linarith only [hkexp, Real.exp_pos (1 + 2 * C)]
  have hlogk : 1 + 2 * C ≤ Real.log k := by
    rw [← Real.log_exp (1 + 2 * C)]; exact Real.log_le_log (Real.exp_pos _) hkexp
  -- the saddle radius
  obtain ⟨a, ha⟩ : ∃ a, a = max Rs (t / 5) := ⟨_, rfl⟩
  have haRs : Rs ≤ a := by rw [ha]; exact le_max_left _ _
  have hat : t / 5 ≤ a := by rw [ha]; exact le_max_right _ _
  have ha8 : 8 ≤ a := by linarith
  have hlo : a * (Real.log (4 * a) + 2 * xiLogDerivStirlingConstant) ≤ 2 * (k : ℝ) := by
    rw [← hC]
    rcases le_total (t / 5) Rs with h | h
    · have : a = Rs := by rw [ha]; exact max_eq_left h
      rw [this]; linarith only [hkK, Real.exp_pos (1 + 2 * C), hk0]
    · have hat' : a = t / 5 := by rw [ha]; exact max_eq_right h
      rw [hat']
      have ht5 : 5 * Rs ≤ t := by linarith
      have hlogt : L ≤ Real.log t := le_trans hlogRs (Real.log_le_log hRs0 (by linarith))
      have ht0' : 0 < t := by linarith
      have h1 : Real.log (4 * (t / 5)) ≤ Real.log t :=
        Real.log_le_log (by linarith only [ht0']) (by linarith only [ht0'])
      have h2 : Real.log (4 * (t / 5)) + 2 * C ≤ 5 / 4 * Real.log t := by
        rw [hL] at hlogt; linarith only [h1, hlogt, hl2, hl4, hpi0, hC0, hB0, hl4pi]
      have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ t / 5)
      linarith only [h3, hkt]
  have hab : a ≤ 2 * (k : ℝ) := by
    rcases le_total (t / 5) Rs with h | h
    · have : a = Rs := by rw [ha]; exact max_eq_left h
      rw [this]; linarith only [hkRs, hk0]
    · have hat' : a = t / 5 := by rw [ha]; exact max_eq_right h
      rw [hat']
      have hlogt : 1 ≤ Real.log t :=
        le_trans (by linarith only [hL10]) (le_trans hlogRs (Real.log_le_log hRs0 (by linarith)))
      have := mul_le_mul_of_nonneg_left hlogt (by linarith : (0 : ℝ) ≤ t)
      linarith only [this, hkt]
  have hhi : 2 * (k : ℝ) ≤ 2 * k * (Real.log (2 * k / 2) - 2 * xiLogDerivStirlingConstant) := by
    rw [← hC, show 2 * (k : ℝ) / 2 = k by ring]
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Real.log k - 2 * C by linarith only [hlogk])
      (by linarith : (0 : ℝ) ≤ 2 * k)
    linarith only [this]
  obtain ⟨R, ⟨haR, hRk⟩, hsad⟩ := exists_saddle_radius_large ht0 ha8 hab (by linarith) hlo hhi
  have hR8 : 8 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have htR : t ≤ 5 * R := by linarith
  have hRRs : Rs ≤ R := by linarith
  have hlogR : L ≤ Real.log R := le_trans hlogRs (Real.log_le_log hRs0 hRRs)
  have hlogR1 : 1 ≤ Real.log R := by linarith only [hlogR, hL10]
  have hlogRR : Real.log R ≤ R := by linarith [Real.log_le_sub_one_of_pos hR0]
  -- the scale
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = R * Real.log R := ⟨_, rfl⟩
  have hΛR : R ≤ Λ := by
    rw [hΛ]; have := mul_le_mul_of_nonneg_left hlogR1 hR0.le; linarith only [this]
  have hΛ0 : 0 < Λ := by linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  obtain ⟨hE1, hE3, hE4⟩ := hΛ₀ Λ (by linarith)
  -- slope and disc constant
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSlice_saddleSlope_bounds_large hR8 ht0 htR
  rw [← hC] at hF₁lo hF₁hi
  rw [← hB] at hF₁lo hF₁hi
  have hl2R : Real.log (R / 2) = Real.log R - Real.log 2 := Real.log_div hR0.ne' (by norm_num)
  have hl4R : Real.log (4 * R) = Real.log 4 + Real.log R := Real.log_mul (by norm_num) hR0.ne'
  have hF₁lo' : 9 / 10 * Real.log R
      ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re := by
    rw [hl2R] at hF₁lo; rw [hL] at hlogR
    linarith only [hF₁lo, hlogR, hl2, hl4, hpi0, hC0, hB0, hl4pi]
  have hF₁hi' : (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
      ≤ 2 * Real.log R := by
    rw [hl4R] at hF₁hi; rw [hL] at hlogR
    linarith only [hF₁hi, hlogR, hl2, hl4, hpi0, hC0, hB0, hl4pi]
  have hD : xiSliceDiscConstantLarge R ≤ Real.log R := by
    unfold xiSliceDiscConstantLarge
    rw [hl4R, ← hC]
    have : Real.log 16 + Real.pi + 4 * C = B := hB.symm
    rw [this]; rw [hL] at hlogR
    linarith only [hlogR, hl2, hl4, hpi0, hC0, hB0, hl4pi]
  have hD0 : 0 ≤ xiSliceDiscConstantLarge R := by
    unfold xiSliceDiscConstantLarge
    have : 0 ≤ Real.log (4 * R) := Real.log_nonneg (by linarith)
    have := xiLogDerivStirlingConstant_pos
    positivity
  have hlog4pi : 1 ≤ Real.log (R / (4 * Real.pi)) := by
    rw [Real.log_div hR0.ne' (by positivity)]; rw [hL] at hlogR
    linarith only [hlogR, hl2, hl4, hpi0, hC0, hB0, hl4pi]
  -- the scales
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, δ₀ = Λ ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = Λ ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  have hδ₀pos : 0 < δ₀ := hδ₀ ▸ Real.rpow_pos_of_pos hΛ0 _
  have hδ₀δ : δ₀ ≤ δ := by
    rw [hδ₀, hδ]; exact Real.rpow_le_rpow_of_exponent_le hΛ1 (by norm_num)
  have hδ1000 : δ ≤ 1 / 1000 := hδ ▸ hE3.le
  have hcore : R * Real.log R * δ₀ ^ 2 ≤ 1 := by
    rw [← hΛ, hδ₀]; exact (mul_rpow_neg_half_sq hΛ0).le
  have hphase : 43 * (R * Real.log R) * δ ^ 3 ≤ 1 / 2 := by
    have := mul_rpow_neg_two_fifths_cube hΛ0
    rw [← hΛ, hδ, mul_assoc, this]; linarith only [hE4]
  have hhalf : Λ ^ (1 / 2 : ℝ) * δ₀ = 1 := by rw [hδ₀]; exact rpow_half_mul_rpow_neg_half_eq_one hΛ0
  have hmid : 1 / 1000 * Real.exp (-(R * Real.log R) * δ ^ 2 / 8) ≤ δ₀ / 20 := by
    have e : -(R * Real.log R) * δ ^ 2 / 8 = -(Λ ^ (1 / 5 : ℝ)) / 8 := by
      rw [← hΛ, hδ, ← mul_rpow_neg_two_fifths_sq hΛ0]; ring
    rw [e]
    have h1 : Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) ≤ 50 * δ₀ := by
      calc Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8)
          = Λ ^ (1 / 2 : ℝ) * Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) * δ₀ := by
            rw [mul_comm (Λ ^ (1 / 2 : ℝ)), mul_assoc, hhalf, mul_one]
        _ ≤ 50 * δ₀ := by gcongr
    linarith only [h1]
  -- the tail
  obtain ⟨E, hE⟩ : ∃ E, E = 16 * Real.exp 31
      * Real.exp (-(R * Real.log (R / (4 * Real.pi))) / 5000000) + Real.exp (-(R / 8) * Real.log R) :=
    ⟨_, rfl⟩
  have htail : ∀ θ : ℝ, 1 / 1000 ≤ θ → θ ≤ Real.pi / 2 → ‖sliceArc t R k θ‖ ≤ E := by
    intro θ h1 h2
    rw [hE]; exact sliceArc_norm_tail_large hfar k (by linarith) hR8 ht0 htR (by linarith) h1 h2
  have hEle : Real.pi / 2 * E ≤ δ₀ / 10 := by
    obtain ⟨hr1, hr2⟩ := hRr R (by linarith)
    rw [Real.rpow_one] at hr1 hr2
    have hx1 : Real.exp (-(R * Real.log (R / (4 * Real.pi))) / 5000000)
        ≤ Real.exp (-(1 / 5000000) * R) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hlog4pi hR0.le
      linarith only [this]
    have hx2 : Real.exp (-(R / 8) * Real.log R) ≤ Real.exp (-(1 / 8) * R) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hlogR1 hR0.le
      linarith only [this]
    have hRE : R * E ≤ 1 / (5 * Real.pi) := by
      rw [hE]
      have h16 : 0 < 16 * Real.exp 31 := by positivity
      have hA : R * (16 * Real.exp 31 * Real.exp (-(R * Real.log (R / (4 * Real.pi))) / 5000000))
          ≤ 16 * Real.exp 31 * (1 / (10 * Real.pi * (16 * Real.exp 31))) := by
        calc R * (16 * Real.exp 31 * Real.exp (-(R * Real.log (R / (4 * Real.pi))) / 5000000))
            = 16 * Real.exp 31 * (R * Real.exp (-(R * Real.log (R / (4 * Real.pi))) / 5000000)) := by
              ring
          _ ≤ 16 * Real.exp 31 * (R * Real.exp (-(1 / 5000000) * R)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx1 hR0.le) h16.le
          _ ≤ _ := mul_le_mul_of_nonneg_left hr1.le h16.le
      have hA' : 16 * Real.exp 31 * (1 / (10 * Real.pi * (16 * Real.exp 31))) = 1 / (10 * Real.pi) := by
        field_simp
      have hB' : R * Real.exp (-(R / 8) * Real.log R) ≤ 1 / (10 * Real.pi) := by
        have := mul_le_mul_of_nonneg_left hx2 hR0.le
        linarith only [this, hr2]
      have : 1 / (10 * Real.pi) + 1 / (10 * Real.pi) = 1 / (5 * Real.pi) := by field_simp; ring
      rw [mul_add]; linarith only [hA, hA', hB', this]
    have hδR : 1 / R ≤ δ₀ := by
      have hΛR2 : Λ ≤ R ^ 2 := by
        rw [hΛ]; have := mul_le_mul_of_nonneg_left hlogRR hR0.le; nlinarith only [this]
      have := Real.rpow_le_rpow_of_nonpos hΛ0 hΛR2 (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
      rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le] at this
      norm_num at this
      rw [Real.rpow_neg_one] at this
      rw [one_div, hδ₀]; exact this
    have hE0 : 0 ≤ E := by rw [hE]; positivity
    have h1 : E ≤ 1 / (5 * Real.pi) / R := by rw [le_div_iff₀ hR0, mul_comm]; exact hRE
    calc Real.pi / 2 * E ≤ Real.pi / 2 * (1 / (5 * Real.pi) / R) := by gcongr
      _ = 1 / R / 10 := by field_simp; ring
      _ ≤ δ₀ / 10 := by linarith only [hδR]
  -- the bundle
  have hbundle : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 →
      ‖sliceArc t R k θ‖ ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
          * R * (1 - Real.cos θ)) + 128 / 3 * (R * xiSliceDiscConstantLarge R) * θ ^ 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
          + 128 / 3 * (R * xiSliceDiscConstantLarge R) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) - 128 / 3 * (R * xiSliceDiscConstantLarge R) * θ ^ 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 128 / 3 * (R * xiSliceDiscConstantLarge R) * θ ^ 3) ≤ (sliceArc t R k θ).re) := by
    intro θ h0 h1
    have hb := xiSlice_saddleArc_bounds_large hR8 ht0 htR h0 h1
    rw [hsad, saddle_cubic_coeff_eq hR0] at hb
    exact hb
  have hSc : Continuous fun θ : ℝ => sliceArc t R k θ := by
    have hg := differentiable_xiSliceProduct t
    have : Continuous fun θ : ℝ => xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    simp only [sliceArc, HTGeometry.saddleArc]
    fun_prop
  have hpos := quarter_integral_pos_of_arc_bounds hSc hR0 (by linarith : 0 < Real.log R)
    hF₁lo' hF₁hi' hD hD0 hbundle htail hδ₀pos hδ₀δ hδ1000 hcore hphase hmid hEle
  rw [xiSliceCoeff_two_mul_eq_quarter t k (by linarith : (1 : ℝ) / 2 < R), Complex.zero_lt_real]
  have hxi : 0 < ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by simp; linarith))
  have hfac : 0 < 2 * ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ (2 * k)) := by
    positivity
  exact mul_pos hfac hpos

/-! ## The reduction of route 3 to finitely many coefficients per height -/

open scoped ComplexOrder

/-- The slice product is even, so its odd Taylor coefficients vanish. -/
theorem xiSliceCoeff_odd_eq_zero (t : ℝ) (k : ℕ) : xiSliceCoeff t (2 * k + 1) = 0 := by
  unfold xiSliceCoeff
  have h := iteratedDeriv_comp_neg (2 * k + 1) (xiSliceProduct t) 0
  have heven : (fun x => xiSliceProduct t (-x)) = xiSliceProduct t := by
    funext x; exact xiSliceProduct_neg t x
  rw [heven, neg_zero, pow_succ, pow_mul] at h
  simp only [neg_one_sq, one_pow, one_mul, neg_smul, one_smul] at h
  have h0 : iteratedDeriv (2 * k + 1) (xiSliceProduct t) 0 = 0 := by
    have := h; linear_combination (1 / 2 : ℂ) * this
  rw [h0, mul_zero]

/-- `t ↦ t log t` is bounded by its value at `T ≥ 1` on `[0, T]`. -/
theorem mul_log_le_of_le {t T : ℝ} (ht : 0 ≤ t) (hT : 1 ≤ T) (htT : t ≤ T) :
    t * Real.log t ≤ T * Real.log T := by
  rcases le_or_gt t 1 with h1 | h1
  · have : Real.log t ≤ 0 := Real.log_nonpos ht h1
    have : t * Real.log t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht this
    have : 0 ≤ T * Real.log T := mul_nonneg (by linarith) (Real.log_nonneg hT)
    linarith
  · have hl : Real.log t ≤ Real.log T := Real.log_le_log (by linarith) htT
    have hl0 : 0 ≤ Real.log t := Real.log_nonneg h1.le
    exact mul_le_mul htT hl hl0 (by linarith)

/-- **High-order positivity at every height.**  There are constants `K` and `κ` such that for every
height `t ≥ 0` and every `k ≥ max(K, κ log t)` the coefficient `c_{2k}(t)` is strictly positive. -/
theorem exists_xiSliceCoeff_pos_high_order :
    ∃ K κ : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, max K (κ * Real.log t) ≤ k →
      0 < xiSliceCoeff t (2 * k) := by
  obtain ⟨t₀, κ, hwin⟩ := exists_xiSliceCoeff_pos_window
  obtain ⟨K₀, hlarge⟩ := exists_xiSliceCoeff_pos_large_order
  set T := max t₀ 1 with hT
  have hT1 : 1 ≤ T := le_max_right _ _
  refine ⟨max K₀ (T * Real.log T / 8 + 1), max κ 0, ?_⟩
  intro t ht0 k hk
  have hkK : max K₀ (T * Real.log T / 8 + 1) ≤ k := le_trans (le_max_left _ _) hk
  have hkκ : max κ 0 * Real.log t ≤ k := le_trans (le_max_right _ _) hk
  have hkK₀ : K₀ ≤ k := le_trans (le_max_left _ _) hkK
  have hkT : T * Real.log T / 8 + 1 ≤ k := le_trans (le_max_right _ _) hkK
  rcases le_or_gt (t * Real.log t / 8) k with hbig | hsmall
  · exact hlarge t ht0 k hkK₀ hbig
  · -- then `t > T`, so the window applies
    have htT : T < t := by
      by_contra h; push Not at h
      have := mul_log_le_of_le ht0 hT1 h
      linarith
    have ht₀ : t₀ ≤ t := le_trans (le_max_left _ _) htT.le
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hκ : κ * Real.log t ≤ k :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogt) hkκ
    exact hwin t ht₀ k hκ hsmall.le

/-- Taylor positivity at nonnegative heights suffices: zeros of `ξ` come in conjugate pairs. -/
theorem riemannHypothesis_of_xiSliceCoeff_nonneg_of_nonneg_height
    (h : ∀ t : ℝ, 0 ≤ t → ∀ n, 0 ≤ xiSliceCoeff t n) : RiemannHypothesis := by
  refine riemannHypothesis_iff_xi_zero_re_eq_half.mpr fun ρ hρ => ?_
  rcases le_or_gt 0 ρ.im with him | him
  · exact re_eq_half_of_xiSliceCoeff_nonneg (h ρ.im him) hρ rfl
  · have hc : xi ((starRingEnd ℂ) ρ) = 0 := by rw [xi_conj, hρ, map_zero]
    have := re_eq_half_of_xiSliceCoeff_nonneg (h ((starRingEnd ℂ) ρ).im
      (by rw [Complex.conj_im]; linarith)) hc rfl
    simpa using this

/-- **Route 3 reduced to `O(log t)` coefficients per height.**  There are constants `K` and `κ`
such that the Riemann hypothesis is equivalent to the nonnegativity, at every height `t ≥ 0`, of the
finitely many even Taylor coefficients `c_{2k}(t)` with `k < max(K, κ log t)` of
`g_t(x) = ξ(½+x+it) ξ(½−x+it)`.  All higher coefficients are positive unconditionally. -/
theorem exists_riemannHypothesis_iff_low_order_xiSliceCoeff_nonneg :
    ∃ K κ : ℝ, (RiemannHypothesis ↔
      ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, (k : ℝ) < max K (κ * Real.log t) → 0 ≤ xiSliceCoeff t (2 * k)) := by
  obtain ⟨K, κ, hpos⟩ := exists_xiSliceCoeff_pos_high_order
  refine ⟨K, κ, ⟨fun hRH t _ k _ => xiSliceCoeff_nonneg_of_riemannHypothesis hRH t (2 * k),
    fun hlow => riemannHypothesis_of_xiSliceCoeff_nonneg_of_nonneg_height fun t ht n => ?_⟩⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases lt_or_ge (k : ℝ) (max K (κ * Real.log t)) with hk | hk
    · exact hlow t ht k hk
    · exact (hpos t ht k hk).le
  · rw [xiSliceCoeff_odd_eq_zero]

/-- **Finite-order falsification certificate.**  There are `K` and `κ` such that the Riemann
hypothesis fails if and only if at some height `t ≥ 0` some slice coefficient of order
`2k < 2 max(K, κ log t)` leaves the nonnegative cone. -/
theorem exists_not_riemannHypothesis_iff_low_order_xiSliceCoeff_not_nonneg :
    ∃ K κ : ℝ, (¬ RiemannHypothesis ↔
      ∃ t : ℝ, 0 ≤ t ∧ ∃ k : ℕ, (k : ℝ) < max K (κ * Real.log t) ∧ ¬ 0 ≤ xiSliceCoeff t (2 * k)) := by
  obtain ⟨K, κ, h⟩ := exists_riemannHypothesis_iff_low_order_xiSliceCoeff_nonneg
  refine ⟨K, κ, ?_⟩
  rw [h]
  push Not
  rfl

end

end RHTower
