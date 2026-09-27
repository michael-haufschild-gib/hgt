import GaloisForLFunctions.RHTower.XiSliceFiniteOrderReduction
import GaloisForLFunctions.RHTower.XiSliceSaddleArcBoundsEulerRegion
import GaloisForLFunctions.RHTower.XiSliceArcTailConvexity

/-!
# Positivity of the slice coefficients above the quarter-log edge

Let `c_n(t)` be the Taylor coefficients of `g_t(x) = ξ(½+x+it) ξ(½−x+it)` at `x = 0`.  For every
`ε > 0` there is `K` such that

```
∀ t ≥ 0, ∀ k ≥ max(K, (¼ + ε) log t) :  c_{2k}(t) > 0,
```

so that the Riemann hypothesis is equivalent to `c_{2k}(t) ≥ 0` for `k < max(K, (¼ + ε) log t)`.

The saddle radius `R` of the order `2k` satisfies `2k ≈ R log t`, so `k ≥ (¼ + ε) log t` puts the
saddle circle at radius `R ≥ ½ + 2η`.  There the saddle disc of radius `η` keeps both points
`½ + w ± it` in the Euler half-plane `Re ≥ 1 + η` (`XiSliceSaddleArcBoundsEulerRegion`), and the
far arc is controlled by the convexity bound `‖ζ(σ + it)‖ ≪ t^{(1+η−σ)/2}`
(`XiSliceArcTailConvexity`): the arc points inside the strip lose `t^{½+η−R cos θ}` in `ζ` and gain
`t^{−(R − R cos θ)}` in the Gamma factors, leaving `t^{−η}`.

The disc constant is now of size `(R/η) log t` rather than `log t`, so the quarter-arc assembly is
run with a scale factor `K = R₁/(2η)`: the saddle-arc bounds are used on `θ ≤ 1/(1000K)` and the tail
bound from there on (`quarter_integral_pos_of_arc_bounds_scaled`).
-/

open Complex Real Metric intervalIntegral
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **Quarter-arc positivity with a scale factor.**  As `quarter_integral_pos_of_arc_bounds`, with
the disc constant `D ≤ Kℓ` for some `K ≥ 1`: the saddle-arc bounds are required on
`[0, 1/(1000K)]`, the tail bound on `[1/(1000K), π/2]`, and the phase condition becomes
`(1 + 128K) Λ δ³ ≤ 3/2`. -/
theorem quarter_integral_pos_of_arc_bounds_scaled {S : ℝ → ℂ} (hSc : Continuous S)
    {R ℓ F₁ D K δ₀ δ E : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) (hK : 1 ≤ K) (hF₁lo : 9 / 10 * ℓ ≤ F₁)
    (hF₁hi : F₁ ≤ 2 * ℓ) (hD : D ≤ K * ℓ) (hD0 : 0 ≤ D)
    (hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / (1000 * K) →
      ‖S θ‖ ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3) ≤ (S θ).re))
    (htail : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi / 2 → ‖S θ‖ ≤ E)
    (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ : δ ≤ 1 / (1000 * K))
    (hcore : R * ℓ * δ₀ ^ 2 ≤ 1) (hphase : (1 + 128 * K) * (R * ℓ) * δ ^ 3 ≤ 3 / 2)
    (hmid : 1 / 1000 * Real.exp (-(R * ℓ) * δ ^ 2 / 8) ≤ δ₀ / 20)
    (hE : Real.pi / 2 * E ≤ δ₀ / 10) :
    0 < ∫ θ in (0 : ℝ)..(Real.pi / 2), (S θ).re := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = R * ℓ := ⟨_, rfl⟩
  rw [← hΛ] at hcore hphase hmid
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  have hF₁0 : 0 ≤ F₁ := by linarith
  have hK0 : 0 < K := by linarith
  obtain ⟨θK, hθK⟩ : ∃ θK : ℝ, θK = 1 / (1000 * K) := ⟨_, rfl⟩
  rw [← hθK] at hb htail hδ
  have hθK0 : 0 < θK := by rw [hθK]; positivity
  have hθK1 : θK ≤ 1 / 1000 := by
    rw [hθK]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hKθK : K * θK = 1 / 1000 := by rw [hθK]; field_simp
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => (S θ).re) MeasureTheory.volume a b :=
    fun a b => (Complex.continuous_re.comp hSc).intervalIntegrable a b
  have hpi : θK ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  -- core: on `[0, δ]` the phase is at most `1/2`
  have hcoreθ : ∀ θ ∈ Set.Icc 0 δ,
      7 / 8 * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) ≤ (S θ).re := by
    intro θ hθ
    have hθ4 : θ ≤ θK := hθ.2.trans hδ
    have hθ3 : θ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ hθ.1 hθ.2 3
    have hθ3' : 0 ≤ θ ^ 3 := pow_nonneg hθ.1 3
    have h1 : |F₁| * R * θ ^ 3 / 6 ≤ Λ / 3 * θ ^ 3 := by
      rw [abs_of_nonneg hF₁0, hΛ]
      have := mul_le_mul_of_nonneg_right hF₁hi (mul_nonneg hR.le hθ3')
      linarith
    have h2 : 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (K * Λ) * θ ^ 3 := by
      rw [hΛ]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hR.le) hθ3'
      linarith
    have h3 : (1 + 128 * K) * Λ * θ ^ 3 ≤ (1 + 128 * K) * Λ * δ ^ 3 :=
      mul_le_mul_of_nonneg_left hθ3 (by positivity)
    have hc3 : 0 ≤ 128 / 3 * (R * D) * θ ^ 3 := by positivity
    have ha : 0 ≤ |F₁| * R * θ ^ 3 / 6 := by positivity
    set φ := |F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3 with hφdef
    have hφ : φ ≤ 1 / 2 := by rw [hφdef]; linarith
    have hφ0 : 0 ≤ φ := by rw [hφdef]; linarith
    have hlow := (hb θ hθ.1 hθ4).2 (by linarith [Real.pi_gt_three])
    have hcos : 7 / 8 ≤ Real.cos φ := by
      have h1 := Real.one_sub_sq_div_two_le_cos (x := φ)
      have h2 : φ ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hφ0 hφ 2
      linarith
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
  have hI3 : -(1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) ≤ ∫ θ in δ..θK, (S θ).re := by
    have := intervalIntegral.integral_mono_on hδ
      (continuous_const.intervalIntegrable δ θK) (hi δ θK)
      (fun θ hθ => (show -Real.exp (-Λ * δ ^ 2 / 8) ≤ (S θ).re from by
        have hθ0 : 0 ≤ θ := hδ₀.le.trans (hδ₀δ.trans hθ.1)
        have hn := (hb θ hθ0 hθ.2).1
        have hre := neg_abs_le (S θ).re
        have hab := Complex.abs_re_le_norm (S θ)
        have hcos := one_sub_cos_ge_sq_div_five (θ := θ)
          (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_gt_three, hθ.2])
        have h1 : 9 / 10 * ℓ * R * (θ ^ 2 / 5) ≤ F₁ * R * (1 - Real.cos θ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hF₁lo hR.le) hcos (by positivity)
            (mul_nonneg hF₁0 hR.le)
        have h2 : 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (R * ℓ) * θ ^ 2 * (1 / 1000) := by
          have hKθ : K * θ ≤ 1 / 1000 := by
            rw [← hKθK]; exact mul_le_mul_of_nonneg_left hθ.2 hK0.le
          have hDR : R * D ≤ R * (K * ℓ) := mul_le_mul_of_nonneg_left hD hR.le
          calc 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (R * (K * ℓ)) * θ ^ 3 := by
                apply mul_le_mul_of_nonneg_right _ (pow_nonneg hθ0 3); linarith
            _ = 128 / 3 * (R * ℓ) * θ ^ 2 * (K * θ) := by ring
            _ ≤ 128 / 3 * (R * ℓ) * θ ^ 2 * (1 / 1000) :=
                mul_le_mul_of_nonneg_left hKθ (by positivity)
        have hδθ : δ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (hδ₀.le.trans hδ₀δ) hθ.1 2
        have hexp : Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
            ≤ Real.exp (-Λ * δ ^ 2 / 8) := by
          apply Real.exp_le_exp.mpr; rw [hΛ]
          have hΛθ : 0 ≤ R * ℓ * θ ^ 2 := by positivity
          have h4 : R * ℓ * δ ^ 2 ≤ R * ℓ * θ ^ 2 :=
            mul_le_mul_of_nonneg_left hδθ (by positivity)
          linarith only [h1, h2, h4, hΛθ]
        linarith only [hn, hexp, hre, hab]))
    have hlen : (θK - δ) * -Real.exp (-Λ * δ ^ 2 / 8)
        ≥ -(1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) := by
      have hδ0 : 0 ≤ δ := hδ₀.le.trans hδ₀δ
      have := mul_le_mul_of_nonneg_right (show θK - δ ≤ 1 / 1000 by linarith)
        (Real.exp_pos (-Λ * δ ^ 2 / 8)).le
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hI4 : -(Real.pi / 2 * E) ≤ ∫ θ in θK..(Real.pi / 2), (S θ).re := by
    have := intervalIntegral.integral_mono_on hpi
      (continuous_const.intervalIntegrable θK (Real.pi / 2)) (hi θK (Real.pi / 2))
      (fun θ hθ => (show -E ≤ (S θ).re from by
        have hn := htail θ hθ.1 hθ.2
        have hre := neg_abs_le (S θ).re
        have hab := Complex.abs_re_le_norm (S θ)
        linarith))
    have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (htail θK le_rfl hpi)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have := mul_nonneg hθK0.le hE0
    linarith
  have hsplit : ∫ θ in (0 : ℝ)..(Real.pi / 2), (S θ).re
      = (∫ θ in (0 : ℝ)..δ₀, (S θ).re) + (∫ θ in δ₀..δ, (S θ).re)
        + (∫ θ in δ..θK, (S θ).re) + ∫ θ in θK..(Real.pi / 2), (S θ).re := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 δ₀) (hi δ₀ δ),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 δ) (hi δ θK),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 θK) (hi θK (Real.pi / 2))]
  rw [hsplit]
  have hmid' : 1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8) ≤ δ₀ / 20 := hmid
  linarith only [hI1, hI2, hI3, hI4, hmid', hE, hδ₀]

/-- **Saddle radius near the strip.**  For `½ + η ≤ a ≤ b ≤ t/2`, if
`a (log t + 2C_η) ≤ 2k ≤ b (log(t/2) − 2C_η)` then some `R ∈ [a, b]` solves
`R g_t'(R)/g_t(R) = 2k`. -/
theorem exists_saddle_radius_euler {t η a b : ℝ} (hη : 0 < η) (ht : 8 ≤ t) (ha : 1 / 2 + η ≤ a)
    (hab : a ≤ b) (hbt : b ≤ t / 2) {k : ℕ}
    (hlo : a * (Real.log t + 2 * xiEulerConstant η) ≤ 2 * (k : ℝ))
    (hhi : 2 * (k : ℝ) ≤ b * (Real.log (t / 2) - 2 * xiEulerConstant η)) :
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
  have ha' : φ a ≤ 2 * k := by
    obtain ⟨-, -, hhia⟩ := xiSliceLogDeriv_real_bounds_euler (t := t) (R := a) hη ht ha
      (by linarith)
    simp only [hφ]
    have := mul_le_mul_of_nonneg_left hhia (by linarith : (0 : ℝ) ≤ a)
    linarith
  have hb' : 2 * k ≤ φ b := by
    obtain ⟨-, hlob, -⟩ := xiSliceLogDeriv_real_bounds_euler (t := t) (R := b) hη ht
      (by linarith) hbt
    simp only [hφ]
    have := mul_le_mul_of_nonneg_left hlob (by linarith : (0 : ℝ) ≤ b)
    linarith
  obtain ⟨R, hR, hRk⟩ := intermediate_value_Icc hab hcont ⟨ha', hb'⟩
  refine ⟨R, hR, ?_⟩
  rw [re_scaledLogDeriv_xiSliceProduct_ofReal (by linarith [hR.1])]
  exact hRk

/-- **Positivity at one height from the saddle data.**  Let `0 < η ≤ 1/8`, `K = R₁/(2η)`, and let
`R ∈ [½ + 2η, R₁]` be the saddle radius of the order `2k` at height `t`.  If the saddle slope lies in
`[(9/10)u, 2u]`, the disc constant is at most `2ηu`, the arc beyond `1/(1000K)` is bounded by `E`,
and `Λ = Ru` is large enough for the three scale conditions, with `(π/2)E ≤ Λ^{−1/2}/10`, then
`c_{2k}(t) > 0`. -/
theorem xiSliceCoeff_pos_of_saddle_euler {η R₁ K t u R E : ℝ} {k : ℕ} (hη : 0 < η)
    (hη8 : η ≤ 1 / 8) (hR₁ : 1 ≤ R₁) (hKdef : K = R₁ / (2 * η)) (ht8 : 8 ≤ t)
    (hu0 : 0 < u) (hRa : 1 / 2 + 2 * η ≤ R) (hRb : R ≤ R₁) (hRt : R ≤ t / 2)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * (k : ℝ))
    (hF₁lo : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re)
    (hF₁hi : (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re ≤ 2 * u)
    (hKd : xiSliceDiscConstantEuler η t R ≤ 2 * η * u)
    (htail : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi / 2 → ‖sliceArc t R k θ‖ ≤ E)
    (hΛ1 : 1 ≤ R * u)
    (hE1 : (R * u) ^ (1 / 2 : ℝ) * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8) < 50)
    (hE3 : (R * u) ^ (-(2 / 5) : ℝ) < 1 / (1000 * K))
    (hE4 : (R * u) ^ (-(1 / 5) : ℝ) < 3 / (2 * (1 + 128 * K)))
    (hEt : Real.pi / 2 * E ≤ (R * u) ^ (-(1 / 2) : ℝ) / 10) :
    0 < xiSliceCoeff t (2 * k) := by
  have hR0 : 0 < R := by linarith
  have hR₁0 : 0 < R₁ := by linarith
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  have hKd0 : 0 ≤ xiSliceDiscConstantEuler η t R := by
    unfold xiSliceDiscConstantEuler
    have h1 : 0 ≤ Real.log (3 * t / 2) := Real.log_nonneg (by linarith)
    have h2 := xiEulerConstant_pos hη
    have h3 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    exact add_nonneg (mul_nonneg hη.le (by linarith [Real.pi_pos]))
      (mul_nonneg hR0.le (by linarith [Real.pi_pos]))
  obtain ⟨D, hDdef⟩ : ∃ D, D = xiSliceDiscConstantEuler η t R * R / (4 * η ^ 2) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; exact div_nonneg (mul_nonneg hKd0 hR0.le) (by positivity)
  have hD : D ≤ K * u := by
    rw [hDdef, div_le_iff₀ (by positivity), hKdef]
    have e : R₁ / (2 * η) * u * (4 * η ^ 2) = 2 * η * u * R₁ := by field_simp; ring
    rw [e]
    calc xiSliceDiscConstantEuler η t R * R ≤ xiSliceDiscConstantEuler η t R * R₁ :=
          mul_le_mul_of_nonneg_left hRb hKd0
      _ ≤ 2 * η * u * R₁ := mul_le_mul_of_nonneg_right hKd hR₁0.le
  -- the saddle-arc bounds on `[0, 1/(1000K)]`
  have hcub : ∀ θ : ℝ, 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3
      = 128 / 3 * (R * D) * θ ^ 3 := by
    intro θ; rw [hDdef]; field_simp; ring
  have hR₁θ : R₁ * (1 / (1000 * K)) = η / 500 := by rw [hKdef]; field_simp; ring
  have hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / (1000 * K) →
      ‖sliceArc t R k θ‖ ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
          * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
          + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 128 / 3 * (R * D) * θ ^ 3) ≤ (sliceArc t R k θ).re) := by
    intro θ hθ0 hθ
    have hRθ : R * θ ≤ η / 2 := by
      have h1 : R * θ ≤ R₁ * θ := mul_le_mul_of_nonneg_right hRb hθ0
      have h2 : R₁ * θ ≤ R₁ * (1 / (1000 * K)) := mul_le_mul_of_nonneg_left hθ hR₁0.le
      linarith
    have h := xiSlice_saddleArc_bounds_euler hη (by linarith) ht8 hRa hRt hθ0 hRθ
    rw [hsad, hcub θ] at h
    exact h
  -- the scales
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = R * u := ⟨_, rfl⟩
  rw [← hΛ] at hΛ1 hE1 hE3 hE4 hEt
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, δ₀ = Λ ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = Λ ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  rw [← hδ₀] at hEt
  have hδ₀pos : 0 < δ₀ := hδ₀ ▸ Real.rpow_pos_of_pos hΛ0 _
  have hδ₀δ : δ₀ ≤ δ := by
    rw [hδ₀, hδ]; exact Real.rpow_le_rpow_of_exponent_le hΛ1 (by norm_num)
  have hδθ : δ ≤ 1 / (1000 * K) := by rw [hδ]; exact hE3.le
  have hcore : Λ * δ₀ ^ 2 ≤ 1 := by rw [hδ₀]; exact (mul_rpow_neg_half_sq hΛ0).le
  have hphase : (1 + 128 * K) * Λ * δ ^ 3 ≤ 3 / 2 := by
    have := mul_rpow_neg_two_fifths_cube hΛ0
    rw [hδ, mul_assoc, this]
    have h4 := hE4.le
    rw [le_div_iff₀ (by positivity)] at h4
    linarith
  have hhalf : Λ ^ (1 / 2 : ℝ) * δ₀ = 1 := by
    rw [hδ₀]; exact rpow_half_mul_rpow_neg_half_eq_one hΛ0
  have hmid : 1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8) ≤ δ₀ / 20 := by
    have e : -Λ * δ ^ 2 / 8 = -(Λ ^ (1 / 5 : ℝ)) / 8 := by
      rw [hδ, ← mul_rpow_neg_two_fifths_sq hΛ0]; ring
    rw [e]
    have h1 : Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) ≤ 50 * δ₀ := by
      calc Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8)
          = Λ ^ (1 / 2 : ℝ) * Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) * δ₀ := by
            rw [mul_comm (Λ ^ (1 / 2 : ℝ)), mul_assoc, hhalf, mul_one]
        _ ≤ 50 * δ₀ := by gcongr
    linarith only [h1]
  -- continuity and assembly
  have hSc : Continuous fun θ : ℝ => sliceArc t R k θ := by
    have hg := differentiable_xiSliceProduct t
    have : Continuous fun θ : ℝ => xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    simp only [sliceArc, HTGeometry.saddleArc]
    fun_prop
  subst hΛ
  have hpos := quarter_integral_pos_of_arc_bounds_scaled hSc hR0 hu0 hK1 hF₁lo hF₁hi hD hD0
    hb htail hδ₀pos hδ₀δ hδθ hcore hphase hmid hEt
  rw [xiSliceCoeff_two_mul_eq_quarter t k (by linarith : (1 : ℝ) / 2 < R), Complex.zero_lt_real]
  have hxi : 0 < ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by simp; linarith))
  have hfac : 0 < 2 * ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ (2 * k)) := by
    positivity
  exact mul_pos hfac hpos

/-- The tail budget: `(π/2)·2A t^{−c} ≤ Λ^{−1/2}/10` once `Λ ≤ R₁ log t` and
`(log t)^{1/2} e^{−c log t} ≤ 1/(10πA√R₁)`. -/
theorem tail_budget_le {A c R₁ t u Λ : ℝ} (hA : 0 < A) (hR₁ : 0 < R₁) (ht : 0 < t)
    (hu : u = Real.log t) (hu0 : 0 < u) (hΛ0 : 0 < Λ) (hΛ : Λ ≤ R₁ * u)
    (h5 : u ^ (1 / 2 : ℝ) * Real.exp (-c * u) ≤ 1 / (10 * Real.pi * A * R₁ ^ (1 / 2 : ℝ))) :
    Real.pi / 2 * (2 * A * t ^ (-c)) ≤ Λ ^ (-(1 / 2) : ℝ) / 10 := by
  have htc : t ^ (-c) = Real.exp (-c * u) := by
    rw [Real.rpow_def_of_pos ht, hu]; ring_nf
  have hsq : Λ ^ (1 / 2 : ℝ) ≤ R₁ ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow hR₁.le hu0.le]
    exact Real.rpow_le_rpow hΛ0.le hΛ (by norm_num)
  have hR₁h : 0 < R₁ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hR₁ _
  have key : Real.pi * A * R₁ ^ (1 / 2 : ℝ) * (u ^ (1 / 2 : ℝ) * Real.exp (-c * u)) ≤ 1 / 10 := by
    calc _ ≤ Real.pi * A * R₁ ^ (1 / 2 : ℝ) * (1 / (10 * Real.pi * A * R₁ ^ (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = 1 / 10 := by field_simp
  have hX : Real.pi / 2 * (2 * A * Real.exp (-c * u)) * Λ ^ (1 / 2 : ℝ) ≤ 1 / 10 := by
    calc Real.pi / 2 * (2 * A * Real.exp (-c * u)) * Λ ^ (1 / 2 : ℝ)
        ≤ Real.pi / 2 * (2 * A * Real.exp (-c * u)) * (R₁ ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Real.pi * A * R₁ ^ (1 / 2 : ℝ) * (u ^ (1 / 2 : ℝ) * Real.exp (-c * u)) := by ring
      _ ≤ 1 / 10 := key
  have hhalf : Λ ^ (1 / 2 : ℝ) * Λ ^ (-(1 / 2) : ℝ) = 1 := rpow_half_mul_rpow_neg_half_eq_one hΛ0
  have hδ₀ : 0 < Λ ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hΛ0 _
  rw [htc]
  calc Real.pi / 2 * (2 * A * Real.exp (-c * u))
      = Real.pi / 2 * (2 * A * Real.exp (-c * u)) * Λ ^ (1 / 2 : ℝ) * Λ ^ (-(1 / 2) : ℝ) := by
        rw [mul_assoc _ (Λ ^ (1 / 2 : ℝ)), hhalf, mul_one]
    _ ≤ 1 / 10 * Λ ^ (-(1 / 2) : ℝ) := mul_le_mul_of_nonneg_right hX hδ₀.le
    _ = Λ ^ (-(1 / 2) : ℝ) / 10 := by ring

/-- **Positivity above the quarter-log edge for bounded saddle radius.**  For `0 < η ≤ 1/8` and
`R₁ ≥ 1` there is `t₀ ≥ 1` such that `c_{2k}(t) > 0` whenever `t ≥ t₀` and
`(¼ + 2η) log t ≤ k ≤ (R₁/4) log t`.  The saddle radius then lies in `[½ + 2η, R₁]`. -/
theorem exists_xiSliceCoeff_pos_sharp_window {η R₁ : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hR₁ : 1 ≤ R₁) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ k : ℕ, (1 / 4 + 2 * η) * Real.log t ≤ k →
      (k : ℝ) ≤ R₁ / 4 * Real.log t → 0 < xiSliceCoeff t (2 * k) := by
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.log 4 + Real.pi + 4 * E := ⟨_, rfl⟩
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hM0 : 0 < M := by rw [hMdef]; positivity
  have hR₁0 : 0 < R₁ := by linarith
  obtain ⟨K, hKdef⟩ : ∃ K, K = R₁ / (2 * η) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  obtain ⟨θ₁, hθ₁def⟩ : ∃ θ₁, θ₁ = 1 / (1000 * K) := ⟨_, rfl⟩
  have hθ₁0 : 0 < θ₁ := by rw [hθ₁def]; positivity
  have hR₁θ : R₁ * θ₁ = η / 500 := by
    rw [hθ₁def, hKdef]; field_simp; ring
  obtain ⟨c, hcdef⟩ : ∃ c, c = θ₁ ^ 2 / 10 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hcη : c ≤ η := by
    have h1 : θ₁ ≤ η / 500 := by rw [← hR₁θ]; exact le_mul_of_one_le_left hθ₁0.le hR₁
    have h2 : θ₁ ^ 2 ≤ θ₁ := by
      rw [sq]; exact mul_le_of_le_one_left hθ₁0.le (by linarith)
    rw [hcdef]; linarith
  obtain ⟨A, hA0, htail⟩ := exists_sliceArc_tail_le_euler (R₁ := R₁) hη (by linarith) hθ₁0
  -- thresholds in `Λ`
  have e1 := (tendsto_order.1 tendsto_rpow_half_mul_exp_neg_fifth_root).2 50 (by norm_num)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2 θ₁ hθ₁0
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (3 / (2 * (1 + 128 * K))) (by positivity)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and e4))
  -- threshold in `log t` for the tail
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) c hc0)).2
    (1 / (10 * Real.pi * A * R₁ ^ (1 / 2 : ℝ))) (by positivity)
  obtain ⟨U₅, hU₅⟩ := Filter.eventually_atTop.mp e5
  -- the threshold `L` for `log t`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hpi := Real.pi_pos
  have hRMη : 0 ≤ R₁ * M / η := by positivity
  have hEη : 0 ≤ E / η := by positivity
  have hΛ₀a := abs_nonneg Λ₀
  have hU₅a := abs_nonneg U₅
  obtain ⟨L, hLdef⟩ : ∃ L, L = 32 * R₁ + 16 + 2 * |Λ₀| + 2
      + 10 * (Real.log 2 + 2 * E + R₁ * M / η)
      + (Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η) + E / η + |U₅| := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; linarith
  refine ⟨Real.exp L, Real.one_le_exp hL0, ?_⟩
  intro t ht k hklo hkhi
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos L) ht
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  rw [← hudef] at hklo hkhi
  have hLu : L ≤ u := by
    rw [hudef, ← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) ht
  have htu : u + 1 ≤ t := by
    have := Real.add_one_le_exp u
    rw [hudef, Real.exp_log ht0] at this; rw [hudef]; exact this
  rw [hLdef] at hLu
  have hu1 : 32 * R₁ + 16 ≤ u := by linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0]
  have hu2 : 2 * |Λ₀| + 2 ≤ u := by
    linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu3 : 10 * (Real.log 2 + 2 * E + R₁ * M / η) ≤ u := by
    linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu4 : Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η ≤ u := by
    linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu5 : E / η ≤ u := by
    linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu6 : U₅ ≤ u := by
    have := le_abs_self U₅
    linarith only [this, hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu0 : 0 < u := by linarith only [hu1, hR₁0]
  have ht32 : 32 * R₁ + 16 ≤ t := by linarith only [hu1, htu]
  have ht8 : 8 ≤ t := by linarith only [ht32, hR₁0]
  have hR₁t : R₁ ≤ t / 2 := by linarith only [ht32, hR₁0]
  -- the saddle radius
  have hlo : (1 / 2 + 2 * η) * (Real.log t + 2 * xiEulerConstant η) ≤ 2 * (k : ℝ) := by
    rw [← hudef, ← hEdef]
    have h1 : 2 * η * (E / η) = 2 * E := by field_simp
    have h2 : 2 * η * (E / η) ≤ 2 * η * u := mul_le_mul_of_nonneg_left hu5 (by linarith)
    have h3 : η * E ≤ 1 / 8 * E := mul_le_mul_of_nonneg_right hη8 hE0.le
    linarith only [h1, h2, h3, hklo, hE0]
  have hhi : 2 * (k : ℝ) ≤ R₁ * (Real.log (t / 2) - 2 * xiEulerConstant η) := by
    rw [Real.log_div ht0.ne' (by norm_num), ← hudef, ← hEdef]
    have h1 : Real.log 2 + 2 * E ≤ u / 2 := by linarith only [hu3, hRMη, hl2, hE0]
    have h2 := mul_le_mul_of_nonneg_left h1 hR₁0.le
    linarith only [h2, hkhi]
  obtain ⟨R, ⟨hRa, hRb⟩, hsad⟩ := exists_saddle_radius_euler (t := t) (k := k) hη ht8
    (by linarith : 1 / 2 + η ≤ 1 / 2 + 2 * η) (by linarith : 1 / 2 + 2 * η ≤ R₁) hR₁t hlo hhi
  have hR0 : 0 < R := by linarith only [hRa, hη]
  have hRt : R ≤ t / 2 := le_trans hRb hR₁t
  -- the slope
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSlice_saddleSlope_bounds_euler (t := t) (R := R) hη
    (by linarith) ht8 hRa hRt
  rw [← hEdef] at hF₁lo hF₁hi
  rw [← hMdef] at hF₁lo hF₁hi
  have hRM : R * M / η ≤ R₁ * M / η :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRb hM0.le) hη.le
  rw [Real.log_div ht0.ne' (by norm_num), ← hudef] at hF₁lo
  rw [← hudef] at hF₁hi
  have hF₁lo' : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re := by
    linarith only [hF₁lo, hRM, hu3]
  have hF₁hi' : (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re ≤ 2 * u := by
    linarith only [hF₁hi, hRM, hu3, hl2, hRMη, hE0]
  -- the disc constant
  have hKd : xiSliceDiscConstantEuler η t R ≤ 2 * η * u := by
    unfold xiSliceDiscConstantEuler
    rw [← hEdef, ← hMdef]
    have e : Real.log (3 * t / 2) = Real.log (3 / 2) + u := by
      rw [show 3 * t / 2 = 3 / 2 * t by ring, Real.log_mul (by norm_num) ht0.ne', hudef]
    rw [e]
    have h1 : η * (R₁ * M / η) = R₁ * M := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hu4 hη.le
    have h3 : R * M ≤ R₁ * M := mul_le_mul_of_nonneg_right hRb hM0.le
    linarith only [h1, h2, h3]
  -- the tail on `[1/(1000K), π/2]`
  have htail' : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi / 2 →
      ‖sliceArc t R k θ‖ ≤ 2 * A * t ^ (-c) := by
    intro θ hθ hθπ
    have h := htail t R θ k ht32 hRa hRb (by rw [hθ₁def]; exact hθ) hθπ
    rw [← hcdef] at h
    have hηc : t ^ (-η) ≤ t ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    calc ‖sliceArc t R k θ‖ ≤ A * (t ^ (-η) + t ^ (-c)) := h
      _ ≤ A * (t ^ (-c) + t ^ (-c)) := mul_le_mul_of_nonneg_left (by linarith) hA0.le
      _ = 2 * A * t ^ (-c) := by ring
  -- the scale conditions
  have hΛlo : u / 2 ≤ R * u := by
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) / 2 ≤ R) hu0.le; linarith
  have hΛhi : R * u ≤ R₁ * u := mul_le_mul_of_nonneg_right hRb hu0.le
  have hΛbig : max Λ₀ 1 ≤ R * u :=
    max_le (by have := le_abs_self Λ₀; linarith only [this, hΛlo, hu2])
      (by linarith only [hΛlo, hu2, hΛ₀a])
  obtain ⟨hE1, hE3, hE4⟩ := hΛ₀ (R * u) (le_trans (le_max_left _ _) hΛbig)
  rw [hθ₁def] at hE3
  have hEt := tail_budget_le hA0 hR₁0 ht0 hudef hu0 (by linarith only [hΛlo, hu0]) hΛhi
    (hU₅ u hu6).le
  exact xiSliceCoeff_pos_of_saddle_euler hη hη8 hR₁ hKdef ht8 hu0 hRa hRb hRt hsad hF₁lo'
    hF₁hi' hKd htail' (le_trans (le_max_right _ _) hΛbig) hE1 hE3 hE4 hEt

/-- **Positivity above the quarter-log edge.**  For every `ε > 0` there is `K` such that
`c_{2k}(t) > 0` for all `t ≥ 0` and `k ≥ max(K, (¼ + ε) log t)`. -/
theorem exists_xiSliceCoeff_pos_above_quarter_log {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, max K ((1 / 4 + ε) * Real.log t) ≤ k →
      0 < xiSliceCoeff t (2 * k) := by
  obtain ⟨t₁, κ, hwin⟩ := exists_xiSliceCoeff_pos_window
  obtain ⟨K₀, hlarge⟩ := exists_xiSliceCoeff_pos_large_order
  obtain ⟨η, hηdef⟩ : ∃ η, η = min (ε / 2) (1 / 8) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min (by linarith) (by norm_num)
  have hη8 : η ≤ 1 / 8 := by rw [hηdef]; exact min_le_right _ _
  have hηε : 2 * η ≤ ε := by have := min_le_left (ε / 2) (1 / 8); rw [hηdef]; linarith
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁, R₁ = 4 * max κ 0 + 4 := ⟨_, rfl⟩
  have hR₁ : 1 ≤ R₁ := by have := le_max_right κ 0; rw [hR₁def]; linarith
  obtain ⟨t₀, ht₀1, hsharp⟩ := exists_xiSliceCoeff_pos_sharp_window hη hη8 hR₁
  obtain ⟨T, hT⟩ : ∃ T, T = max (max t₀ t₁) 1 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := hT ▸ le_max_right _ _
  refine ⟨max K₀ (T * Real.log T / 8 + 1), ?_⟩
  intro t ht0 k hk
  have hkK : max K₀ (T * Real.log T / 8 + 1) ≤ k := le_trans (le_max_left _ _) hk
  have hkK₀ : K₀ ≤ k := le_trans (le_max_left _ _) hkK
  have hkT : T * Real.log T / 8 + 1 ≤ k := le_trans (le_max_right _ _) hkK
  have hkε : (1 / 4 + ε) * Real.log t ≤ k := le_trans (le_max_right _ _) hk
  rcases le_or_gt (t * Real.log t / 8) k with hbig | hsmall
  · exact hlarge t ht0 k hkK₀ hbig
  · have htT : T < t := by
      by_contra h
      have := mul_log_le_of_le ht0 hT1 (not_lt.mp h)
      linarith
    have hmax : max t₀ t₁ ≤ t := le_trans (hT ▸ le_max_left _ _) htT.le
    have ht₀ : t₀ ≤ t := le_trans (le_max_left _ _) hmax
    have ht₁ : t₁ ≤ t := le_trans (le_max_right _ _) hmax
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    rcases le_or_gt (k : ℝ) (R₁ / 4 * Real.log t) with hkR | hkR
    · refine hsharp t ht₀ k ?_ hkR
      have := mul_le_mul_of_nonneg_right (by linarith : 1 / 4 + 2 * η ≤ 1 / 4 + ε) hlogt
      linarith
    · have hκ : κ * Real.log t ≤ k := by
        have h1 : κ * Real.log t ≤ max κ 0 * Real.log t :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlogt
        have h2 : max κ 0 * Real.log t ≤ R₁ / 4 * Real.log t :=
          mul_le_mul_of_nonneg_right (by rw [hR₁def]; linarith) hlogt
        linarith
      exact hwin t ht₁ k hκ hsmall.le

/-- **Route 3 reduced to coefficients below the quarter-log edge.**  For every `ε > 0` there is
`K` such that the Riemann hypothesis is equivalent to `c_{2k}(t) ≥ 0` for all `t ≥ 0` and
`k < max(K, (¼ + ε) log t)`. -/
theorem exists_riemannHypothesis_iff_xiSliceCoeff_nonneg_below_quarter_log {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K : ℝ, (RiemannHypothesis ↔
      ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, (k : ℝ) < max K ((1 / 4 + ε) * Real.log t) →
        0 ≤ xiSliceCoeff t (2 * k)) := by
  obtain ⟨K, hpos⟩ := exists_xiSliceCoeff_pos_above_quarter_log hε
  refine ⟨K, ⟨fun hRH t _ k _ => xiSliceCoeff_nonneg_of_riemannHypothesis hRH t (2 * k),
    fun hlow => riemannHypothesis_of_xiSliceCoeff_nonneg_of_nonneg_height fun t ht n => ?_⟩⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases lt_or_ge (k : ℝ) (max K ((1 / 4 + ε) * Real.log t)) with hk | hk
    · exact hlow t ht k hk
    · exact (hpos t ht k hk).le
  · rw [xiSliceCoeff_odd_eq_zero]

end

end RHTower
