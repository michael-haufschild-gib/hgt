import GaloisForLFunctions.RHTower.KiKimLeeSharpReality
import GaloisForLFunctions.RHTower.KiKimLeeEffectiveReality

/-!
# The sharp heat horizon: zeros of `H_t` are real once `t log(X/2π) ≥ 1 + √3/2 + ε`

**Theorem** (`riemannHeat_zeros_real_sharp`). For every `ε > 0` there is `X₀` such that for all
`0 < t ≤ 1/8`, every zero `z` of the de Bruijn–Newman deformation `H_t` with `|Re z| ≥ X₀` and
`|Re z| ≥ 2π e^{(1 + √3/2 + ε)/t}` is real.

The corpus has the height `2π e^{40/t}` (`riemannHeat_zeros_real_of_le_re`).

**Proof.**
* Put `c₀ = 1 + √3/2 + ε` and `c = t log(X/2π) = 2tα`.
* If `c ≥ 40`, the corpus effective Ki–Kim–Lee theorem applies.
* If `c₀ ≤ c < 40`, the sharp one-height positivity `re_slope_mul_conj_pos_sharp` applies once the
  error sums are small. Parameters `η, m` are chosen with `c² − 2c(1+η) + ¼ ≥ m > 0` for all `c ≥ c₀`
  (`exists_sharp_params`; this is where `c₀ > 1 + √3/2` enters).
* For `t ∈ [c₀/(2α), 20/α]` every error term is bounded by an explicit function of `α`
  (`sharp_error_bounds`), and each of these tends to `0` (`eventually_sharp_errors_small`).

Scope: the constant `1 + √3/2` is the convexity threshold. With a subconvexity exponent `θ₀ ≤ 1/6`
the same argument gives `1/(1 − 2θ₀)`, and every window argument needs `c > 1`. The theorem is
RH-blind.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- **Choice of the window parameters.** -/
theorem exists_sharp_params {c₀ : ℝ} (hc₀ : 1 + Real.sqrt 3 / 2 < c₀) :
    ∃ η m : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < m ∧
      (∀ c : ℝ, c₀ ≤ c → m ≤ c ^ 2 - 2 * c * (1 + η) + 1 / 4) ∧
      1 + η ≤ c₀ ∧ 3 / 2 ≤ c₀ ∧ 0 < 3 / 4 * c₀ - 1 - η := by
  have hs3 : (1.7 : ℝ) < Real.sqrt 3 := by
    rw [show (1.7 : ℝ) = Real.sqrt (1.7 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hd : 3 / 4 < (c₀ - 1) ^ 2 := by
    have h0 : 0 ≤ Real.sqrt 3 / 2 := by positivity
    have h1 : Real.sqrt 3 / 2 < c₀ - 1 := by linarith
    nlinarith
  set D := (c₀ - 1) ^ 2 - 3 / 4 with hD
  have hD0 : 0 < D := by linarith
  have hc0 : 0 < c₀ := by linarith
  refine ⟨min (1 / 4) (D / (4 * c₀)), D / 2, lt_min (by norm_num) (by positivity),
    min_le_left _ _, by positivity, fun c hc => ?_, ?_, ?_, ?_⟩
  · have hη : min (1 / 4) (D / (4 * c₀)) ≤ D / (4 * c₀) := min_le_right _ _
    have hη0 : 0 ≤ min (1 / 4) (D / (4 * c₀)) := le_min (by norm_num) (by positivity)
    have h2 : 2 * c₀ * min (1 / 4) (D / (4 * c₀)) ≤ D / 2 := by
      have := mul_le_mul_of_nonneg_left hη (by linarith : (0 : ℝ) ≤ 2 * c₀)
      rw [show 2 * c₀ * (D / (4 * c₀)) = D / 2 by field_simp; ring] at this
      exact this
    -- monotone in `c ≥ 1 + η`
    have hmono : c₀ ^ 2 - 2 * c₀ * (1 + min (1 / 4) (D / (4 * c₀))) ≤
        c ^ 2 - 2 * c * (1 + min (1 / 4) (D / (4 * c₀))) := by
      have hη4 : min (1 / 4) (D / (4 * c₀)) ≤ 1 / 4 := min_le_left _ _
      nlinarith
    nlinarith
  · have hη4 : min (1 / 4) (D / (4 * c₀)) ≤ 1 / 4 := min_le_left _ _
    linarith
  · linarith
  · have hη4 : min (1 / 4) (D / (4 * c₀)) ≤ 1 / 4 := min_le_left _ _
    linarith

/-- **Explicit bounds for the six error terms** in the regime `c₀ ≤ 2tα ≤ 40`. -/
theorem sharp_error_bounds {c₀ η m K α t : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hm : 0 < m)
    (hK0 : 0 ≤ K) (hc₀ : 3 / 2 ≤ c₀) (hα : 160 ≤ α)
    (hη₁ : 20 * (1 / η + 3) ^ 2 ≤ α) (ht1 : c₀ / (2 * α) ≤ t) (ht2 : t ≤ 20 / α) :
    sharpR1 η t α ≤ Real.exp (-(α / 2) * (3 / 4 * c₀ - 1 - η)) ∧
    kklR2 t α ≤ Real.exp (-α ^ 2 + 1) ∧
    sharpR3 η t ≤ 2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4 ∧
    sharpStripErr K η m t α ≤ 24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) ∧
    kklRC t α ≤ 12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) ∧
    kklRB t α ≤ 2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
      (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α) := by
  have hα0 : 0 < α := by linarith
  have hc0 : 0 < c₀ := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hct : c₀ ≤ 2 * t * α := by
    rw [div_le_iff₀ (by positivity)] at ht1; linarith
  have htα : t * α ≤ 20 := by
    rw [le_div_iff₀ hα0] at ht2; linarith
  have ht8 : t ≤ 1 / 8 := by
    refine ht2.trans ?_
    rw [div_le_iff₀ hα0]; linarith
  have hinvt : 1 / t ≤ 2 * α / c₀ := by
    rw [div_le_div_iff₀ ht0 hc0]; linarith
  have hinvt2 : α / 20 ≤ 1 / t := by
    rw [div_le_div_iff₀ (by norm_num) ht0]; linarith
  have h2α : 2 * α / c₀ ≤ 2 * α := by
    rw [div_le_iff₀ hc0]; nlinarith
  -- `(4πt)^{−½} ≤ 2α`
  have hg : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) ≤ 2 * α := by
    refine (rpow_neg_half_le_one_add_inv (by positivity)).trans ?_
    have hpi := Real.pi_gt_three
    have h1 : (4 * Real.pi * t)⁻¹ ≤ α := by
      rw [inv_le_comm₀ (by positivity) hα0, inv_eq_one_div, div_le_iff₀ hα0]
      nlinarith
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the lower tail
    unfold sharpR1
    apply Real.exp_le_exp.mpr
    nlinarith
  · unfold kklR2
    apply Real.exp_le_exp.mpr
    linarith
  · -- the model error
    unfold sharpR3
    set η₁ := 1 / η + 3 with hη₁def
    have hη₁0 : 0 ≤ η₁ := by positivity
    have hst : Real.sqrt t ≤ Real.sqrt (20 / α) := Real.sqrt_le_sqrt ht2
    have hsq0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hsmall : η₁ * Real.sqrt (20 / α) ≤ 1 := by
      have h1 : η₁ ^ 2 * (20 / α) ≤ 1 := by
        rw [mul_div_assoc', div_le_one hα0]; linarith
      have h2 : η₁ * Real.sqrt (20 / α) = Real.sqrt (η₁ ^ 2 * (20 / α)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hη₁0]
      rw [h2]
      calc Real.sqrt (η₁ ^ 2 * (20 / α)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
        _ = 1 := Real.sqrt_one
    have hexp : t * (1 / Real.sqrt t + η₁) ^ 2 = (1 + η₁ * Real.sqrt t) ^ 2 := by
      have key : ∀ r : ℝ, 0 < r → r ^ 2 * (1 / r + η₁) ^ 2 = (1 + η₁ * r) ^ 2 := by
        intro r hr; field_simp
      have h := key (Real.sqrt t) hsq0
      rwa [Real.sq_sqrt ht0.le] at h
    rw [hexp]
    have hle : (1 + η₁ * Real.sqrt t) ^ 2 ≤ 4 := by
      have : η₁ * Real.sqrt t ≤ 1 := (mul_le_mul_of_nonneg_left hst hη₁0).trans hsmall
      have : 0 ≤ η₁ * Real.sqrt t := by positivity
      nlinarith
    have h2 : 2 * η₁ * Real.sqrt t ≤ 2 * η₁ * Real.sqrt (20 / α) :=
      mul_le_mul_of_nonneg_left hst (by positivity)
    exact mul_le_mul h2 (Real.exp_le_exp.mpr hle) (by positivity) (by positivity)
  · -- the strip
    unfold sharpStripErr
    have hpi := Real.pi_gt_three
    have hfac1 : (1 + η) / (2 * t) + α + 1 ≤ 3 * α := by
      have : (1 + η) / (2 * t) ≤ α := by
        have h1 : (1 + η) / (2 * t) = (1 + η) / 2 * (1 / t) := by field_simp
        rw [h1]
        have h2 : (1 + η) / 2 * (1 / t) ≤ (1 + η) / 2 * (2 * α / c₀) := by gcongr
        have h3 : (1 + η) / 2 * (2 * α / c₀) ≤ α := by
          rw [show (1 + η) / 2 * (2 * α / c₀) = (1 + η) * α / c₀ by ring, div_le_iff₀ hc0]
          nlinarith
        linarith
      linarith
    have hfac2 : (2 * Real.pi) ^ ((1 / 2 + η) / 2) ≤ 2 * Real.pi := by
      calc (2 * Real.pi) ^ ((1 / 2 + η) / 2) ≤ (2 * Real.pi) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 2 * Real.pi := Real.rpow_one _
    have hfac3 : Real.exp (-(m / (4 * t))) ≤ Real.exp (-(m / 80) * α) := by
      apply Real.exp_le_exp.mpr
      have : m / 80 * α ≤ m / (4 * t) := by
        rw [show m / (4 * t) = m / 4 * (1 / t) by field_simp]
        have := mul_le_mul_of_nonneg_left hinvt2 (by positivity : (0 : ℝ) ≤ m / 4)
        linarith
      linarith
    have hη1 : 1 + η ≤ 2 := by linarith
    calc (1 + η) * ((1 + η) / (2 * t) + α + 1) * ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K *
          (2 * Real.pi) ^ ((1 / 2 + η) / 2) * Real.exp (-(m / (4 * t))))
        ≤ 2 * (3 * α) * ((2 * α) * K * (2 * Real.pi) * Real.exp (-(m / 80) * α)) := by
          gcongr
      _ = 24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) := by ring
  · -- the far region
    unfold kklRC
    have hfac : 1 / (2 * t) + α + 1 ≤ 3 * α := by
      have : 1 / (2 * t) ≤ α := by
        have h1 : 1 / (2 * t) = 1 / 2 * (1 / t) := by field_simp
        rw [h1]
        have : 1 / 2 * (1 / t) ≤ 1 / 2 * (2 * α / c₀) := by gcongr
        nlinarith
      linarith
    have hexp : -(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t ≤
        -(15 / 8) * α ^ 2 + 20 * α + 164 := by
      have : t * α ^ 2 ≤ 20 * α := by nlinarith
      nlinarith
    calc 2 * Real.exp 1 * 2 * (1 / (2 * t) + α + 1) *
          Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)
        ≤ 2 * Real.exp 1 * 2 * (3 * α) * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) := by
          gcongr
      _ = _ := by ring
  · -- the boundary value at `W`
    unfold kklRB
    have hexp : -((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + t * α ^ 2 ≤
        -((α ^ 2 - 1 / 2) ^ 2 * α / 80) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α := by
      have h1 : (α ^ 2 - 1 / 2) ^ 2 * α / 80 ≤ (α ^ 2 - 1 / 2) ^ 2 / (4 * t) := by
        rw [show (α ^ 2 - 1 / 2) ^ 2 / (4 * t) = (α ^ 2 - 1 / 2) ^ 2 / 4 * (1 / t) by field_simp]
        have := mul_le_mul_of_nonneg_left hinvt2 (by positivity : (0 : ℝ) ≤ (α ^ 2 - 1 / 2) ^ 2 / 4)
        nlinarith
      have h2 : t * α ^ 2 ≤ 20 * α := by nlinarith
      linarith
    calc (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + t * α ^ 2)
        ≤ (2 * α) * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
            (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α) := by
          gcongr
      _ = _ := by ring

/-- `x ≤ eˣ`. -/
private theorem self_le_exp (x : ℝ) : x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

/-- **The bounding functions are eventually small.** -/
theorem eventually_sharp_errors_small {c₀ η m K b : ℝ} (hη : 0 < η) (hm : 0 < m)
    (hδ : 0 < 3 / 4 * c₀ - 1 - η) :
    ∀ᶠ α : ℝ in atTop, 160 ≤ α ∧ 20 * (1 / η + 3) ^ 2 ≤ α ∧
      Real.exp (-(α / 2) * (3 / 4 * c₀ - 1 - η)) + Real.exp (-α ^ 2 + 1) +
        2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4 +
        24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp b * (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 5 ∧
      2 * (24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α)) +
        Real.exp b * (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
          2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
            (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) +
        (1 / η + 3) * (1 + 2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4) <
        18 / 25 * α := by
  set δ := 3 / 4 * c₀ - 1 - η with hδdef
  set η₁ := 1 / η + 3 with hη₁
  -- the six bounding functions tend to `0`
  have t1 : Tendsto (fun α : ℝ => Real.exp (-(α / 2) * δ)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h0 : Tendsto (fun α : ℝ => α / 2 * δ) atTop atTop :=
      (tendsto_id.atTop_div_const (by norm_num)).atTop_mul_const hδ
    have h1 : Tendsto (fun α : ℝ => -(α / 2 * δ)) atTop atBot := tendsto_neg_atTop_atBot.comp h0
    exact h1.congr fun α => by ring
  have t2 : Tendsto (fun α : ℝ => Real.exp (-α ^ 2 + 1)) atTop (𝓝 0) := by
    have h := tendsto_mul_exp_quadratic 1 (c := 1) one_pos 0 1
    refine h.congr fun α => ?_
    simp only [one_mul, zero_mul, add_zero]
    ring_nf
  have t3 : Tendsto (fun α : ℝ => 2 * η₁ * Real.sqrt (20 / α) * Real.exp 4) atTop (𝓝 0) := by
    have h1 : Tendsto (fun α : ℝ => 20 / α) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    have h3 := (h2.const_mul (2 * η₁)).mul_const (Real.exp 4)
    simpa [mul_assoc] using h3
  have t4 : Tendsto (fun α : ℝ => 24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α))
      atTop (𝓝 0) := by
    have hk : 0 < m / 80 := by positivity
    have h1 : Tendsto (fun α : ℝ => m / 80 * α) atTop atTop := tendsto_id.const_mul_atTop hk
    have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp h1
    have h3 := h2.const_mul (24 * Real.pi * K * (80 / m) ^ 2)
    rw [mul_zero] at h3
    refine h3.congr fun α => ?_
    simp only [Function.comp]
    field_simp
  have t5 : Tendsto (fun α : ℝ => Real.exp b *
      (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164))) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic (Real.exp b * 12 * Real.exp 1) (c := 15 / 8)
      (by norm_num) 21 164 ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with α hα
      positivity
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with α hα
      have h1 : α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) ≤
          Real.exp (164 + 21 * α - 15 / 8 * α ^ 2) := by
        calc α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)
            ≤ Real.exp α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) := by
              gcongr; exact self_le_exp α
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ Real.exp b * 12 * Real.exp 1)
      calc Real.exp b * (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164))
          = Real.exp b * 12 * Real.exp 1 * (α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) := by
            ring
        _ ≤ _ := h2
  have t6 : Tendsto (fun α : ℝ => Real.exp b * (2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
      (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α))) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic (2 * Real.exp b) (c := 1) one_pos 0 0 ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with α hα
      positivity
    · filter_upwards [eventually_ge_atTop (100 : ℝ)] with α hα
      have hpoly : -((α ^ 2 - 1 / 2) ^ 2 * α / 80) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α + α ≤
          0 + 0 * α - 1 * α ^ 2 := by
        have ha2 : α ^ 2 / 2 ≤ α ^ 2 - 1 / 2 := by nlinarith
        have hsq : (α ^ 2 / 2) ^ 2 ≤ (α ^ 2 - 1 / 2) ^ 2 := by
          have : 0 ≤ α ^ 2 / 2 := by positivity
          nlinarith
        have h5 : α ^ 5 / 320 ≤ (α ^ 2 - 1 / 2) ^ 2 * α / 80 := by
          have := mul_le_mul_of_nonneg_right hsq (by linarith : (0 : ℝ) ≤ α)
          nlinarith
        have h3 : (α ^ 2 + 1 / 2) * (α + 1 / 8) ≤ 4 * α ^ 3 := by nlinarith
        have h6 : 4 * α ^ 3 + 21 * α + α ^ 2 ≤ α ^ 5 / 320 := by
          have hα2 : 10000 ≤ α ^ 2 := by nlinarith
          have hα3 : 0 ≤ α ^ 3 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hα2 hα3]
        linarith
      have h1 : 2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
          (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α) ≤ 2 * Real.exp (0 + 0 * α - 1 * α ^ 2) := by
        calc 2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
              (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)
            ≤ 2 * (Real.exp α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
                (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) := by
              rw [mul_assoc]; gcongr; exact self_le_exp α
          _ = 2 * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
                (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α + α) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ 2 * Real.exp (0 + 0 * α - 1 * α ^ 2) := by
              gcongr
      calc Real.exp b * (2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
            (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α))
          ≤ Real.exp b * (2 * Real.exp (0 + 0 * α - 1 * α ^ 2)) := by gcongr
        _ = 2 * Real.exp b * Real.exp (0 + 0 * α - 1 * α ^ 2) := by ring
  -- eventual smallness
  have e1 := t1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e2 := t2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e3 := t3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e4 := t4.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e5 := t5.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e6 := t6.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  filter_upwards [e1, e2, e3, e4, e5, e6, eventually_ge_atTop (160 : ℝ),
    eventually_ge_atTop (20 * η₁ ^ 2), eventually_gt_atTop (25 / 18 * (2 * η₁ + 1))]
    with α h1 h2 h3 h4 h5 h6 h160 hη₁α hbig
  have hη₁0 : 0 ≤ η₁ := by positivity
  refine ⟨h160, hη₁α, by linarith, ?_⟩
  have h3' : η₁ * (1 + 2 * η₁ * Real.sqrt (20 / α) * Real.exp 4) ≤ η₁ * (1 + 1) := by
    gcongr; linarith
  have hsplit : Real.exp b * (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
      2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) =
      Real.exp b * (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) +
      Real.exp b * (2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
        (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) := by ring
  rw [hsplit]
  linarith

/-- The second error sum from its bounds (pure arithmetic). -/
private theorem combine_sharp_S2 {S RC RB R3 F3 F4 F5 F6 B η₁ α : ℝ} (hA : S ≤ F4)
    (h5 : RC ≤ F5) (h6 : RB ≤ F6) (h3 : R3 ≤ F3) (hB : 0 ≤ B) (hη : 0 ≤ η₁)
    (hsum : 2 * F4 + B * (F5 + F6) + η₁ * (1 + F3) < 18 / 25 * α) :
    2 * S + B * (RC + RB) + η₁ * (1 + R3) < 18 / 25 * α := by
  have h1 : B * (RC + RB) ≤ B * (F5 + F6) := mul_le_mul_of_nonneg_left (by linarith) hB
  have h2 : η₁ * (1 + R3) ≤ η₁ * (1 + F3) := mul_le_mul_of_nonneg_left (by linarith) hη
  linarith

/-- **Sharp large-height slope positivity.** With the parameters of `exists_sharp_params`, for `X`
past an absolute height and `X ≥ 2π e^{c₀/t}`, the window slope pairing is positive at every
`|v| ≤ ½`. -/
theorem re_slope_pos_sharp_window {c₀ η m K α₀ t X : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hm : 0 < m) (hmc : ∀ c : ℝ, c₀ ≤ c → m ≤ c ^ 2 - 2 * c * (1 + η) + 1 / 4)
    (hc₀ : 3 / 2 ≤ c₀)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ ((1 / 2 + η - w) / 2) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K)
    (hα₀ : ∀ α ≥ α₀, 160 ≤ α ∧ 20 * (1 / η + 3) ^ 2 ≤ α ∧
      Real.exp (-(α / 2) * (3 / 4 * c₀ - 1 - η)) + Real.exp (-α ^ 2 + 1) +
        2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4 +
        24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 5 ∧
      2 * (24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α)) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
            2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
              (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) +
        (1 / η + 3) * (1 + 2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4) <
        18 / 25 * α)
    (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX₀ : 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ X)
    (hXc : 2 * Real.pi * Real.exp (c₀ / t) ≤ X) :
    ∀ v : ℝ, |v| ≤ 1 / 2 →
      0 < ((∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) *
        xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) v)).re := by
  intro v hv
  have h2π : 0 < 2 * Real.pi := by positivity
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX₀
  set α := (horizontalSlope X).re with hαdef
  have hαlog : α = Real.log (X / (2 * Real.pi)) / 2 := by rw [hαdef, horizontalSlope_re]
  -- `α` from the two height conditions
  have hαge : ∀ L : ℝ, 2 * Real.pi * Real.exp L ≤ X → L / 2 ≤ α := by
    intro L hL
    have h1 : Real.exp L ≤ X / (2 * Real.pi) := by rw [le_div_iff₀ h2π]; linarith
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    rw [hαlog]; linarith
  have hαbig : max α₀ 160 ≤ α := by have := hαge _ hX₀; linarith
  have hα160 : 160 ≤ α := (le_max_right _ _).trans hαbig
  have hαα₀ : α₀ ≤ α := (le_max_left _ _).trans hαbig
  have hα0 : 0 < α := by linarith
  have hct : c₀ / (2 * α) ≤ t := by
    have h := hαge _ hXc
    rw [div_le_iff₀ (by positivity)]
    have : c₀ / t / 2 * t = c₀ / 2 := by field_simp
    nlinarith
  rcases le_or_gt (20 / α) t with h20 | h20
  · -- the corpus regime `t log(X/2π) ≥ 40`
    have htα : 20 ≤ t * α := by
      rw [div_le_iff₀ hα0] at h20; linarith
    have hX200 : 200 ≤ X := by
      have h1 : (1 : ℝ) + 320 ≤ Real.exp (2 * max α₀ 160) := by
        have := Real.add_one_le_exp (2 * max α₀ 160)
        have : (320 : ℝ) ≤ 2 * max α₀ 160 := by linarith [le_max_right α₀ 160]
        linarith
      have := Real.pi_gt_three
      nlinarith
    refine re_slope_mul_conj_pos ht ht8 hX200 hv (by linarith) ?_
      (window_fits ht8 ht hX0 (by linarith))
      ((kklError_le_uniform ht le_rfl ht8 (by linarith)).trans
        (kklErrorUniform_le_of_mul_ge ht ht8 htα))
    linarith
  · -- the sharp regime `c₀ ≤ t log(X/2π) < 40`
    obtain ⟨-, hη₁α, hsum1, hsum2⟩ := hα₀ α hαα₀
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := sharp_error_bounds (c₀ := c₀) (K := K) hη hη4 hm hK0 hc₀
      hα160 hη₁α hct h20.le
    have hX200 : 200 ≤ X := by
      have h1 : (1 : ℝ) + 320 ≤ Real.exp (2 * max α₀ 160) := by
        have := Real.add_one_le_exp (2 * max α₀ 160)
        have : (320 : ℝ) ≤ 2 * max α₀ 160 := by linarith [le_max_right α₀ 160]
        linarith
      have := Real.pi_gt_three
      nlinarith
    have h2tα : c₀ ≤ 2 * t * α := by
      rw [div_le_iff₀ (by positivity)] at hct; linarith
    have heb := Real.exp_pos (9 / 2 * (1 / η + 3))
    refine re_slope_mul_conj_pos_sharp ht ht8 hη hK hK0 hX200 hv (by linarith) (by linarith)
      (by linarith) (hmc _ h2tα) (by nlinarith) (window_fits ht8 ht hX0 (by linarith)) ?_ ?_
    · have := mul_le_mul_of_nonneg_left b5 heb.le
      linarith
    · exact combine_sharp_S2 b4 b5 b6 b3 heb.le (by positivity) hsum2

/-- **Sharp large-height nonvanishing.** Under the hypotheses of `re_slope_pos_sharp_window`,
`H_t(X + iy) ≠ 0` for `0 < |y| ≤ ½`. -/
theorem riemannHeat_ne_zero_sharp {c₀ η m K α₀ t X : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hm : 0 < m) (hmc : ∀ c : ℝ, c₀ ≤ c → m ≤ c ^ 2 - 2 * c * (1 + η) + 1 / 4)
    (hc₀ : 3 / 2 ≤ c₀)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ ((1 / 2 + η - w) / 2) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K)
    (hα₀ : ∀ α ≥ α₀, 160 ≤ α ∧ 20 * (1 / η + 3) ^ 2 ≤ α ∧
      Real.exp (-(α / 2) * (3 / 4 * c₀ - 1 - η)) + Real.exp (-α ^ 2 + 1) +
        2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4 +
        24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 5 ∧
      2 * (24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α)) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
            2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
              (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) +
        (1 / η + 3) * (1 + 2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4) <
        18 / 25 * α)
    (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX₀ : 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ X)
    (hXc : 2 * Real.pi * Real.exp (c₀ / t) ≤ X) {y : ℝ} (hy0 : y ≠ 0) (hy : |y| ≤ 1 / 2) :
    riemannHeat t ((X : ℂ) + I * y) ≠ 0 :=
  riemannHeat_ne_zero_of_re_slope_pos ht
    (re_slope_pos_sharp_window hη hη4 hm hmc hc₀ hK hK0 hα₀ ht ht8 hX₀ hXc) hy0 hy

/-- **The sharp heat horizon.** For every `ε > 0` there is `X₀` such that for all `0 < t ≤ 1/8`, every
zero `z` of `H_t` with `|Re z| ≥ X₀` and `|Re z| ≥ 2π e^{(1 + √3/2 + ε)/t}` is real. -/
theorem riemannHeat_zeros_real_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      2 * Real.pi * Real.exp ((1 + Real.sqrt 3 / 2 + ε) / t) ≤ |z.re| → z.im = 0 := by
  set c₀ := 1 + Real.sqrt 3 / 2 + ε with hc₀def
  obtain ⟨η, m, hη, hη4, hm, hmc, -, hc₀, hδ⟩ := exists_sharp_params (c₀ := c₀) (by linarith)
  obtain ⟨K, hKpos, hK⟩ := exists_norm_xiLine_le_strip_convexity hη (by linarith)
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp
    (eventually_sharp_errors_small (c₀ := c₀) (K := K) (b := 9 / 2 * (1 / η + 3)) hη hm hδ)
  refine ⟨2 * Real.pi * Real.exp (2 * max α₀ 160), fun t ht ht8 z hz hX₀ hXc => ?_⟩
  have hnz : ∀ {X y : ℝ}, 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ X →
      2 * Real.pi * Real.exp (c₀ / t) ≤ X → y ≠ 0 → |y| ≤ 1 / 2 →
      riemannHeat t ((X : ℂ) + I * y) ≠ 0 := fun hX hXc' hy0 hy =>
    riemannHeat_ne_zero_sharp hη hη4 hm hmc hc₀ hK hKpos.le hα₀ ht ht8 hX hXc' hy0 hy
  have him := riemannHeat_zeros_im_sq_le ht hz
  have him2 : z.im ^ 2 ≤ 1 / 4 := him.trans (max_le (by linarith) (by norm_num))
  have him' : |z.im| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  by_contra hne
  rcases le_or_gt 0 z.re with h0 | h0
  · rw [abs_of_nonneg h0] at hX₀ hXc
    apply hnz hX₀ hXc hne him'
    rw [← hz]
    congr 1
    apply Complex.ext <;> simp
  · rw [abs_of_neg h0] at hX₀ hXc
    apply hnz (X := (-z).re) (by simpa using hX₀) (by simpa using hXc)
      (y := (-z).im) (by simpa using hne) (by simpa using him')
    rw [← hz, ← riemannHeat_neg ht.le]
    congr 1
    apply Complex.ext <;> simp

end

end RHTower.DeBruijn
