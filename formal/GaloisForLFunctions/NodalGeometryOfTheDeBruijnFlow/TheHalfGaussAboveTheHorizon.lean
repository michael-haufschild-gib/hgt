import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.SymmetricHalfCollisionLaw

/-!
# The half-Gauss transform above the horizon

Above the collision-free horizon `t log(X/2π) ≥ 6600/9991 + ε` the flow is a sum of two conjugate half-line Gaussian transforms,
`H_t(X) = 2 Re Q_X(0)`, `H_t'(X) = −2 Im Q_X'(0)`, and each of them is one exponential: with `a = α + iπ/4` the horizontal slope, `α = ½ log(X/2π)`, and
`P = |ξ(½ + 2tα + iX)| e^{−tα²}`,

`|Q − main| ≤ P/5`,  `|main| = P e^{−tπ²/16}`,  `|Q' − aQ| ≤ κ P`    (`exists_halfGauss_estimates`).

The second estimate has a constant `κ`, not a multiple of `α`. So `H_t` and `H_t'/α` are the two quadratures of an amplitude of size `≍ P`:
`|H_t(x)| ≤ (12/5) P`, and `P² ≤ 4(|H_t(x)|² + |H_t'(x)|²/α²)` (`exists_quadrature_bounds`). The amplitude is comparable at nearby heights
(`exists_scale_height_comparison`) and it rises at the exact exponential rate `e^{(t' − t)α²}` in heat time (`exists_scale_time_comparison`). These facts are the input to the frequency at the horizon.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

private theorem strip_exponent_collar_le' {w v δ₀ c Ew m : ℝ} (hw0 : 0 ≤ w) (hδ0 : 0 ≤ δ₀)
    (hv_lo : -δ₀ ≤ v) (hcw : w + δ₀ ≤ c) (hm : m ≤ (c - w) ^ 2 - 4 * c * Ew - 2 * δ₀ * c) :
    -(w - v) ^ 2 + 4 * c * Ew + 2 * c * (w - (v + c)) + c ^ 2 ≤ -m := by
  have hc_sub : 0 ≤ c - w - δ₀ := by linarith
  have hsq : (c - w - δ₀) ^ 2 ≤ (c - w + v) ^ 2 := by
    simpa [sq] using mul_self_le_mul_self hc_sub (by linarith : c - w - δ₀ ≤ c - w + v)
  have hid1 : -(w - v) ^ 2 + 2 * c * (w - (v + c)) + c ^ 2 = -(c - w + v) ^ 2 := by ring
  have hid2 : (c - w - δ₀) ^ 2 = (c - w) ^ 2 - 2 * δ₀ * c + 2 * δ₀ * w + δ₀ ^ 2 := by ring
  have hdw : 0 ≤ 2 * δ₀ * w := by positivity
  linarith [sq_nonneg δ₀]

/-- The derivative of the half-Gauss transform in the shift. -/
abbrev halfGaussSlope (t X v : ℝ) : ℂ :=
  ∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) * xiLine X w

/-- The two main estimates at a point `v` of the collar, for a general profile. -/
theorem halfGauss_estimates_of_profile {E : ℝ → ℝ} {K η δ₀ γ m t X v : ℝ}
    (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hη : 0 < η) (hγ : 0 ≤ γ)
    (hE0 : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η), 0 ≤ E w)
    (hE2 : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η), E w ≤ (1 / 2 + 2 * η) / 2)
    (hK : ∀ w u : ℝ, 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (E w) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 200 ≤ X) (hvδ : |v| ≤ δ₀) (hδ₀2 : δ₀ ≤ 1 / 2)
    (hα1 : 1 ≤ (horizontalSlope X).re)
    (hsep : 1 / 2 + 2 * η + γ ≤ -δ₀ + 2 * t * (horizontalSlope X).re)
    (hm : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      m ≤ (2 * t * (horizontalSlope X).re - w) ^ 2 -
        4 * (2 * t * (horizontalSlope X).re) * E w -
        2 * δ₀ * (2 * t * (horizontalSlope X).re))
    (hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)
    (hWX : 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2) :
    ∃ Main : ℂ, ‖Main‖ = (‖xiLine X (v + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) * Real.exp (-(t * (Real.pi / 4) ^ 2)) ∧
      ‖halfGaussTransform t (xiLine X) v - Main‖ ≤
        (‖xiLine X (v + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
        (chernoffLowerR1 γ t + kklR2 t (horizontalSlope X).re + sharpR3 (2 * η) t +
          sharpStripErr K (2 * η) m t (horizontalSlope X).re +
          Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re) ∧
      ‖halfGaussSlope t X v - horizontalSlope X * halfGaussTransform t (xiLine X) v‖ ≤
        (‖xiLine X (v + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
        (2 * sharpStripErr K (2 * η) m t (horizontalSlope X).re +
          Real.exp (9 / 2 * (1 / (2 * η) + 3)) *
            (kklRC t (horizontalSlope X).re + kklRB t (horizontalSlope X).re) +
          (1 / (2 * η) + 3) * (1 + sharpR3 (2 * η) t)) := by
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  have hv : |v| ≤ 1 / 2 := hvδ.trans hδ₀2
  have hv_lo : -δ₀ ≤ v := (abs_le.mp hvδ).1
  set a := horizontalSlope X with hadef
  set α := a.re with hαdef
  set u := v + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  set W := 2 * t * α + α ^ 2 with hWdef
  set η' := 2 * η with hη'
  have hη'pos : 0 < η' := by positivity
  set b := 9 / 2 * (1 / η' + 3) with hbdef
  have hv2 := (abs_le.mp hv).2
  have hWu : u ≤ W := by rw [hudef, hWdef]; linarith [one_le_pow₀ hα1 (n := 2)]
  have hu_sep : 1 / 2 + η' + γ ≤ u := by rw [hudef, hη']; linarith
  have hu : u ∈ Icc (1 / 2 + η') (X / 32 - 1 / 2) :=
    ⟨by linarith, hWu.trans hWX⟩
  have hw1W : 1 / 2 + η' ≤ W := hu.1.trans hWu
  have hN0 : 0 ≤ N := norm_nonneg _
  set P := N * Real.exp (-(t * α ^ 2)) with hP
  have hP0 : 0 ≤ P := by positivity
  have hmodel : ∀ w ∈ Icc (1 / 2 + η') W, ‖xiLine X w - xiLine X u *
      Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
        ‖xiLine X u‖ * Real.exp ((w - u) * a.re) * (Real.exp ((1 / η' + 3) * |w - u|) - 1) :=
    fun w hw => norm_xiLine_sub_model_le_near hX hη'pos hu ⟨hw.1, hw.2.trans hWX⟩
  have hderiv : ∀ w ∈ Icc (1 / 2 + η') W, ‖xiLineDeriv X w - a * xiLine X w‖ ≤
      (1 / η' + 3) * ‖xiLine X w‖ :=
    fun w hw => norm_xiLineDeriv_sub_le_near hX hη'pos hw.1 (hw.2.trans hWX)
  have hQ := norm_halfGaussTransform_sub_main_le ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (y := v) (by positivity) (by linarith) hw1W hmodel
  have hD := norm_slope_sub_mul_le ht (hasDerivAt_xiLine X) (continuous_xiLineDeriv X)
    (integrable_exp_mul_norm_xiLine ht X) (y := v) (by linarith) hw1W hderiv
  have hT1 := chernoff_lowerTail_le ht hγ hu_sep hN0
  have hT2 := upperTail_le ht hv hN0 (α := α)
  have hT3 := sharp_modelError_le (η := η') (α := α) (y := v) ht hη'pos hN0
  have hM := sharp_windowMass_le (η := η') ht hη'pos hX hu hWX
  have hcX : u ≤ X := by have := hu.2; linarith
  have hexp_strip : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      -(w - v) ^ 2 + 4 * (2 * t * α) * E w +
        2 * (2 * t * α) * (w - u) + (2 * t * α) ^ 2 ≤ -m := fun w hw => by
    rw [hudef]
    exact strip_exponent_collar_le' hw.1 ((abs_nonneg v).trans hvδ) hv_lo
      (by linarith [hw.2]) (hm w hw)
  obtain ⟨hSA, hOA, hB1⟩ := strip_terms_le_anchor_of_profile ht hη hE0 hE2 hK hK0
    (by linarith) hv hα0 hu.1 hcX hexp_strip
  have hFWb : ‖xiLine X W‖ ≤ (Real.exp b * N) * Real.exp ((W - u) * (α + 1 / 8)) :=
    norm_xiLine_far_end_le hX hη'pos hu hW9 hWu hWX
  obtain ⟨hSC, hOC, hB2⟩ := far_terms_le_of_bound (b := b) ht ht8 hX hv hα1 hW9 hFWb
  have hmain := norm_main_eq (t := t) (X := X) (y := v) (xiLine X u)
  rw [← hadef, ← hαdef, ← hudef] at hmain
  have hmain' : ‖xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (v * a + t * a ^ 2)‖ = P * Real.exp (-(t * (Real.pi / 4) ^ 2)) := by
    rw [hmain, hP, hN]
  set S₁ := chernoffLowerR1 γ t + kklR2 t α + sharpR3 η' t + sharpStripErr K η' m t α +
    Real.exp b * kklRC t α with hS₁
  set S₂ := 2 * sharpStripErr K η' m t α + Real.exp b * (kklRC t α + kklRB t α) +
    (1 / η' + 3) * (1 + sharpR3 η' t) with hS₂
  refine ⟨xiLine X u * Complex.exp (-((u : ℂ) * a)) * Complex.exp (v * a + t * a ^ 2), hmain', ?_, ?_⟩
  · refine hQ.trans ?_
    have e : ‖xiLine X u‖ * Real.exp (-(u * a.re)) *
        ((∫ w in Iic (1 / 2 + η' : ℝ), gaussDensity t (w - v) * Real.exp (w * a.re)) +
          (∫ w in Ioi W, gaussDensity t (w - v) * Real.exp (w * a.re)) +
          ∫ w, gaussDensity t (w - v) * Real.exp (w * a.re) *
            (Real.exp ((1 / η' + 3) * |w - u|) - 1)) =
        N * Real.exp (-(u * α)) * (∫ w in Iic (1 / 2 + η' : ℝ),
            gaussDensity t (w - v) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) * (∫ w in Ioi W, gaussDensity t (w - v) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) *
          ∫ w, gaussDensity t (w - v) * Real.exp (w * α) *
            (Real.exp ((1 / η' + 3) * |w - u|) - 1) := by ring
    rw [e]
    have hOC' : ∫ w in Ioi W, gaussDensity t (w - v) * ‖xiLine X w‖ ≤
        P * (Real.exp b * kklRC t α) := hOC.trans (le_of_eq (by rw [hP]; ring))
    rw [← hudef] at hT1 hT3
    have hsum : P * chernoffLowerR1 γ t + P * kklR2 t α + P * sharpR3 η' t +
        P * sharpStripErr K η' m t α + P * (Real.exp b * kklRC t α) = P * S₁ := by
      rw [hS₁]; ring
    linarith
  · refine hD.trans ?_
    have hSC' : ∫ w in Ioi W, (|(w - v) / (2 * t)| + ‖a‖) * gaussDensity t (w - v) *
        ‖xiLine X w‖ ≤ P * (Real.exp b * kklRC t α) := hSC.trans (le_of_eq (by rw [hP]; ring))
    have hB2' : gaussDensity t (W - v) * ‖xiLine X W‖ ≤ P * (Real.exp b * kklRB t α) :=
      hB2.trans (le_of_eq (by rw [hP]; ring))
    have hM' : (1 / η' + 3) * ∫ w in Ioc (1 / 2 + η') W, gaussDensity t (w - v) * ‖xiLine X w‖ ≤
        (1 / η' + 3) * (P * (1 + sharpR3 η' t)) := by gcongr
    have hsum : P * sharpStripErr K η' m t α + P * (Real.exp b * kklRC t α) +
        P * sharpStripErr K η' m t α + P * (Real.exp b * kklRB t α) +
        (1 / η' + 3) * (P * (1 + sharpR3 η' t)) = P * S₂ := by rw [hS₂]; ring
    linarith

/-- The super-exponentially small boundary term is eventually bounded. -/
private theorem eventually_exp_mul_RB_le (b : ℝ) :
    ∀ᶠ α : ℝ in atTop, Real.exp b * (2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
      (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) ≤ 1 := by
  have ht : Tendsto (fun α : ℝ => Real.exp b * (2 * (α ^ 1 * Real.exp (-α)))) atTop (𝓝 (Real.exp b * (2 * 0))) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 2 |>.const_mul _
  have hsmall : ∀ᶠ α : ℝ in atTop, Real.exp b * (2 * (α ^ 1 * Real.exp (-α))) < 1 :=
    ht.eventually (gt_mem_nhds (by simp))
  filter_upwards [hsmall, eventually_ge_atTop (160 : ℝ)] with α h1 hα
  refine le_trans ?_ h1.le
  have hα0 : 0 < α := by linarith only [hα]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos b).le
  rw [pow_one, ← mul_assoc]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have h2 : α ^ 2 / 2 ≤ α ^ 2 - 1 / 2 := by nlinarith only [hα]
  have h3 : (α ^ 2 / 2) ^ 2 ≤ (α ^ 2 - 1 / 2) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have h4 : (α ^ 2 / 2) ^ 2 * α / 80 ≤ (α ^ 2 - 1 / 2) ^ 2 * α / 80 := by
    have := mul_le_mul_of_nonneg_right h3 hα0.le
    linarith only [this]
  have h5 : 80 * α ^ 3 ≤ (α ^ 2 / 2) ^ 2 * α / 80 := by
    have h6 : 25600 ≤ α ^ 2 := by nlinarith only [hα]
    have h7 : 0 ≤ α ^ 3 := by positivity
    have h8 := mul_le_mul_of_nonneg_right h6 h7
    have h9 : (α ^ 2 / 2) ^ 2 * α / 80 = α ^ 2 * α ^ 3 / 320 := by ring
    rw [h9]
    linarith only [h8]
  have h10 : (α ^ 2 + 1 / 2) * (α + 1 / 8) + 21 * α ≤ 79 * α ^ 3 := by
    have h11 : 25600 ≤ α ^ 2 := by nlinarith only [hα]
    have h12 : 25600 * α ≤ α ^ 2 * α := mul_le_mul_of_nonneg_right h11 hα0.le
    nlinarith only [h12, hα, h11]
  have h13 : α ^ 3 ≥ 0 := by positivity
  linarith only [h4, h5, h10, h13]

/-- **The half-Gauss estimates above the horizon.** With `P = |ξ(½ + v + 2tα + iX)| e^{−tα²}`, `α = ½ log(X/2π)`, for `|v| ≤ δ₀` one has `(18/25) P ≤ |Q(v)| ≤ (6/5) P` and
`|Q'(v) − aQ(v)| ≤ κ P`, with `κ` independent of the height. -/
theorem exists_halfGauss_estimates {ε : ℝ} (hε : 0 < ε) :
    ∃ κ δ₀ X₀ : ℝ, 0 < κ ∧ 0 < δ₀ ∧ 200 ≤ X₀ ∧ ∀ t X v : ℝ, 0 < t → t ≤ 1 / 8 → X₀ ≤ X →
      6600 / 9991 + ε ≤ 2 * t * (horizontalSlope X).re → 2 * t * (horizontalSlope X).re ≤ 1 → |v| ≤ δ₀ →
      18 / 25 * (‖xiLine X (v + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) ≤ ‖halfGaussTransform t (xiLine X) v‖ ∧
      ‖halfGaussTransform t (xiLine X) v‖ ≤ 6 / 5 * (‖xiLine X (v + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) ∧
      ‖halfGaussSlope t X v - horizontalSlope X * halfGaussTransform t (xiLine X) v‖ ≤
        κ * (‖xiLine X (v + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) := by
  have hc₀ : 6600 / 9991 < 6600 / 9991 + ε := by linarith
  set c₀ := 6600 / 9991 + ε with hc₀def
  obtain ⟨η, δ₀, m, hη, hη40, hδ₀, hδ₀40, hm, hsep, hmc⟩ := exists_subWeyl_params hc₀
  obtain ⟨K, hKpos, hK⟩ := exists_norm_xiLine_le_strip_subWeyl hη hη40
  set b := 9 / 2 * (1 / (2 * η) + 3) with hbdef
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp
    ((eventually_interior_errors_small (η' := 2 * η) (δ₀ := δ₀) (γ := 1 / 10) (m := m) (K := K)
      (b := b) (by positivity) hδ₀ (by norm_num) hm).and (eventually_exp_mul_RB_le b))
  set η₁ := 1 / (2 * η) + 3 with hη₁
  have hη₁0 : 0 < η₁ := by positivity
  have h2π : 0 < 2 * Real.pi := by positivity
  refine ⟨2 + 2 * η₁, δ₀, 2 * Real.pi * Real.exp (2 * max α₀ 160), by positivity, hδ₀, ?_, ?_⟩
  · have h1 : (321 : ℝ) ≤ Real.exp (2 * max α₀ 160) := by
      have := Real.add_one_le_exp (2 * max α₀ 160)
      have : (320 : ℝ) ≤ 2 * max α₀ 160 := by linarith [le_max_right α₀ 160]
      linarith
    nlinarith only [h1, Real.pi_gt_three]
  intro t X v ht ht8 hX hc h2tα hv
  have hX200 : 200 ≤ X := by
    have h1 : (321 : ℝ) ≤ Real.exp (2 * max α₀ 160) := by
      have := Real.add_one_le_exp (2 * max α₀ 160)
      have : (320 : ℝ) ≤ 2 * max α₀ 160 := by linarith [le_max_right α₀ 160]
      linarith
    nlinarith only [hX, h1, Real.pi_gt_three]
  have hX0 : 0 < X := by linarith only [hX200]
  obtain ⟨α, hαdef⟩ : ∃ α, α = (horizontalSlope X).re := ⟨_, rfl⟩
  have hαlog : α = Real.log (X / (2 * Real.pi)) / 2 := by rw [hαdef, horizontalSlope_re]
  have hαbig : max α₀ 160 ≤ α := by
    have h1 : Real.exp (2 * max α₀ 160) ≤ X / (2 * Real.pi) := by
      rw [le_div_iff₀ h2π]
      linarith only [hX]
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    rw [hαlog]
    linarith only [h2]
  have hα160 : 160 ≤ α := (le_max_right _ _).trans hαbig
  have hαα₀ : α₀ ≤ α := (le_max_left _ _).trans hαbig
  have hα0 : 0 < α := by linarith only [hα160]
  rw [← hαdef] at hc h2tα ⊢
  have htα : t * α ≤ 1 / 2 := by linarith only [h2tα]
  have hct : c₀ / (2 * α) ≤ t := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hc]
  have ht20 : t ≤ 20 / α := by
    rw [le_div_iff₀ hα0]
    linarith only [htα]
  obtain ⟨⟨-, hη₁α, hsum1, -, -⟩, hRB⟩ := hα₀ α hαα₀
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := interior_error_bounds (c₀ := c₀) (η' := 2 * η)
    (γ := 1 / 10) (m := m) (K := K) (by positivity) (by linarith only [hη40]) (by norm_num) hm hKpos.le
    (by linarith only [hc₀]) hα160 hη₁α hct ht20
  have hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := by
    rw [← hαdef]
    have h1 : (0 : ℝ) ≤ 2 * t * α := by positivity
    have h2 : (9 : ℝ) / 2 ≤ α ^ 2 := by nlinarith only [hα160]
    linarith only [h1, h2]
  have hαre160 : 160 ≤ (horizontalSlope X).re := by rwa [← hαdef]
  have hWX := window_fits ht8 ht hX0 (by linarith only [hαre160])
  obtain ⟨Main, hMain, hQ, hD⟩ := halfGauss_estimates_of_profile (E := subWeylStripExp η)
    (K := K) (η := η) (δ₀ := δ₀) (γ := 1 / 10) (m := m) (t := t) (X := X) (v := v) ht ht8 hη (by norm_num)
    (fun w hw => subWeylStripExp_nonneg hη.le hw.2)
    (fun w hw => subWeylStripExp_le_quarter_add hη.le (by linarith only [hη40]) hw.1)
    (fun w u h1 h2 h3 h4 => hK X w u (by linarith only [hX200]) h1 h2 h3 h4) hKpos.le hX200 hv
    (by linarith only [hδ₀40]) (by linarith only [hαre160])
    (by rw [← hαdef]; linarith only [hsep, hc])
    (by rw [← hαdef]; exact hmc _ hc) hW9 hWX
  rw [← hαdef] at hMain hQ hD
  set P := ‖xiLine X (v + 2 * t * α)‖ * Real.exp (-(t * α ^ 2)) with hP
  have hP0 : 0 ≤ P := by positivity
  -- smallness of the error terms
  have he1 : 0 ≤ Real.exp (-((1 / 10 : ℝ) ^ 2 / 80) * α) := (Real.exp_pos _).le
  have he2 : 0 ≤ Real.exp (-α ^ 2 + 1) := (Real.exp_pos _).le
  have he3 : 0 ≤ 2 * (1 / (2 * η) + 3) * Real.sqrt (20 / α) * Real.exp 4 := by positivity
  have he4 : 0 ≤ 40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) := by positivity
  have he5 : 0 ≤ Real.exp b * (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) := by
    positivity
  have heb := (Real.exp_pos b).le
  have hS1 : chernoffLowerR1 (1 / 10) t + kklR2 t α + sharpR3 (2 * η) t +
      sharpStripErr K (2 * η) m t α + Real.exp b * kklRC t α ≤ 1 / 5 := by
    have := mul_le_mul_of_nonneg_left b5 heb
    linarith only [this, b1, b2, b3, b4, hsum1]
  have hS2 : 2 * sharpStripErr K (2 * η) m t α + Real.exp b * (kklRC t α + kklRB t α) +
      η₁ * (1 + sharpR3 (2 * η) t) ≤ 2 + 2 * η₁ := by
    have h5 := mul_le_mul_of_nonneg_left b5 heb
    have h6 := mul_le_mul_of_nonneg_left b6 heb
    have hstrip : sharpStripErr K (2 * η) m t α ≤ 1 / 5 := by
      linarith only [b4, hsum1, he1, he2, he3, he5]
    have hR3 : sharpR3 (2 * η) t ≤ 1 / 5 := by
      linarith only [b3, hsum1, he1, he2, he4, he5]
    have hRC : Real.exp b * kklRC t α ≤ 1 / 5 := by
      linarith only [h5, hsum1, he1, he2, he3, he4]
    have hRB' : Real.exp b * kklRB t α ≤ 1 := h6.trans hRB
    have h7 := mul_le_mul_of_nonneg_left hR3 hη₁0.le
    rw [mul_add]
    nlinarith only [hstrip, hRC, hRB', h7, hη₁0]
  have hphase := gaussPhase_ge ht8 ht
  have hphase1 : Real.exp (-(t * (Real.pi / 4) ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ t * (Real.pi / 4) ^ 2 := by positivity
    linarith only [this]
  have hQ' : ‖halfGaussTransform t (xiLine X) v - Main‖ ≤ P * (1 / 5) :=
    hQ.trans (mul_le_mul_of_nonneg_left hS1 hP0)
  have htri1 := norm_sub_norm_le Main (Main - halfGaussTransform t (xiLine X) v)
  rw [sub_sub_cancel, norm_sub_rev Main] at htri1
  have htri2 := norm_add_le (halfGaussTransform t (xiLine X) v - Main) Main
  rw [sub_add_cancel] at htri2
  have hM1 := mul_le_mul_of_nonneg_left hphase hP0
  have hM2 := mul_le_mul_of_nonneg_left hphase1 hP0
  refine ⟨?_, ?_, ?_⟩
  · rw [hMain] at htri1
    linarith only [htri1, hQ', hM1]
  · rw [hMain] at htri2
    linarith only [htri2, hQ', hM2]
  · refine hD.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hS2 hP0

/-! ## The amplitude -/

/-- The amplitude `P = |ξ(½ + 2tα + iX)| e^{−tα²}` of the flow at height `X` and time `t`. -/
def horizonAmp (t X : ℝ) : ℝ :=
  ‖xiLine X (2 * t * (horizontalSlope X).re)‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2))

theorem horizonAmp_nonneg (t X : ℝ) : 0 ≤ horizonAmp t X := by
  unfold horizonAmp
  positivity

/-- **The two quadratures of the amplitude.** Above the horizon `|H_t(x)| ≤ (12/5) P` and `P² ≤ 4(|H_t(x)|² + |H_t'(x)|²/α²)`. -/
theorem exists_quadrature_bounds {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, 200 ≤ X₀ ∧ ∀ t x : ℝ, 0 < t → t ≤ 1 / 8 → X₀ ≤ x →
      6600 / 9991 + ε ≤ 2 * t * (horizontalSlope x).re → 2 * t * (horizontalSlope x).re ≤ 1 →
      ‖riemannHeat t (x : ℂ)‖ ≤ 12 / 5 * horizonAmp t x ∧
      horizonAmp t x ^ 2 ≤ 4 * (‖riemannHeat t (x : ℂ)‖ ^ 2 +
        ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 / (horizontalSlope x).re ^ 2) := by
  obtain ⟨κ, δ₀, X₁, hκ, hδ₀, hX₁, hest⟩ := exists_halfGauss_estimates hε
  have h2π : 0 < 2 * Real.pi := by positivity
  refine ⟨max X₁ (2 * Real.pi * Real.exp (8 * (1 + κ))), hX₁.trans (le_max_left _ _), ?_⟩
  intro t x ht ht8 hx hc h2t
  have hxX₁ : X₁ ≤ x := (le_max_left _ _).trans hx
  have hxe : 2 * Real.pi * Real.exp (8 * (1 + κ)) ≤ x := (le_max_right _ _).trans hx
  set α := (horizontalSlope x).re with hαdef
  have hαbig : 4 * (1 + κ) ≤ α := by
    have h1 : Real.exp (8 * (1 + κ)) ≤ x / (2 * Real.pi) := by
      rw [le_div_iff₀ h2π]
      linarith only [hxe]
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    rw [hαdef, horizontalSlope_re]
    linarith only [h2]
  have hα0 : 0 < α := by linarith only [hαbig, hκ]
  obtain ⟨hlow, hup, hE⟩ := hest t x 0 ht ht8 hxX₁ hc h2t (by rw [abs_zero]; exact hδ₀.le)
  rw [zero_add] at hlow hup hE
  have hPdef : ‖xiLine x (2 * t * α)‖ * Real.exp (-(t * α ^ 2)) = horizonAmp t x := rfl
  rw [← hαdef, hPdef] at hlow hup hE
  set P := horizonAmp t x with hP
  have hP0 : 0 ≤ P := horizonAmp_nonneg t x
  set A := halfGaussTransform t (xiLine x) 0 with hA
  set D := deriv (halfGaussTransform t (xiLine x)) 0 with hD
  have hDeq : D = halfGaussSlope t x 0 :=
    (hasDerivAt_halfGaussTransform ht (continuous_xiLine x) (integrable_exp_mul_norm_xiLine ht x) 0).deriv
  have hH : riemannHeat t (x : ℂ) = ((2 * A.re : ℝ) : ℂ) := riemannHeat_ofReal_eq_two_re_halfGauss ht x
  have hH' : deriv (riemannHeat t) (x : ℂ) = ((-2 * D.im : ℝ) : ℂ) :=
    deriv_riemannHeat_ofReal_eq_neg_two_im_deriv_halfGauss ht x
  have hnH : ‖riemannHeat t (x : ℂ)‖ ^ 2 = 4 * A.re ^ 2 := by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hnH' : ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 = 4 * D.im ^ 2 := by
    rw [hH', Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  constructor
  · rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := Complex.abs_re_le_norm A
    linarith only [this, hup]
  · rw [hnH, hnH']
    have hnormA : ‖A‖ ^ 2 = A.re ^ 2 + A.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hlow2 : (18 / 25 * P) ^ 2 ≤ ‖A‖ ^ 2 := pow_le_pow_left₀ (by positivity) hlow 2
    rw [hnormA] at hlow2
    have hfrac : 0 ≤ 4 * D.im ^ 2 / α ^ 2 := by positivity
    by_cases hcase : P ^ 2 / 4 ≤ A.re ^ 2
    · nlinarith only [hcase, hfrac]
    · have hcase' := not_le.mp hcase
      have him2 : (P / 2) ^ 2 ≤ A.im ^ 2 := by nlinarith only [hlow2, hcase', sq_nonneg P]
      have hre2 : A.re ^ 2 ≤ (P / 2) ^ 2 := by nlinarith only [hcase']
      have him : P / 2 ≤ |A.im| :=
        (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp (by rwa [sq_abs])
      have hre : |A.re| ≤ P / 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by rwa [sq_abs])
      -- the imaginary part of the slope
      set E := D - horizontalSlope x * A with hEdef
      have hEn : |E.im| ≤ κ * P := by
        refine (Complex.abs_im_le_norm E).trans ?_
        rw [hEdef, hDeq]
        exact hE
      have hDim : D.im = α * A.im + Real.pi / 4 * A.re + E.im := by
        have h1 : D = horizontalSlope x * A + E := by rw [hEdef]; ring
        rw [h1, Complex.add_im, Complex.mul_im, horizontalSlope_im]
      have hpi : Real.pi / 4 ≤ 1 := by linarith only [Real.pi_lt_d2]
      have hpi0 : 0 ≤ Real.pi / 4 := by positivity
      have hmain : α * P / 2 ≤ |D.im| + P / 2 + κ * P := by
        have h1 : α * A.im = D.im - Real.pi / 4 * A.re - E.im := by rw [hDim]; ring
        have h2 : |α * A.im| = α * |A.im| := by rw [abs_mul, abs_of_pos hα0]
        have h3 : |α * A.im| ≤ |D.im| + |Real.pi / 4 * A.re| + |E.im| := by
          rw [h1]
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        have h4 : |Real.pi / 4 * A.re| ≤ P / 2 := by
          rw [abs_mul, abs_of_nonneg hpi0]
          have : Real.pi / 4 * |A.re| ≤ 1 * |A.re| := mul_le_mul_of_nonneg_right hpi (abs_nonneg _)
          linarith only [this, hre]
        have h5 : α * (P / 2) ≤ α * |A.im| := mul_le_mul_of_nonneg_left him hα0.le
        linarith only [h2, h3, h4, h5, hEn]
      have hquarter : α * P / 4 ≤ |D.im| := by
        have h1 : 4 * (1 + κ) * P ≤ α * P := mul_le_mul_of_nonneg_right hαbig hP0
        nlinarith only [hmain, h1, hP0]
      have hsq : (α * P / 4) ^ 2 ≤ D.im ^ 2 := by
        rw [← sq_abs D.im]
        exact pow_le_pow_left₀ (by positivity) hquarter 2
      have hdiv : P ^ 2 / 4 ≤ 4 * D.im ^ 2 / α ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith only [hsq]
      have hre0 : 0 ≤ A.re ^ 2 := sq_nonneg _
      linarith only [hdiv, hre0]

/-- The log-linear bound on a vertical line of the Euler half-plane. -/
theorem norm_xiLine_le_model {X u w : ℝ} (hX : 200 ≤ X) (hu : 3 / 5 ≤ u) (huX : u ≤ X / 32 - 1 / 2)
    (hw : 3 / 5 ≤ w) (hwX : w ≤ X / 32 - 1 / 2) :
    ‖xiLine X w‖ ≤ ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) * Real.exp (13 * |w - u|) := by
  have h := norm_xiLine_sub_model_le_near (X := X) (u := u) (w := w) (ε := 1 / 10) hX (by norm_num)
    ⟨by linarith only [hu], huX⟩ ⟨by linarith only [hw], hwX⟩
  have hc : (1 / (1 / 10 : ℝ) + 3) = 13 := by norm_num
  rw [hc] at h
  have htri := norm_add_le (xiLine X w - xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X))
    (xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X))
  rw [sub_add_cancel, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul] at htri
  have hrw : ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) * Real.exp (13 * |w - u|) =
      ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) * (Real.exp (13 * |w - u|) - 1) +
        ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) := by ring
  rw [hrw]
  linarith only [h, htri]

/-- The height derivative of `ξ` on a vertical line. -/
theorem hasDerivAt_xiLine_height' (u x : ℝ) :
    HasDerivAt (fun v : ℝ => xiLine v u) (I * xiLineDeriv x u) x := by
  have hin : HasDerivAt (fun v : ℂ => (1 / 2 : ℂ) + (u : ℂ) + I * v) I (x : ℂ) := by
    have h := ((hasDerivAt_id' (x : ℂ)).const_mul I).const_add ((1 / 2 : ℂ) + (u : ℂ))
    simpa only [mul_one] using h
  have h := (xi_differentiable ((1 / 2 : ℂ) + (u : ℂ) + I * x)).hasDerivAt.comp (x : ℂ) hin
  simpa only [xiLine, xiLineDeriv, Function.comp_def, mul_comm I] using h.comp_ofReal

/-- The slope changes slowly with the height. -/
theorem abs_horizontalSlope_re_sub_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |(horizontalSlope y).re - (horizontalSlope x).re| ≤ |y - x| / min x y := by
  have h2π : 0 < 2 * Real.pi := by positivity
  rw [horizontalSlope_re, horizontalSlope_re]
  have hratio : Real.log (y / (2 * Real.pi)) / 2 - Real.log (x / (2 * Real.pi)) / 2 =
      Real.log (y / x) / 2 := by
    rw [Real.log_div hy.ne' h2π.ne', Real.log_div hx.ne' h2π.ne', Real.log_div hy.ne' hx.ne']
    ring
  rw [hratio, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmin : 0 < min x y := lt_min hx hy
  have h1 : Real.log (y / x) ≤ |y - x| / min x y := by
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [show y / x - 1 = (y - x) / x by field_simp]
    calc (y - x) / x ≤ |y - x| / x := div_le_div_of_nonneg_right (le_abs_self _) hx.le
      _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _) hmin (min_le_left _ _)
  have h2 : -Real.log (y / x) ≤ |y - x| / min x y := by
    rw [← Real.log_inv, inv_div]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [show x / y - 1 = (x - y) / y by field_simp, abs_sub_comm]
    calc (x - y) / y ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy.le
      _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _) hmin (min_le_right _ _)
  have h3 : |Real.log (y / x)| ≤ |y - x| / min x y := abs_le.mpr ⟨by linarith only [h2], h1⟩
  have h4 : 0 ≤ |y - x| / min x y := by positivity
  linarith only [h3, h4]

/-- **Nearby heights.** On a vertical line of the Euler half-plane the size of `ξ` changes by a bounded factor per unit of height. -/
theorem norm_xiLine_height_le {u x y : ℝ} (hx : 400 ≤ x) (hxy : |y - x| ≤ x / 2) (hu : 3 / 5 ≤ u)
    (hux : u ≤ x / 64 - 1 / 2) :
    ‖xiLine y u‖ ≤ ‖xiLine x u‖ * Real.exp (15 * |y - x|) := by
  have hmem (s : ℝ) (hs : s ∈ uIcc x y) : x / 2 ≤ s := by
    rcases le_total x y with h | h
    · rw [uIcc_of_le h] at hs
      linarith only [hs.1, hx]
    · rw [uIcc_of_ge h] at hs
      have := (abs_le.mp hxy).1
      linarith only [hs.1, this]
  have hmem2 (s : ℝ) (hs : s ∈ uIcc x y) : |s - x| ≤ x / 2 := by
    rcases le_total x y with h | h
    · rw [uIcc_of_le h] at hs
      rw [abs_of_nonneg (by linarith only [hs.1])]
      have := (abs_le.mp hxy).2
      linarith only [hs.2, this]
    · rw [uIcc_of_ge h] at hs
      rw [abs_of_nonpos (by linarith only [hs.2])]
      have := (abs_le.mp hxy).1
      linarith only [hs.1, this]
  have hb : ∀ s ∈ uIcc x y, ‖I * xiLineDeriv s u - (I * horizontalSlope x) * xiLine s u‖ ≤
      14 * ‖xiLine s u‖ := by
    intro s hs
    have hs1 := hmem s hs
    have hs2 := hmem2 s hs
    have hs200 : 200 ≤ s := by linarith only [hs1, hx]
    have hus : u ≤ s / 32 - 1 / 2 := by linarith only [hux, hs1]
    have h1 := norm_xiLineDeriv_sub_le_near (X := s) (w := u) (ε := 1 / 10) hs200 (by norm_num)
      (by linarith only [hu]) hus
    have hc : (1 / (1 / 10 : ℝ) + 3) = 13 := by norm_num
    rw [hc] at h1
    have h2 : ‖horizontalSlope s - horizontalSlope x‖ ≤ 1 := by
      have h3 : horizontalSlope s - horizontalSlope x =
          (((horizontalSlope s).re - (horizontalSlope x).re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [horizontalSlope_im]
      rw [h3, Complex.norm_real, Real.norm_eq_abs]
      have hxpos : 0 < x := by linarith only [hx]
      have hspos : 0 < s := by linarith only [hs200]
      refine (abs_horizontalSlope_re_sub_le hxpos hspos).trans ?_
      have hmin : x / 2 ≤ min x s := le_min (by linarith only [hx]) hs1
      rw [div_le_one (lt_of_lt_of_le (by positivity) hmin)]
      exact hs2.trans hmin
    have h4 : I * xiLineDeriv s u - (I * horizontalSlope x) * xiLine s u =
        I * ((xiLineDeriv s u - horizontalSlope s * xiLine s u) +
          (horizontalSlope s - horizontalSlope x) * xiLine s u) := by ring
    rw [h4, norm_mul, Complex.norm_I, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h5 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (xiLine s u))
    linarith only [h1, h5]
  have hm := GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le (a := I * horizontalSlope x) (η := 14)
    (u := x) (w := y) (by norm_num) (fun s _ => hasDerivAt_xiLine_height' u s) hb
  have hre : (I * horizontalSlope x).re = -(Real.pi / 4) := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, horizontalSlope_im]
    ring
  rw [hre] at hm
  have htri := norm_add_le (xiLine y u - xiLine x u * Complex.exp (((y - x : ℝ) : ℂ) * (I * horizontalSlope x)))
    (xiLine x u * Complex.exp (((y - x : ℝ) : ℂ) * (I * horizontalSlope x)))
  rw [sub_add_cancel, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, hre] at htri
  have hexp1 : Real.exp ((y - x) * -(Real.pi / 4)) ≤ Real.exp |y - x| := by
    apply Real.exp_le_exp.mpr
    have h1 : Real.pi / 4 ≤ 1 := by linarith only [Real.pi_lt_d2]
    have h2 : 0 ≤ Real.pi / 4 := by positivity
    have h3 : (y - x) * -(Real.pi / 4) ≤ |y - x| * (Real.pi / 4) := by
      have := neg_abs_le (y - x)
      nlinarith only [this, h2]
    have h4 : |y - x| * (Real.pi / 4) ≤ |y - x| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    linarith only [h3, h4]
  have hn := norm_nonneg (xiLine x u)
  have hbig : ‖xiLine x u‖ * Real.exp ((y - x) * -(Real.pi / 4)) * Real.exp (14 * |y - x|) ≤
      ‖xiLine x u‖ * Real.exp (15 * |y - x|) := by
    have heq : Real.exp (15 * |y - x|) = Real.exp |y - x| * Real.exp (14 * |y - x|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hn
    exact mul_le_mul_of_nonneg_right hexp1 (Real.exp_pos _).le
  have hexpand : ‖xiLine x u‖ * Real.exp ((y - x) * -(Real.pi / 4)) * Real.exp (14 * |y - x|) =
      ‖xiLine x u‖ * Real.exp ((y - x) * -(Real.pi / 4)) * (Real.exp (14 * |y - x|) - 1) +
        ‖xiLine x u‖ * Real.exp ((y - x) * -(Real.pi / 4)) := by ring
  linarith only [hm, htri, hbig, hexpand]

/-- **The amplitude at nearby heights.** -/
theorem horizonAmp_height_le {t x y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hx : 400 ≤ x) (hxy : |y - x| ≤ x / 2)
    (hxlo : 3 / 5 ≤ 2 * t * (horizontalSlope x).re) (hxhi : 2 * t * (horizontalSlope x).re ≤ 1)
    (hylo : 3 / 5 ≤ 2 * t * (horizontalSlope y).re) (hyhi : 2 * t * (horizontalSlope y).re ≤ 1) :
    horizonAmp t y ≤ horizonAmp t x * Real.exp (22 * |y - x|) := by
  set α := (horizontalSlope x).re with hα
  set β := (horizontalSlope y).re with hβ
  have hy200 : 200 ≤ y := by
    have := (abs_le.mp hxy).1
    linarith only [this, hx]
  have hxpos : 0 < x := by linarith only [hx]
  have hypos : 0 < y := by linarith only [hy200]
  have hmin : 1 ≤ min x y := le_min (by linarith only [hx]) (by linarith only [hy200])
  have he : |β - α| ≤ |y - x| := by
    refine (abs_horizontalSlope_re_sub_le hxpos hypos).trans ?_
    exact div_le_self (abs_nonneg _) hmin
  have hα0 : 0 < α := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * t) (not_lt.mp h)
    linarith only [this, hxlo]
  have hβ0 : 0 < β := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * t) (not_lt.mp h)
    linarith only [this, hylo]
  -- step from `2tβ` to `2tα` at height `y`
  have h1 := norm_xiLine_le_model (X := y) (u := 2 * t * α) (w := 2 * t * β) hy200 hxlo
    (by linarith only [hxhi, hy200]) hylo (by linarith only [hyhi, hy200])
  rw [← hβ] at h1
  -- step in height
  have h2 := norm_xiLine_height_le (u := 2 * t * α) hx hxy hxlo (by linarith only [hxhi, hx])
  unfold horizonAmp
  rw [← hα, ← hβ]
  set A := ‖xiLine x (2 * t * α)‖ with hA
  set e := |y - x| with heDef
  have he0 : 0 ≤ e := abs_nonneg _
  have hdiff : |2 * t * β - 2 * t * α| ≤ e / 4 := by
    rw [show 2 * t * β - 2 * t * α = 2 * t * (β - α) by ring, abs_mul,
      abs_of_pos (by positivity : 0 < 2 * t)]
    have : 2 * t * |β - α| ≤ 2 * t * e := mul_le_mul_of_nonneg_left he (by positivity)
    nlinarith only [this, ht8, he0]
  have hE1 : (2 * t * β - 2 * t * α) * β - t * β ^ 2 ≤ -(t * α ^ 2) + e := by
    have h3 : (2 * t * β - 2 * t * α) * β - t * β ^ 2 + t * α ^ 2 = t * (β - α) ^ 2 := by ring
    have h4 : (β - α) ^ 2 = |β - α| * |β - α| := by
      rw [← sq, sq_abs]
    have h5 : t * |β - α| ≤ 1 := by
      have h6 : |β - α| ≤ α + β := by
        rw [abs_le]
        constructor <;> linarith only [hα0, hβ0]
      have h7 : t * |β - α| ≤ t * (α + β) := mul_le_mul_of_nonneg_left h6 ht.le
      nlinarith only [h7, hxhi, hyhi]
    have h8 : t * (β - α) ^ 2 ≤ e := by
      rw [h4, ← mul_assoc]
      calc t * |β - α| * |β - α| ≤ 1 * |β - α| := mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
        _ ≤ e := by rw [one_mul]; exact he
    linarith only [h3, h8]
  calc ‖xiLine y (2 * t * β)‖ * Real.exp (-(t * β ^ 2))
      ≤ (‖xiLine y (2 * t * α)‖ * Real.exp ((2 * t * β - 2 * t * α) * β) *
          Real.exp (13 * |2 * t * β - 2 * t * α|)) * Real.exp (-(t * β ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ ((A * Real.exp (15 * e)) * Real.exp ((2 * t * β - 2 * t * α) * β) *
          Real.exp (13 * (e / 4))) * Real.exp (-(t * β ^ 2)) := by
        gcongr
    _ = A * Real.exp ((2 * t * β - 2 * t * α) * β - t * β ^ 2 + 15 * e + 13 * (e / 4)) := by
        simp only [Real.exp_add, Real.exp_sub, Real.exp_neg]
        field_simp
    _ ≤ A * Real.exp (-(t * α ^ 2) + 22 * e) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        linarith only [hE1, he0]
    _ = _ := by
        rw [Real.exp_add]
        ring

/-- **The amplitude in heat time.** It rises at the exact exponential rate `α²`. -/
theorem horizonAmp_time_le {t₁ t₂ X : ℝ} (ht : t₁ ≤ t₂) (hX : 200 ≤ X)
    (hlo : 3 / 5 ≤ 2 * t₁ * (horizontalSlope X).re) (hhi : 2 * t₂ * (horizontalSlope X).re ≤ 1) :
    horizonAmp t₂ X ≤ horizonAmp t₁ X *
      Real.exp ((t₂ - t₁) * (horizontalSlope X).re ^ 2 + 26 * ((t₂ - t₁) * (horizontalSlope X).re)) := by
  set α := (horizontalSlope X).re with hα
  have hα0 : 0 ≤ α := by
    by_contra hneg
    have h1 := not_le.mp hneg
    have hX' : (1 : ℝ) ≤ X / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hX, Real.pi_lt_d2]
    have := Real.log_nonneg hX'
    rw [hα, horizontalSlope_re] at h1
    linarith only [h1, this]
  have hu2 : 2 * t₁ * α ≤ 2 * t₂ * α := by
    have := mul_le_mul_of_nonneg_right ht hα0
    linarith only [this]
  have h := norm_xiLine_le_model (X := X) (u := 2 * t₁ * α) (w := 2 * t₂ * α) hX hlo
    (by linarith only [hu2, hhi, hX]) (by linarith only [hu2, hlo]) (by linarith only [hhi, hX])
  rw [← hα, abs_of_nonneg (by linarith only [hu2])] at h
  unfold horizonAmp
  rw [← hα]
  calc ‖xiLine X (2 * t₂ * α)‖ * Real.exp (-(t₂ * α ^ 2))
      ≤ (‖xiLine X (2 * t₁ * α)‖ * Real.exp ((2 * t₂ * α - 2 * t₁ * α) * α) *
          Real.exp (13 * (2 * t₂ * α - 2 * t₁ * α))) * Real.exp (-(t₂ * α ^ 2)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = ‖xiLine X (2 * t₁ * α)‖ * Real.exp (-(t₁ * α ^ 2)) *
          Real.exp ((t₂ - t₁) * α ^ 2 + 26 * ((t₂ - t₁) * α)) := by
        rw [mul_assoc (‖xiLine X (2 * t₁ * α)‖), mul_assoc (‖xiLine X (2 * t₁ * α)‖),
          mul_assoc (‖xiLine X (2 * t₁ * α)‖), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- The anchor `|ξ(16.5 + iX)|` is at most a power of `X` times the amplitude. -/
theorem norm_xiLine_sixteen_le_horizonAmp {t X : ℝ} (ht : 0 < t) (hX : 600 ≤ X)
    (hlo : 3 / 5 ≤ 2 * t * (horizontalSlope X).re) (hhi : 2 * t * (horizontalSlope X).re ≤ 1) :
    ‖xiLine X 16‖ ≤ horizonAmp t X * Real.exp (17 * (horizontalSlope X).re + 208) := by
  set α := (horizontalSlope X).re with hα
  have hα0 : 0 < α := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * t) (not_lt.mp h)
    linarith only [this, hlo]
  have hu0 : 0 ≤ 2 * t * α := by positivity
  have h := norm_xiLine_le_model (X := X) (u := 2 * t * α) (w := 16) (by linarith only [hX]) hlo
    (by linarith only [hhi, hX]) (by norm_num) (by linarith only [hX])
  rw [← hα, abs_of_nonneg (by linarith only [hhi])] at h
  unfold horizonAmp
  rw [← hα]
  have hexp : Real.exp ((16 - 2 * t * α) * α) * Real.exp (13 * (16 - 2 * t * α)) ≤
      Real.exp (-(t * α ^ 2)) * Real.exp (17 * α + 208) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : t * α ≤ 1 := by linarith only [hhi, hu0]
    have h2 : t * α ^ 2 ≤ α := by
      have := mul_le_mul_of_nonneg_right h1 hα0.le
      nlinarith only [this]
    have h3 : 0 ≤ t * α ^ 2 := by positivity
    nlinarith only [h2, h3, hu0, hα0]
  calc ‖xiLine X 16‖ ≤ ‖xiLine X (2 * t * α)‖ * Real.exp ((16 - 2 * t * α) * α) *
        Real.exp (13 * (16 - 2 * t * α)) := h
    _ = ‖xiLine X (2 * t * α)‖ * (Real.exp ((16 - 2 * t * α) * α) * Real.exp (13 * (16 - 2 * t * α))) := by
        ring
    _ ≤ ‖xiLine X (2 * t * α)‖ * (Real.exp (-(t * α ^ 2)) * Real.exp (17 * α + 208)) :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ = _ := by ring

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
