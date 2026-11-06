import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightErrorDecay

/-!
# The typical envelopes at a power of the logarithm

The error envelopes of the half-Gauss transform at a typical height stay small when the size `η` of the zero-free box shrinks with the height. With `η = 1/u⁴` and a slope `α ≍ u²⁰`, that is `η ≍ α^{−1/5}`, all of them
are `≪ 1/u` (`typical_envelopes_small`). The point is the model envelope `2v e^{(1+v)²}`, `v = b/√α`, with `b ≍ log α/η²` the slope error on the box. It requires `η ≫ α^{−1/4}`, up to a logarithm: the Gaussian width `≍ 1/√α` must not feel the slope error.
-/

open Real
open GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

theorem exp_neg_le_one_div {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 1 / y := by
  rw [Real.exp_neg, one_div]
  refine inv_anti₀ hy ?_
  linarith only [Real.add_one_le_exp y]

theorem exp_neg_le_of_le {y c : ℝ} (hc : 0 < c) (h : c ≤ y) : Real.exp (-y) ≤ 1 / c :=
  (exp_neg_le_one_div (hc.trans_le h)).trans (one_div_le_one_div_of_le hc h)

/-- **The envelopes along a power of the logarithm.** -/
theorem typical_envelopes_small {u α : ℝ} (hu : (10 : ℝ) ^ 9 ≤ u) (hα1 : u ^ 20 / 8 ≤ α) (hα2 : α ≤ u ^ 20) :
    typicalSlopeEnvelope (1 / u ^ 4) α ≤ 2 / 9 * α ∧
    typicalTailLogEnvelope (1 / u ^ 4) α ≤ (1 / u ^ 4) ^ 2 * α ∧
    typicalMainEnvelope (1 / u ^ 4) α ≤ 1 / 5 ∧
    typicalSlopeNormalizedEnvelope (1 / u ^ 4) α ≤ 1 / 100 ∧
    typicalOppositeEnvelope (1 / u ^ 4) α ≤ 1 / 2 := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  set p := u ^ 4 with hp
  have hp0 : 0 < p := by positivity
  have hpu : u ≤ p := by
    rw [hp]
    exact le_self_pow₀ hu1 (by norm_num)
  have hpu3 : u ^ 3 ≤ p := by
    rw [hp]
    exact pow_le_pow_right₀ hu1 (by norm_num)
  have hQ : u ^ 20 = p ^ 5 := by
    rw [hp]
    ring
  rw [hQ] at hα1 hα2
  have hp1 : (10 : ℝ) ^ 9 ≤ p := hu.trans hpu
  have hα0 : 0 < α := lt_of_lt_of_le (by positivity) hα1
  have hu2 : 1 / u ≤ 1 / (10 : ℝ) ^ 9 := one_div_le_one_div_of_le (by positivity) hu
  have hup0 : 0 < 1 / u := by positivity
  have hαu : u * u ≤ α := by
    refine le_trans ?_ hα1
    have h1 : u * u ≤ p * p := mul_le_mul hpu hpu hu0.le hp0.le
    have h2 : p * p * 8 ≤ p ^ 5 := by
      have h3 : (8 : ℝ) ≤ p ^ 3 := by
        have : (1 : ℝ) ≤ p := le_trans (by norm_num) hp1
        have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10 ^ 9) hp1 3
        refine le_trans ?_ h4
        norm_num
      nlinarith only [mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ p * p)]
    have h5 : p * p ≤ p ^ 5 / 8 := by
      rw [le_div_iff₀ (by norm_num)]
      exact h2
    linarith only [h1, h5]
  set η := 1 / p with hη
  have hηinv : 1 / η = p := by rw [hη, one_div_one_div]
  have hη0 : 0 < η := by positivity
  have hηsq : 1 / η ^ 2 = p ^ 2 := by
    rw [hη]
    field_simp
  -- lower bounds for the exponents
  have hη2α : p ^ 3 / 8 ≤ η ^ 2 * α := by
    have h1 : η ^ 2 * (p ^ 5 / 8) ≤ η ^ 2 * α := mul_le_mul_of_nonneg_left hα1 (by positivity)
    refine le_trans (le_of_eq ?_) h1
    rw [hη]
    field_simp
  have hηα : p ^ 4 / 8 ≤ η * α := by
    have h1 : η * (p ^ 5 / 8) ≤ η * α := mul_le_mul_of_nonneg_left hα1 hη0.le
    refine le_trans (le_of_eq ?_) h1
    rw [hη]
    field_simp
  -- the logarithms
  have hlogu : Real.log α ≤ 20 * u := by
    have h1 : Real.log α ≤ Real.log (p ^ 5) := Real.log_le_log hα0 hα2
    have h2 : Real.log (p ^ 5) = 20 * Real.log u := by
      rw [← hQ, Real.log_pow]
      norm_num
    have h3 := Real.log_le_sub_one_of_pos hu0
    linarith only [h1, h2, h3]
  have hlog8 : Real.log 8 ≤ 7 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith only [h]
  have hlog9 : Real.log 9 ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    linarith only [h]
  have hαone : 1 ≤ α := by nlinarith only [hαu, hu1]
  have hlogα0 : 0 ≤ Real.log α := Real.log_nonneg hαone
  -- the slope envelope
  set b := typicalSlopeEnvelope η α with hb
  have hbval : b = 96 * p ^ 2 * Real.log α + (96 * Real.log 8 + 216) * p ^ 2 + 4 := by
    rw [hb]
    unfold typicalSlopeEnvelope
    rw [div_eq_mul_one_div 96, hηsq, div_eq_mul_one_div (96 * Real.log 8 + 216), hηsq]
  have hb0 : 0 ≤ b := typicalSlopeEnvelope_nonneg hαone
  have hpsq0 : 0 < p ^ 2 := by positivity
  have hbup : b ≤ 1921 * (p ^ 2 * u) := by
    rw [hbval]
    have h1 : 96 * p ^ 2 * Real.log α ≤ 96 * p ^ 2 * (20 * u) :=
      mul_le_mul_of_nonneg_left hlogu (by positivity)
    have h2 : (96 * Real.log 8 + 216) * p ^ 2 ≤ 888 * p ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hlog8]) hpsq0.le
    have h3 : 889 * p ^ 2 ≤ p ^ 2 * u := by
      have : (889 : ℝ) ≤ u := le_trans (by norm_num) hu
      nlinarith only [mul_le_mul_of_nonneg_left this hpsq0.le]
    have h4 : (4 : ℝ) ≤ p ^ 2 := by nlinarith only [hp1]
    nlinarith only [h1, h2, h3, h4]
  -- the size of `α` against `p`
  have hp1' : (1 : ℝ) ≤ p := le_trans (by norm_num) hp1
  have hpsq : (10 : ℝ) ^ 18 ≤ p ^ 2 := by nlinarith only [hp1]
  have hαp : 16000 * p ≤ α := by
    have h1 : (128000 : ℝ) ≤ p ^ 4 := le_trans (by norm_num) (hp1.trans (le_self_pow₀ hp1' (by norm_num)))
    have h2 : p ^ 5 = p * p ^ 4 := by ring
    have h3 := mul_le_mul_of_nonneg_left h1 hp0.le
    linarith only [hα1, h2, h3]
  have hα1000 : 1000 ≤ α := by linarith only [hαp, hp1']
  have hp3 : 1000 * p ≤ p ^ 3 := by
    have h1 : (1000 : ℝ) ≤ p ^ 2 := le_trans (by norm_num) hpsq
    have h2 := mul_le_mul_of_nonneg_left h1 hp0.le
    have h3 : p ^ 3 = p * p ^ 2 := by ring
    linarith only [h2, h3]
  have hp4 : 8000 ≤ p ^ 4 := le_trans (le_trans (by norm_num) hp1) (le_self_pow₀ hp1' (by norm_num))
  -- the exponentials
  have hEa : Real.exp (-(24 * η ^ 2 * α)) ≤ 1 / (1000 * p) :=
    exp_neg_le_of_le (by positivity) (by linarith only [hη2α, hp3, pow_pos hp0 3])
  have hEb : Real.exp (-(8 * η ^ 2 * α)) ≤ 1 / (1000 * p) :=
    exp_neg_le_of_le (by positivity) (by linarith only [hη2α, hp3, pow_pos hp0 3])
  have hEc : Real.exp (-(η * α)) ≤ 1 / 1000 :=
    exp_neg_le_of_le (by norm_num) (by linarith only [hηα, hp4])
  have hEd : Real.exp (-α ^ 2 + 5 / 8) ≤ 1 / 1000 := by
    have h1 : -α ^ 2 + 5 / 8 = -(α ^ 2 - 5 / 8) := by ring
    rw [h1]
    exact exp_neg_le_of_le (by norm_num) (by nlinarith only [hα1000])
  have h1p : 1 / (1000 * p) ≤ 1 / 1000 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    linarith only [hp1']
  -- the far envelope
  have hconst : typicalFarConstant η ≤ p := by
    unfold typicalFarConstant
    have he := Real.exp_one_lt_d9
    have h1 : 1 / (16 * η) = p / 16 := by
      rw [hη]
      field_simp
    have h2 : 1 / (8 * η) = p / 8 := by
      rw [hη]
      field_simp
    rw [h1, h2]
    have h3 : 0 ≤ p / 16 + 2 := by positivity
    have h4 : 4 * Real.exp 1 * (p / 16 + 2) ≤ 12 * (p / 16 + 2) :=
      mul_le_mul_of_nonneg_right (by linarith only [he]) h3
    linarith only [h4, hp1]
  have hF : typicalFarEnvelope η α ≤ 1 / 1000 := by
    unfold typicalFarEnvelope
    have h1 : Real.exp (α - α ^ 2) ≤ 1 / (1000 * (p * α)) := by
      have h2 : 1000 * (p * α) ≤ α ^ 2 - α := by
        have h3 := mul_le_mul_of_nonneg_right hαp hα0.le
        have h4 : α ≤ p * α := by nlinarith only [hp1', hα0]
        nlinarith only [h3, h4]
      have h3 := exp_neg_le_of_le (by positivity) h2
      rwa [neg_sub] at h3
    calc typicalFarConstant η * α * Real.exp (α - α ^ 2)
        ≤ p * α * (1 / (1000 * (p * α))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hconst hα0.le) h1 (Real.exp_pos _).le (by positivity)
      _ = 1 / 1000 := by
          field_simp
  -- the ratio of the slope error to the slope
  have hbα : 1000 * b ≤ α := by
    have h1 : 1921 * (p ^ 2 * u) ≤ 1921 * (p ^ 2 * p) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpu hpsq0.le) (by norm_num)
    have h3 : (15368000 : ℝ) ≤ p ^ 2 := le_trans (by norm_num) hpsq
    have h4 := mul_le_mul_of_nonneg_left h3 (pow_pos hp0 3).le
    have h5 : p ^ 3 * p ^ 2 = p ^ 5 := by ring
    have h6 : p ^ 2 * p = p ^ 3 := by ring
    rw [h6] at h1
    linarith only [hbup, h1, h4, h5, hα1]
  have hbαdiv : b / α ≤ 1 / 1000 := by
    rw [div_le_iff₀ hα0]
    linarith only [hbα]
  -- the ratio of the slope error to the Gaussian width: this is where `η ≫ α^{−1/4}` enters
  have hsqrtα : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα0
  have hv : b / Real.sqrt α ≤ 1 / 10000 := by
    rw [div_le_iff₀ hsqrtα]
    have hb2 : (10000 * b) ^ 2 ≤ (10000 * (1921 * (p ^ 2 * u))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hbup]) 2
    have hu18 : (10 : ℝ) ^ 18 ≤ u ^ 2 := by nlinarith only [hu]
    have hp5 : p ^ 4 * u ^ 2 * u ^ 2 = p ^ 5 := by
      rw [hp]
      ring
    have h1 : (10000 * (1921 * (p ^ 2 * u))) ^ 2 = 19210000 ^ 2 * (p ^ 4 * u ^ 2) := by ring
    have h2 : 0 ≤ p ^ 4 * u ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hu18 h2
    have h4 : (10000 * b) ^ 2 ≤ α := by
      rw [h1] at hb2
      refine hb2.trans ?_
      linarith only [hα1, h3, hp5, h2]
    have h5 := (le_abs_self _).trans (Real.abs_le_sqrt h4)
    linarith only [h5]
  have hv0 : 0 ≤ b / Real.sqrt α := by positivity
  -- the model envelope
  have hexp2 : Real.exp 2 ≤ 9 := by
    have h1 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h1]
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith only [h2]) 2
    linarith only [h3]
  have hM : typicalModelEnvelope η α ≤ 1 / 50 := by
    unfold typicalModelEnvelope
    rw [← hb]
    have h1 : (1 + b / Real.sqrt α) ^ 2 ≤ 2 := by nlinarith only [hv, hv0]
    have h2 : Real.exp ((1 + b / Real.sqrt α) ^ 2) ≤ 9 := (Real.exp_le_exp.mpr h1).trans hexp2
    have h3 : 2 * (b / Real.sqrt α) * Real.exp ((1 + b / Real.sqrt α) ^ 2) ≤ 2 * (b / Real.sqrt α) * 9 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith only [h3, hv]
  have hM0 : 0 ≤ typicalModelEnvelope η α := typicalModelEnvelope_nonneg hαone
  have hb2 : (1 / (1000 * p)) * (1 + typicalModelEnvelope η α) ≤ 2 / 1000 := by
    have h1 : 1 + typicalModelEnvelope η α ≤ 2 := by linarith only [hM]
    have h2 := mul_le_mul h1p h1 (by linarith only [hM0]) (by norm_num)
    linarith only [h2]
  -- the tail
  have hTail : typicalTailLogEnvelope η α ≤ η ^ 2 * α := by
    unfold typicalTailLogEnvelope
    have h48 : 48 / η = 48 * p := by rw [div_eq_mul_one_div, hηinv]
    have h108 : 108 / η = 108 * p := by rw [div_eq_mul_one_div, hηinv]
    rw [h48, h108]
    have hl : Real.log (8 * α) ≤ 7 + 20 * u := by
      rw [Real.log_mul (by norm_num) hα0.ne']
      linarith only [hlog8, hlogu]
    have h1 : (4 + 48 * p) * Real.log (8 * α) ≤ (4 + 48 * p) * (7 + 20 * u) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    have h2 : (4 + 48 * p) * (7 + 20 * u) ≤ (49 * p) * (21 * p) := by
      have h3 : 4 + 48 * p ≤ 49 * p := by linarith only [hp1]
      have h4 : 7 + 20 * u ≤ 21 * p := by linarith only [hu, hpu]
      exact mul_le_mul h3 h4 (by positivity) (by positivity)
    have h5 : p ^ 2 * 8240 ≤ p ^ 2 * p := mul_le_mul_of_nonneg_left (le_trans (by norm_num) hp1) hpsq0.le
    have h6 : p ^ 2 * p = p ^ 3 := by ring
    have h7 : p ≤ p ^ 2 := le_self_pow₀ hp1' (by norm_num)
    nlinarith only [h1, h2, h5, h6, h7, hη2α, hlog9, hpsq]
  have hexp24 : Real.exp (-(24 * η ^ 2 * α)) ≤ 1 / 1000 := hEa.trans h1p
  have hEa0 := Real.exp_pos (-(24 * η ^ 2 * α))
  have hEb0 := Real.exp_pos (-(8 * η ^ 2 * α))
  refine ⟨by linarith only [hbα, hα0], hTail, ?_, ?_, ?_⟩
  · unfold typicalMainEnvelope
    linarith only [hexp24, hEd, hM, hF]
  · unfold typicalSlopeNormalizedEnvelope
    rw [← hb]
    have h1 : 3 / (16 * η) = 3 * p / 16 := by
      rw [hη]
      field_simp
    rw [h1]
    have h2 : (2 + 3 * p / 16) * Real.exp (-(24 * η ^ 2 * α)) ≤ p * (1 / (1000 * p)) :=
      mul_le_mul (by linarith only [hp1]) hEa hEa0.le hp0.le
    have h3 : p * (1 / (1000 * p)) = 1 / 1000 := by
      field_simp
    have h4 : (b / α) * (1 + typicalModelEnvelope η α) ≤ (1 / 1000) * 2 :=
      mul_le_mul hbαdiv (by linarith only [hM]) (by linarith only [hM0]) (by norm_num)
    linarith only [h2, h3, h4, hF]
  · unfold typicalOppositeEnvelope
    have h4 : Real.exp (-(8 * η ^ 2 * α)) * (1 + typicalModelEnvelope η α) ≤
        (1 / (1000 * p)) * (1 + typicalModelEnvelope η α) :=
      mul_le_mul_of_nonneg_right hEb (by linarith only [hM0])
    linarith only [h4, hb2, hEc, hF]

/-- **The errors at a power of the logarithm.** With `L = 1 + log 4T = u²⁰`, slope `α ≍ L` and `η = 1/u⁴ = L^{−1/5}`, all errors of the half-Gauss transform are small, for every time with `16η ≤ 2τα ≤ 2`. -/
theorem typical_errors_at_power_of_log {u T τ α : ℝ} (hu : (10 : ℝ) ^ 9 ≤ u) (hT : 8 ≤ T)
    (hL : 1 + Real.log (4 * T) = u ^ 20) (hα1 : u ^ 20 / 8 ≤ α) (hα2 : α ≤ u ^ 20)
    (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8) (hc : 16 * (1 / u ^ 4) ≤ 2 * τ * α) (hc2 : 2 * τ * α ≤ 2) :
    typicalHalfGaussError (1 / u ^ 4) T τ α ≤ 1 / 5 ∧
    typicalHalfGaussSlopeError (1 / u ^ 4) T τ α ≤ α / 100 ∧
    typicalHalfGaussOppositeError (1 / u ^ 4) T τ α ≤ 1 / 2 ∧
    typicalXiSlopeError (1 / u ^ 4) T ≤ 2 / 9 * α := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  obtain ⟨hb, hlog, hM, hS, hO⟩ := typical_envelopes_small hu hα1 hα2
  have hu1 : (1 : ℝ) ≤ u := le_trans (by norm_num) hu
  have hupow : u ≤ u ^ 4 := le_self_pow₀ hu1 (by norm_num)
  have hη : (0 : ℝ) < 1 / u ^ 4 := by positivity
  have hη8 : (1 : ℝ) / u ^ 4 ≤ 1 / 8 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [hu, hupow])
  have hu20 : u ≤ u ^ 20 := le_self_pow₀ hu1 (by norm_num)
  have hα8 : 8 ≤ α := by
    have h1 : (1000 : ℝ) ≤ u := le_trans (by norm_num) hu
    linarith only [hα1, hu20, h1]
  have hscale : 1 + Real.log (4 * T) ≤ 8 * α := by
    rw [hL]
    linarith only [hα1]
  obtain ⟨h1, h2, h3⟩ := typicalHalfGaussErrors_le_envelopes hη hη8 hT hα8 hscale hτ hτ8 hc hc2 hb hlog
  have hα0 : 0 < α := by linarith only [hα8]
  refine ⟨h1.trans hM, h2.trans ?_, h3.trans hO, ?_⟩
  · have := mul_le_mul_of_nonneg_left hS hα0.le
    linarith only [this]
  · exact (typicalXiSlopeError_le_envelope hη hT (by linarith only [hα8]) hscale).trans hb

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
