import GaloisForLFunctions.RHTower.JointAncestryQuasiRHChainExclusion
import GaloisForLFunctions.RHTower.JointAncestryProgressionScales
import GaloisForLFunctions.RHTower.JointAncestrySinglePrimeLevel

/-!
# Chain exclusion needs only a sparse family of prime windows

Under quasi-RH an off-line chain is excluded by the level-one log-weight Bernoulli tests on the
windows `(n, n²]` (`one_add_sSup_le_of_jasWindowPositivity_of_chain`). The window index of the proof
is `n = ⌊γ^{75/θ}⌋`, where `γ` is the height of an isolated peak of the chain and `θ` is a small
exponent. Every `θ` below the admissible maximum `θ₂` works, and the window conditions hold
uniformly for `θ ∈ [θ₂/2, θ₂]` (`eventually_window_conditions_uniform`). So the window can be chosen
after the peak.

**Theorem** (`one_add_sSup_le_of_jasWindowPositivityOn_of_chain`). The chain exclusion holds with
positivity only on a set `W` of window indices that is *chain-rich*: for every `θ₂ ∈ (0, 1]`, every
large `γ` admits `θ ∈ [θ₂/2, θ₂]` with `⌊γ^{75/θ}⌋ ∈ W`.

**Theorem** (`chainRichWindows_doubleExp`). The doubly exponential indices `n = 2^{2^k}` are
chain-rich: for `θ = 75 log γ/(2^k log 2)` the index is exactly `2^{2^k}`, and one `k` puts `θ` in
`[θ₂/2, θ₂)`.

**Capstone** (`riemannHypothesis_iff_quasi_and_doubleExpWindows_and_dyadicScales`). RH holds iff
* quasi-RH holds (`Re ρ ≤ ½ + α` with `α < ½`);
* the level-one log-weight Bernoulli tests are positive on the windows `(2^{2^k}, 2^{2^{k+1}}]`;
* the level-one constant-vector interval tests are positive at the dyadic scales `y = 2^m`.

So under quasi-RH the whole content of route JAS sits in a doubly exponentially sparse family of
prime windows together with one geometric progression of scales. Quasi-RH itself is the
single-prime JAS positivity at some level `σ < ½`
(`riemannHypothesis_iff_singlePrime_and_doubleExpWindows_and_dyadicScales`).
-/

open Complex Filter Real Set
open scoped ComplexConjugate BigOperators Topology

namespace RHTower

noncomputable section

/-! ## Uniform window conditions -/

theorem jqrCut_mono {θ θ' ε ε' CM C x : ℝ} (hθ : 0 ≤ θ) (hθθ' : θ ≤ θ') (hεε' : ε ≤ ε')
    (hCM : 0 ≤ CM) (hC : 0 ≤ C) (hx : 1 ≤ x) :
    jqrCut θ ε CM C x ≤ jqrCut θ' ε' CM C x := by
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hx1 : (1 : ℝ) ≤ x + 1 := by linarith
  have hS : (x + 1) ^ θ ≤ (x + 1) ^ θ' := Real.rpow_le_rpow_of_exponent_le hx1 hθθ'
  have hS0 : 0 ≤ (x + 1) ^ θ := by positivity
  have hM : 0 ≤ jqrMassHi CM x := by unfold jqrMassHi; positivity
  have he : Real.exp (2 * ε * Real.log x) ≤ Real.exp (2 * ε' * Real.log x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hfar : jqrFarExponent θ ε CM x ≤ jqrFarExponent θ' ε' CM x := by
    unfold jqrFarExponent jqrScaleMax
    have h1 : Real.exp (2 * ε * Real.log x) * jqrMassHi CM x + jqrMassHi CM x ≤
        Real.exp (2 * ε' * Real.log x) * jqrMassHi CM x + jqrMassHi CM x := by nlinarith
    have h2 : 0 ≤ Real.exp (2 * ε * Real.log x) * jqrMassHi CM x + jqrMassHi CM x := by positivity
    nlinarith
  have hH : jqrHeight θ x ≤ jqrHeight θ' x :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hH1 : 1 ≤ jqrHeight θ x := one_le_jqrHeight hθ (by linarith)
  have hlog : Real.log (640 * Real.exp 1 * (C + 3) * (jqrHeight θ x + 2) ^ 2) ≤
      Real.log (640 * Real.exp 1 * (C + 3) * (jqrHeight θ' x + 2) ^ 2) := by
    refine Real.log_le_log (by positivity) ?_
    have : (jqrHeight θ x + 2) ^ 2 ≤ (jqrHeight θ' x + 2) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  unfold jqrCut
  linarith

theorem jqrCut_nonneg {θ ε CM C x : ℝ} (hθ : 0 ≤ θ) (hCM : 0 ≤ CM) (hC : 0 ≤ C) (hx : 1 ≤ x) :
    0 ≤ jqrCut θ ε CM C x := by
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hMH : 0 ≤ jqrMassHi CM x := by unfold jqrMassHi; linarith
  have hS : 0 ≤ jqrScaleMax θ x := by unfold jqrScaleMax; exact Real.rpow_nonneg (by linarith) _
  have hfar : 0 ≤ jqrFarExponent θ ε CM x := by
    unfold jqrFarExponent
    have : 0 ≤ Real.exp (2 * ε * Real.log x) * jqrMassHi CM x + jqrMassHi CM x :=
      add_nonneg (mul_nonneg (Real.exp_pos _).le hMH) hMH
    have := mul_nonneg hS this
    linarith
  have hΓ := one_le_jqrHeight hθ (by linarith : (0 : ℝ) ≤ x)
  have hlog : 0 ≤ Real.log (640 * Real.exp 1 * (C + 3) * (jqrHeight θ x + 2) ^ 2) := by
    refine Real.log_nonneg ?_
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h3 : (1 : ℝ) ≤ 640 * Real.exp 1 * (C + 3) := by nlinarith
    have h4 : (1 : ℝ) ≤ (jqrHeight θ x + 2) ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le h3 h4
  unfold jqrCut
  linarith

theorem c4_mono {K p p' Cut Cut' y : ℝ} (hK : 0 ≤ K) (hp : p ≤ p') (hC0 : 0 ≤ Cut)
    (hCC : Cut ≤ Cut') (hy : 1 ≤ y) (h : 2 * K * y ^ p' * (Cut' + 2) ^ 2 ≤ 1) :
    2 * K * y ^ p * (Cut + 2) ^ 2 ≤ 1 := by
  have h1 : y ^ p ≤ y ^ p' := Real.rpow_le_rpow_of_exponent_le hy hp
  have h2 : (Cut + 2) ^ 2 ≤ (Cut' + 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h3 : 0 ≤ y ^ p := Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ (Cut + 2) ^ 2 := by positivity
  calc 2 * K * y ^ p * (Cut + 2) ^ 2 ≤ 2 * K * y ^ p' * (Cut' + 2) ^ 2 := by gcongr
    _ ≤ 1 := h

/-- The cut condition holds at every `x ≥ 3`, uniformly in `θ ∈ [0, 75]`. -/
theorem cut_large_of_three_le {θ ε CM C x : ℝ} (hθ : 0 ≤ θ) (hθ75 : θ ≤ 75) (hCM : 0 ≤ CM)
    (hC : 0 ≤ C) (hx3 : 3 ≤ x) :
    2 * (x ^ 2 + jqrHeight θ x + 10) ≤ Real.exp (jqrCut θ ε CM C x) := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hΓ := one_le_jqrHeight hθ hx0.le
  have hΓx : jqrHeight θ x ≤ x + 1 := by
    rw [jqrHeight]
    calc (x + 1) ^ (θ / 75) ≤ (x + 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x + 1 := Real.rpow_one _
  have hlogt : 0 ≤ Real.log (640 * Real.exp 1 * (C + 3) * (jqrHeight θ x + 2) ^ 2) := by
    refine Real.log_nonneg ?_
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h3 : (1 : ℝ) ≤ 640 * Real.exp 1 * (C + 3) := by nlinarith
    have h4 : (1 : ℝ) ≤ (jqrHeight θ x + 2) ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le h3 h4
  have hfar : 2 * Real.log x ≤ jqrFarExponent θ ε CM x := by
    unfold jqrFarExponent jqrMassHi jqrScaleMax
    have h1 : (1 : ℝ) ≤ (x + 1) ^ θ := Real.one_le_rpow (by linarith) hθ
    have h2 : 0 ≤ Real.exp (2 * ε * Real.log x) * (2 * Real.log x + CM) :=
      mul_nonneg (Real.exp_pos _).le (by positivity)
    nlinarith
  have hcut : 4 * Real.log x ≤ jqrCut θ ε CM C x := by unfold jqrCut; linarith
  have hx4 : Real.exp (4 * Real.log x) = x ^ 4 := by
    rw [show 4 * Real.log x = Real.log (x ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  have hx9 : 9 ≤ x ^ 2 := by nlinarith
  have hx44 : 9 * x ^ 2 ≤ x ^ 4 := by nlinarith
  calc 2 * (x ^ 2 + jqrHeight θ x + 10) ≤ x ^ 4 := by nlinarith
    _ = Real.exp (4 * Real.log x) := hx4.symm
    _ ≤ Real.exp (jqrCut θ ε CM C x) := Real.exp_le_exp.mpr hcut

/-- The scale conditions hold eventually, uniformly in `θ ∈ [θ₁, θ₂]`. -/
theorem eventually_scale_conditions_uniform {θ₁ θ₂ C CM W : ℝ} (hθ₁ : 0 < θ₁)
    (hθ75 : θ₂ ≤ 75 / 2) (hW : 0 ≤ W) :
    ∀ᶠ x : ℝ in atTop, ∀ θ : ℝ, θ₁ ≤ θ → θ ≤ θ₂ →
      32 * Real.pi ≤ jqrScaleMin θ C x * jqrMassLo CM x ∧
      4 * jqrThreshold θ W x ≤ jqrScaleMin θ C x * jqrMassLo CM x ∧
      (230 + 4 * Real.pi * jqrThreshold θ W x) / (jqrScaleMin θ C x * jqrMassLo CM x) ≤
        Real.pi / 8 := by
  set c₁ : ℝ := Real.exp (-(34 * C)) * 5 ^ (-(34 : ℝ)) with hc₁
  have hc₁0 : 0 < c₁ := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  set s : ℝ := θ₁ - 34 * θ₁ / 75 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  set K₂ : ℝ := 58 + 2 * Real.log (144 * W + 1) with hK₂
  have hK₂0 : 0 ≤ K₂ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 144 * W + 1 by linarith); rw [hK₂]; linarith
  filter_upwards [eventually_jqrMassLo_ge CM 1, eventually_le_rpow (32 * Real.pi / c₁) hs0,
    eventually_mul_one_add_log_pow_le 1 hs0 (4 * K₂ / c₁),
    eventually_mul_one_add_log_pow_le 1 hs0 ((230 + 4 * Real.pi * K₂) / (Real.pi / 8 * c₁)),
    eventually_ge_atTop 1] with x hM h1 h2 h3 hx1 θ hθ1 hθ2
  have hθ : 0 < θ := lt_of_lt_of_le hθ₁ hθ1
  have hx0 : 0 < x := by linarith
  rw [pow_one] at h2 h3
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hmin : c₁ * x ^ s ≤ jqrScaleMin θ C x := by
    refine le_trans ?_ (jqrScaleMin_ge hθ.le hx0.le)
    rw [← hc₁]
    refine mul_le_mul_of_nonneg_left ?_ hc₁0.le
    calc x ^ s ≤ x ^ (θ - 34 * θ / 75) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hs]; linarith)
      _ ≤ (x + 1) ^ (θ - 34 * θ / 75) :=
          Real.rpow_le_rpow hx0.le (by linarith) (by linarith)
  have hxs : 0 < x ^ s := Real.rpow_pos_of_pos hx0 s
  have hprod : c₁ * x ^ s ≤ jqrScaleMin θ C x * jqrMassLo CM x := by
    have hmin0 : 0 ≤ jqrScaleMin θ C x := le_trans (by positivity) hmin
    nlinarith
  have hthr := jqrThreshold_le hθ.le (le_trans hθ2 hθ75) hW hx1
  rw [← hK₂] at hthr
  have hcx : 0 < c₁ * x ^ s := mul_pos hc₁0 hxs
  refine ⟨?_, ?_, ?_⟩
  · have : 32 * Real.pi ≤ c₁ * x ^ s := by
      rw [div_le_iff₀ hc₁0] at h1; linarith
    linarith
  · have : 4 * K₂ * (1 + Real.log x) ≤ c₁ * x ^ s := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc₁0] at h2; linarith
    nlinarith
  · rw [div_le_iff₀ (lt_of_lt_of_le hcx hprod)]
    have : (230 + 4 * Real.pi * K₂) * (1 + Real.log x) ≤ Real.pi / 8 * (c₁ * x ^ s) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h3; linarith
    have hthr' : 4 * Real.pi * jqrThreshold θ W x ≤ 4 * Real.pi * (K₂ * (1 + Real.log x)) :=
      mul_le_mul_of_nonneg_left hthr (by positivity)
    have : 230 ≤ 230 * (1 + Real.log x) := by nlinarith
    nlinarith [Real.pi_pos]

/-- **All window conditions hold eventually, uniformly in `θ ∈ [θ₁, θ₂]` with `ε = θ c₀/300`.** -/
theorem eventually_window_conditions_uniform {θ₁ θ₂ c₀ σ₁ K δS : ℝ} (hθ₁ : 0 < θ₁)
    (hθ₁₂ : θ₁ ≤ θ₂) (hθσ : θ₂ ≤ (1 - σ₁) / 20) (hθδ : θ₂ ≤ δS / 16) (hc₀0 : 0 ≤ c₀)
    (hc₀1 : c₀ ≤ 1) (hσ₁0 : 0 ≤ σ₁) (hσ₁ : σ₁ < 1) (hK : 0 ≤ K) (hδS : 0 < δS) :
    ∀ᶠ x : ℝ in atTop, ∀ θ ε : ℝ, θ₁ ≤ θ → θ ≤ θ₂ → ε = θ * c₀ / 300 →
      3 ≤ x ∧ 400 ≤ jqrMassLo mertensPrimeWindowBound x ∧
      Real.exp (-(1 / 8) * Real.log (x + 1)) * jqrMassHi mertensPrimeWindowBound x ≤ 99 ∧
      2 * K * (x + 1 / 2) ^ (σ₁ - 1 + ε) *
        (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant x + 2) ^ 2 ≤ 1 ∧
      2 * (x + 1) ^ θ * (2 * Real.log x) * Real.exp ((ε - 1) * Real.log (x + 1)) ≤ 1 / 2 ∧
      16 * ((x + 1) ^ θ) ^ 2 * (2 * Real.log x) ^ 2 / Real.sqrt x ≤ 1 / 100 ∧
      (x + 1) ^ θ * (Real.exp (-(δS / 2) * Real.log (x + 1)) *
        jqrMassHi mertensPrimeWindowBound x) ≤ 1 / 100 ∧
      (x + 1) ^ θ * (2 * Real.log x) * Real.exp (-(2 * θ) * Real.log (x + 1)) ≤ 1 / 2 ∧
      Real.exp (-δS * Real.log (x + 1)) ≤ 1 / 2 ∧
      (32 * Real.pi ≤ jqrScaleMin θ xiLineTwoLogDerivConstant x *
          jqrMassLo mertensPrimeWindowBound x ∧
        4 * jqrThreshold θ (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) x ≤
          jqrScaleMin θ xiLineTwoLogDerivConstant x * jqrMassLo mertensPrimeWindowBound x ∧
        (230 + 4 * Real.pi *
            jqrThreshold θ (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) x) /
            (jqrScaleMin θ xiLineTwoLogDerivConstant x * jqrMassLo mertensPrimeWindowBound x) ≤
          Real.pi / 8) ∧
      2 * (x ^ 2 + jqrHeight θ x + 10) ≤
        Real.exp (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant x) ∧
      40 / (Real.pi / 8 - 3 / 100) ≤ x ^ (θ / 75) := by
  have hCM := mertensPrimeWindowBound_nonneg
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hW : 0 ≤ ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    tsum_nonneg fun q => norm_nonneg _
  have hθ₂0 : 0 < θ₂ := lt_of_lt_of_le hθ₁ hθ₁₂
  have hθ₂1 : θ₂ ≤ 1 / 20 := by linarith
  filter_upwards [eventually_window_conditions (θ := θ₂) (ε := θ₂ * c₀ / 300) (K := K) hθ₂0 hθσ
      hθδ (by positivity) (by nlinarith) hσ₁0 hσ₁ hK hδS,
    eventually_window_conditions (θ := θ₁) (ε := θ₁ * c₀ / 300) (K := K) hθ₁ (by linarith)
      (by linarith) (by positivity) (by nlinarith) hσ₁0 hσ₁ hK hδS,
    eventually_scale_conditions_uniform (θ₁ := θ₁) (θ₂ := θ₂)
      (C := xiLineTwoLogDerivConstant) (CM := mertensPrimeWindowBound) hθ₁ (by linarith) hW]
    with x h₂ h₁ hsc θ ε hθ1 hθ2 hε
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h₂
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := h₁
  have hθ : 0 < θ := lt_of_lt_of_le hθ₁ hθ1
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hL0 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hεε : ε ≤ θ₂ * c₀ / 300 := by
    rw [hε]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hθ2 hc₀0) (by norm_num)
  have hpow : (x + 1) ^ θ ≤ (x + 1) ^ θ₂ := Real.rpow_le_rpow_of_exponent_le (by linarith) hθ2
  have hpow0 : 0 ≤ (x + 1) ^ θ := by positivity
  have hMH : 0 ≤ jqrMassHi mertensPrimeWindowBound x := by unfold jqrMassHi; positivity
  refine ⟨a1, a2, a3, ?_, ?_, ?_, ?_, ?_, a9, hsc θ hθ1 hθ2,
    cut_large_of_three_le hθ.le (by linarith) hCM hC a1, ?_⟩
  · -- c4: monotone in `θ` and `ε`
    have hcut := jqrCut_mono (CM := mertensPrimeWindowBound) (C := xiLineTwoLogDerivConstant)
      (x := x) hθ.le hθ2 hεε hCM hC hx1
    have hcut00 := jqrCut_nonneg (ε := ε) hθ.le hCM hC hx1 (CM := mertensPrimeWindowBound)
      (C := xiLineTwoLogDerivConstant)
    exact c4_mono hK (by linarith only [hεε]) hcut00 hcut (by linarith only [hx1]) a4
  · -- c5
    have he : Real.exp ((ε - 1) * Real.log (x + 1)) ≤
        Real.exp ((θ₂ * c₀ / 300 - 1) * Real.log (x + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [hεε]) hL0)
    calc 2 * (x + 1) ^ θ * (2 * Real.log x) * Real.exp ((ε - 1) * Real.log (x + 1))
        ≤ 2 * (x + 1) ^ θ₂ * (2 * Real.log x) *
          Real.exp ((θ₂ * c₀ / 300 - 1) * Real.log (x + 1)) := by gcongr
      _ ≤ 1 / 2 := a5
  · -- c6
    calc 16 * ((x + 1) ^ θ) ^ 2 * (2 * Real.log x) ^ 2 / Real.sqrt x
        ≤ 16 * ((x + 1) ^ θ₂) ^ 2 * (2 * Real.log x) ^ 2 / Real.sqrt x := by gcongr
      _ ≤ 1 / 100 := a6
  · -- c7
    calc (x + 1) ^ θ * (Real.exp (-(δS / 2) * Real.log (x + 1)) *
          jqrMassHi mertensPrimeWindowBound x)
        ≤ (x + 1) ^ θ₂ * (Real.exp (-(δS / 2) * Real.log (x + 1)) *
          jqrMassHi mertensPrimeWindowBound x) := by gcongr
      _ ≤ 1 / 100 := a7
  · -- c8: decreasing in `θ`
    have hx10 : 0 < x + 1 := by linarith
    have e1 : ∀ t : ℝ, (x + 1) ^ t * Real.exp (-(2 * t) * Real.log (x + 1)) =
        Real.exp (-t * Real.log (x + 1)) := fun t => by
      rw [Real.rpow_def_of_pos hx10, ← Real.exp_add]; congr 1; ring
    have h1 : (x + 1) ^ θ * (2 * Real.log x) * Real.exp (-(2 * θ) * Real.log (x + 1)) =
        (2 * Real.log x) * Real.exp (-θ * Real.log (x + 1)) := by
      rw [← e1 θ]; ring
    have h2 : (x + 1) ^ θ₁ * (2 * Real.log x) * Real.exp (-(2 * θ₁) * Real.log (x + 1)) =
        (2 * Real.log x) * Real.exp (-θ₁ * Real.log (x + 1)) := by
      rw [← e1 θ₁]; ring
    have h3 : Real.exp (-θ * Real.log (x + 1)) ≤ Real.exp (-θ₁ * Real.log (x + 1)) := by
      have := mul_le_mul_of_nonneg_right hθ1 hL0
      exact Real.exp_le_exp.mpr (by linarith only [this])
    rw [h1]
    rw [h2] at b8
    calc (2 * Real.log x) * Real.exp (-θ * Real.log (x + 1))
        ≤ (2 * Real.log x) * Real.exp (-θ₁ * Real.log (x + 1)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 1 / 2 := b8
  · -- c12: increasing in `θ`
    calc 40 / (Real.pi / 8 - 3 / 100) ≤ x ^ (θ₁ / 75) := b12
      _ ≤ x ^ (θ / 75) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

/-! ## Chain exclusion on a chain-rich set of windows -/

/-- Positivity of the log-weight Bernoulli tests on the windows `(n, n²]` with `n ∈ W`. -/
def JasWindowPositivityOn (σ : ℝ) (W : Set ℕ) : Prop :=
  ∀ n ∈ W, ∀ (ξ : ℂ) (a : Nat.Primes → ℝ), (∀ p ∈ jasPrimeWindow n (n ^ 2), 0 ≤ a p) →
    (∀ p ∈ jasPrimeWindow n (n ^ 2), a p * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p) ≤ 1 / 2) →
    ∀ φ : ℝ, 0 ≤ (∑' q : XiZeroCopy, (∏ p ∈ jasPrimeWindow n (n ^ 2),
      jasLogWeightLocal ξ (q.1 : ℂ) (a p) φ p) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re

/-- A set of window indices is *chain-rich* if, for every `θ₂ ∈ (0, 1]`, every large height `γ`
admits some `θ ∈ [θ₂/2, θ₂]` with `⌊γ^{75/θ}⌋ ∈ W`. -/
def ChainRichWindows (W : Set ℕ) : Prop :=
  ∀ θ₂ : ℝ, 0 < θ₂ → θ₂ ≤ 1 → ∃ G₁ : ℝ, ∀ γ : ℝ, G₁ ≤ γ →
    ∃ θ : ℝ, θ₂ / 2 ≤ θ ∧ θ ≤ θ₂ ∧ ⌊γ ^ (75 / θ)⌋₊ ∈ W

/-- **Chain exclusion from window positivity on a chain-rich set of windows.** -/
theorem one_add_sSup_le_of_jasWindowPositivityOn_of_chain {alpha σ : ℝ} {W : Set ℕ}
    (halpha0 : 0 ≤ alpha) (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha)
    (hW : JasWindowPositivityOn σ W) (hrich : ChainRichWindows W) (hch : JasOffLineChain) :
    1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ σ := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨δS, hδSdef⟩ : ∃ δS, δS = sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨_, rfl⟩
  rw [← hδSdef] at hlt
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  have hle : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δS := fun q => by
    rw [hδSdef]; exact le_csSup hbdd ⟨q, rfl⟩
  obtain ⟨q₁, hq₁⟩ := hch.1
  have hδS0 : 0 < δS := lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hq₁)) (hle q₁)
  have hδSa : δS ≤ alpha := by
    rw [hδSdef]
    exact csSup_le ⟨_, ⟨q₁, rfl⟩⟩ (by
      rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q)
  have hδSh : δS < 1 / 2 := lt_of_le_of_lt hδSa halpha
  -- the frontier and the Perron constant
  obtain ⟨σ₁, hσ₁def⟩ : ∃ σ₁ : ℝ, σ₁ = 3 / 4 + alpha / 2 := ⟨_, rfl⟩
  have hσ₁a : 1 / 2 + alpha < σ₁ := by rw [hσ₁def]; linarith
  have hσ₁1 : σ₁ < 1 := by rw [hσ₁def]; linarith
  have hσ₁0 : 0 ≤ σ₁ := by rw [hσ₁def]; linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = (1 - σ₁) / 4 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; linarith
  obtain ⟨K, hK0, hPer⟩ := exists_norm_jasLogWeightSum_sub_le halpha0 hXi hσ₁a hσ₁1 hη0
  -- the exponents
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = (1 + δS - σ) / 2 := ⟨_, rfl⟩
  have hμ0 : 0 < μ := by rw [hμdef]; linarith
  obtain ⟨θ₂, hθ₂def⟩ : ∃ θ₂ : ℝ, θ₂ = min (min (μ / 2) ((1 - σ₁) / 20)) (δS / 16) := ⟨_, rfl⟩
  have hθ₂0 : 0 < θ₂ := by
    rw [hθ₂def]; exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hθ₂μ : θ₂ ≤ μ / 2 := by rw [hθ₂def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hθ₂σ : θ₂ ≤ (1 - σ₁) / 20 := by
    rw [hθ₂def]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hθ₂δ : θ₂ ≤ δS / 16 := by rw [hθ₂def]; exact min_le_right _ _
  have hθ₂1 : θ₂ ≤ 1 := by linarith
  -- the peak exponent
  obtain ⟨c₀, hc₀0, hc₀1, G₀, hG₀, hpeak⟩ :=
    exists_isolated_rePeak (σ₀ := 1 / 2 + δS / 2) (by linarith) (by linarith)
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = θ₂ / 2 * c₀ / 300 := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁def]; positivity
  have hε₁θ : ε₁ ≤ θ₂ := by
    rw [hε₁def]
    have h1 : θ₂ / 2 * c₀ / 300 ≤ θ₂ / 2 * 1 / 300 := by
      gcongr
    linarith only [h1, hθ₂0]
  have hε₁δ : ε₁ ≤ δS / 16 := le_trans hε₁θ hθ₂δ
  -- the uniform window threshold and the chain-rich windows
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp
    (eventually_window_conditions_uniform (θ₁ := θ₂ / 2) (θ₂ := θ₂) (c₀ := c₀) (K := K)
      (by linarith) (by linarith) hθ₂σ hθ₂δ hc₀0.le hc₀1.le hσ₁0 hσ₁1 hK0.le hδS0)
  obtain ⟨G₁, hG₁⟩ := hrich θ₂ hθ₂0 hθ₂1
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀ : ℝ, X₀ = max X₂ 0 := ⟨_, rfl⟩
  have hX₀0 : 0 ≤ X₀ := hX₀def ▸ le_max_right _ _
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = max G₀ (max 1 (max G₁ ((X₀ + 1) ^ (θ₂ / 75)))) :=
    ⟨_, rfl⟩
  have hGG₀ : G₀ ≤ G := by rw [hGdef]; exact le_max_left _ _
  have hGG₁ : G₁ ≤ G := by
    rw [hGdef]; exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hGX : (X₀ + 1) ^ (θ₂ / 75) ≤ G := by
    rw [hGdef]; exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  -- a chain zero near the supremum and a peak above it
  obtain ⟨_, ⟨q₀, rfl⟩, hq₀⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _)
    (show δS - ε₁ < sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) by
      rw [← hδSdef]; linarith)
  beta_reduce at hq₀
  have hoff : (q₀.1 : ℂ).re ≠ 1 / 2 := by
    intro h; rw [h, sub_self, abs_zero] at hq₀; linarith
  obtain ⟨q₂, hfar, hhigh⟩ := exists_farther_high_of_chain hch q₀ hoff (2 * G)
  obtain ⟨qt, hre, hγG, hiso⟩ := hpeak G hGG₀ q₂ (by linarith) hhigh.le
  -- the height and the window exponent
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = (qt.1 : ℂ).im := ⟨_, rfl⟩
  have hγG' : G ≤ γ := by rw [hγdef]; exact hγG
  obtain ⟨θ, hθlo, hθhi, hWn⟩ := hG₁ γ (le_trans hGG₁ hγG')
  have hθ0 : 0 < θ := by linarith
  have hθμ : θ ≤ μ / 2 := le_trans hθhi hθ₂μ
  have hθσ : θ ≤ (1 - σ₁) / 20 := le_trans hθhi hθ₂σ
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = θ * c₀ / 300 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hεθ : ε ≤ θ := by rw [hεdef]; nlinarith
  have hεc : c₀ * θ = 300 * ε := by rw [hεdef]; ring
  have hε₁ε : ε₁ ≤ ε := by
    rw [hε₁def, hεdef]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hθlo hc₀0.le) (by norm_num)
  -- the target
  obtain ⟨δt, hδtdef⟩ : ∃ δt : ℝ, δt = (qt.1 : ℂ).re - 1 / 2 := ⟨_, rfl⟩
  have hδt1 : δS - ε₁ < δt := by rw [hδtdef]; linarith
  have hδt2 : δt ≤ δS := by
    have := hle qt; rw [hδtdef]; exact le_trans (le_abs_self _) this
  have hγ0 : 0 ≤ γ := by linarith [hG₀, hGG₀, hγG']
  have hqt_gt : 1 / 2 < (qt.1 : ℂ).re := by rw [hδtdef] at hδt1; linarith
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℂ, ξ = 1 - conj (qt.1 : ℂ) := ⟨_, rfl⟩
  have hqt : jasLeftRep (qt.1 : ℂ) = ξ := by
    rw [jasLeftRep, if_neg (by linarith), hξdef]
  have hξre : ξ.re = 1 / 2 - δt := by rw [hξdef, hδtdef]; simp; ring
  have hξim : ξ.im = γ := by rw [hξdef, hγdef]; simp
  have hstrip : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δt + ε := fun q => by
    linarith [hle q]
  have hiso' : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ γ ^ c₀ → |(q.1 : ℂ).re - 1 / 2| ≤ δt := by
    intro q hq
    rw [hγdef] at hq
    have h1 := hiso q hq
    obtain ⟨q', hq're, hq'im⟩ := exists_xiZeroCopy_mirror q
    have h2 := hiso q' (by rw [hq'im]; exact hq)
    rw [hq're] at h2
    rw [abs_le, hδtdef]
    constructor <;> linarith
  -- the window
  have hγX : (X₀ + 1) ^ (θ / 75) ≤ γ := by
    refine le_trans ?_ (le_trans hGX hγG')
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  obtain ⟨hnγ, hγΓ⟩ := window_index_brackets (γ := γ) hθ0 hγ0
  have hnX := le_window_index (θ := θ) (γ := γ) hθ0 hX₀0 hγX
  have hX₂n : X₂ ≤ ((⌊γ ^ (75 / θ)⌋₊ : ℕ) : ℝ) :=
    le_trans (by rw [hX₀def]; exact le_max_left _ _) hnX
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ :=
    hX₂ _ hX₂n θ ε hθlo hθhi hεdef
  have hσt : σ - δt - 1 ≤ -(2 * θ) := by
    have : σ = 1 + δS - 2 * μ := by rw [hμdef]; ring
    rw [this]; linarith
  obtain ⟨τ, φ, hτ0, hadm, hneg⟩ := exists_neg_test_at_target hθ0 hθσ hε0 hεθ hεc hσ₁0 hσ₁1
    hηdef hc₀0.le hK0.le hδS0 hδSh hPer qt hqt hξre (by linarith) hδt2 hξim hstrip hiso'
    hnγ hγΓ c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 hσt
  -- positivity contradicts the negative test
  have hpos := hW _ hWn ξ (fun p => τ * (Real.log p / p))
    (fun p _ => mul_nonneg hτ0 (log_div_nonneg_prime p)) hadm φ
  have : (∑' q : XiZeroCopy,
      jasLogWeightValue ξ ⌊γ ^ (75 / θ)⌋₊ (⌊γ ^ (75 / θ)⌋₊ ^ 2) τ φ (q.1 : ℂ)).re =
      (∑' q : XiZeroCopy, (∏ p ∈ jasPrimeWindow ⌊γ ^ (75 / θ)⌋₊ (⌊γ ^ (75 / θ)⌋₊ ^ 2),
        jasLogWeightLocal ξ (q.1 : ℂ) (τ * (Real.log p / p)) φ p) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := rfl
  linarith only [this, hpos, hneg]

/-! ## Doubly exponential windows -/

/-- The doubly exponential window indices `2^{2^k}`. -/
def doubleExpIndices : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ (2 ^ k)}

/-- **The doubly exponential indices are chain-rich.** For `γ ≥ 2` choose `k` with
`2^k log 2 ∈ (75 log γ/θ₂, 150 log γ/θ₂]` and `θ = 75 log γ/(2^k log 2)`; then
`γ^{75/θ} = 2^{2^k}` exactly. -/
theorem chainRichWindows_doubleExp : ChainRichWindows doubleExpIndices := by
  intro θ₂ hθ₂ hθ₂1
  refine ⟨2, fun γ hγ => ?_⟩
  have hγ0 : 0 < γ := by linarith
  have hlγ : 0 < Real.log γ := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set x : ℝ := 75 * Real.log γ / (θ₂ * Real.log 2) with hxdef
  have hl2γ : Real.log 2 ≤ Real.log γ := Real.log_le_log (by norm_num) hγ
  have hx1 : 1 ≤ x := by
    rw [hxdef, le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx1 one_lt_two
  -- `K = k + 1` puts `2^K` in `(x, 2x]`
  have hK1 : x < (2 : ℝ) ^ (k + 1) := hk2
  have hK2 : (2 : ℝ) ^ (k + 1) ≤ 2 * x := by rw [pow_succ]; linarith
  have h2K : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  refine ⟨75 * Real.log γ / ((2 : ℝ) ^ (k + 1) * Real.log 2), ?_, ?_, ⟨k + 1, ?_⟩⟩
  · rw [le_div_iff₀ (by positivity)]
    have : (2 : ℝ) ^ (k + 1) * (θ₂ * Real.log 2) ≤ 2 * (75 * Real.log γ) := by
      have h := mul_le_mul_of_nonneg_right hK2 (show 0 ≤ θ₂ * Real.log 2 by positivity)
      rw [hxdef, mul_assoc 2, div_mul_cancel₀ _ (by positivity)] at h
      linarith
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_right hK1.le (show 0 ≤ θ₂ * Real.log 2 by positivity)
    rw [hxdef, div_mul_cancel₀ _ (by positivity)] at h
    nlinarith
  · have hexp : γ ^ (75 / (75 * Real.log γ / ((2 : ℝ) ^ (k + 1) * Real.log 2))) =
        ((2 ^ (2 ^ (k + 1)) : ℕ) : ℝ) := by
      rw [Real.rpow_def_of_pos hγ0]
      have h1 : Real.log γ * (75 / (75 * Real.log γ / ((2 : ℝ) ^ (k + 1) * Real.log 2))) =
          (2 : ℝ) ^ (k + 1) * Real.log 2 := by
        field_simp
      have h2 : (2 : ℝ) ^ (k + 1) * Real.log 2 = Real.log ((2 : ℝ) ^ (2 ^ (k + 1))) := by
        rw [Real.log_pow]; push_cast; ring
      rw [h1, h2, Real.exp_log (by positivity)]
      push_cast
      ring
    rw [hexp, Nat.floor_natCast]

/-! ## The sparse capstone -/

/-- Quasi-RH and window positivity on a chain-rich set of windows exclude an off-line chain. -/
theorem not_jasOffLineChain_of_quasi_of_jasWindowPositivityOn {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha) {W : Set ℕ}
    (hW : JasWindowPositivityOn 1 W) (hrich : ChainRichWindows W) : ¬ JasOffLineChain := by
  intro hch
  have h := one_add_sSup_le_of_jasWindowPositivityOn_of_chain halpha0 halpha hXi hW hrich hch
  obtain ⟨q₁, hq₁⟩ := hch.1
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  have h1 := le_csSup hbdd ⟨q₁, rfl⟩
  have h2 : 0 < |(q₁.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hq₁)
  simp only at h1
  linarith

/-- **Sparse JAS capstone.** RH ⟺ quasi-RH ∧ level-one log-weight window positivity on the
doubly exponential windows `(2^{2^k}, 2^{2^{k+1}}]` ∧ level-one constant-vector interval positivity
at the dyadic scales `y = 2^m`. -/
theorem riemannHypothesis_iff_quasi_and_doubleExpWindows_and_dyadicScales :
    RiemannHypothesis ↔
      (∃ alpha : ℝ, 0 ≤ alpha ∧ alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha) ∧
        JasWindowPositivityOn 1 doubleExpIndices ∧
        ∃ X : ℕ, JasProgressionPositive X (Real.log 2) := by
  constructor
  · intro hRH
    obtain ⟨hPSD, hq⟩ := riemannHypothesis_iff_jasDressedPSD_one_and_quasi.mp hRH
    have hWall := jasWindowPositivity_of_jasDressedPSD hPSD
    exact ⟨hq, fun n _ => hWall n (Nat.zero_le n),
      jasProgressionPositive_of_riemannHypothesis hRH _⟩
  · rintro ⟨⟨alpha, h0, h1, hXi⟩, hW, hprog⟩
    exact riemannHypothesis_iff_not_jasOffLineChain_and_jasDyadicScalesPositive.mpr
      ⟨not_jasOffLineChain_of_quasi_of_jasWindowPositivityOn h0 h1 hXi hW
        chainRichWindows_doubleExp, hprog⟩

/-- **Sparse JAS capstone, purely JAS form.** RH ⟺ the single-prime tests on large primes are
positive at some level `σ < ½` ∧ the level-one log-weight window tests are positive on the doubly
exponential windows ∧ the level-one constant-vector interval tests are positive at the dyadic
scales. The single-prime tests supply the half-plane `Re ρ ≤ ½ + max(σ, ¼)`. -/
theorem riemannHypothesis_iff_singlePrime_and_doubleExpWindows_and_dyadicScales :
    RiemannHypothesis ↔
      (∃ (X : ℕ) (σ : ℝ), 0 ≤ σ ∧ σ < 1 / 2 ∧ JasSinglePrimePositiveAbove X σ) ∧
        JasWindowPositivityOn 1 doubleExpIndices ∧
        ∃ X : ℕ, JasProgressionPositive X (Real.log 2) := by
  constructor
  · intro hRH
    obtain ⟨X, hS, -⟩ :=
      riemannHypothesis_iff_exists_jasSinglePrime_and_jasProductPositiveAbove.mp hRH
    obtain ⟨-, hW, hprog⟩ :=
      riemannHypothesis_iff_quasi_and_doubleExpWindows_and_dyadicScales.mp hRH
    obtain ⟨σ, hσ0, hσ, hSσ⟩ := hS
    exact ⟨⟨X, σ, hσ0, hσ, hSσ⟩, hW, hprog⟩
  · rintro ⟨⟨X, σ, hσ0, hσ, hS⟩, hW, hprog⟩
    refine riemannHypothesis_iff_quasi_and_doubleExpWindows_and_dyadicScales.mpr
      ⟨⟨max σ (1 / 4), le_trans hσ0 (le_max_left _ _), max_lt hσ (by norm_num),
        xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove hσ0 hσ hS⟩, hW, hprog⟩

end

end RHTower
