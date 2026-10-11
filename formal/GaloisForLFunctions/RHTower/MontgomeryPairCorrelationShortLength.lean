import GaloisForLFunctions.RHTower.MontgomeryPairCorrelationLeadingOrder

/-!
# Montgomery's pair form down to length `(log T)³`

**Theorem** (`eventually_montgomeryForm_lower_uniform`). Eventually in `T`, for every `x` with
`(log T)³ ≤ x ≤ T^{1/8}`:

`(π/2) Re F(x, T) ≥ (5/8) (T/4) log x`,

with `F` Montgomery's pair form over all zeros of `ξ` with `0 < γ ≤ T`. No hypothesis on the zeros.

So the unconditional pair-correlation lower bound holds uniformly down to `x = (log T)³`, i.e.
`α = 3 log log T / log T`.

**Proof.** The corpus assembly (`assembly_bound`) with `δ = 1/8`. The four error terms are bounded
explicitly:
* truncation `≪ x (log T)³ ≤ T^{1/8} (log T)³`;
* prime-side diagonal error `312 x² log x`, against `T x log x`;
* remainder energy `96x² + 3T(C + log(T+4))²/x + 1536/x⁴`, against `T x log x`, where `x ≥ (log T)³`
  beats the middle term;
* the prime-number-theorem ratio `Σ d_n² / (x log x) → 1`, applied with `x ≥ (log T)³ → ∞`.
-/

open Filter Topology Set

namespace RHTower

/-- The truncation error is at most `T/1024` once `x ≤ T^{1/8}`. -/
theorem eventually_truncation_le_uniform :
    ∀ᶠ T : ℝ in atTop, 131072 * T ^ (1 / 8 : ℝ) *
      (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) ≤ T / 1024 := by
  set C := xiLineTwoLogDerivConstant with hC
  have hC0 : 0 ≤ C := xiLineTwoLogDerivConstant_nonneg
  set K : ℝ := 131072 * (8 * (C + 2) ^ 2 + 64) with hK
  have hK0 : 0 < K := by positivity
  have hdom := (tendsto_log_pow_div_rpow 3 (s := 7 / 8) (by norm_num)).eventually
    (eventually_le_nhds (show (0 : ℝ) < 1 / (1024 * K) by positivity))
  filter_upwards [hdom, eventually_log_bounds, eventually_gt_atTop (1 : ℝ)] with T hd hb hT1
  obtain ⟨hl1, h2, h3, -⟩ := hb
  have hT0 : 0 < T := by linarith
  set L := Real.log T
  have htr : truncationLog T ≤ (C + 2) * L := by unfold truncationLog; nlinarith
  have htr0 : 0 ≤ truncationLog T := truncationLog_nonneg hT0.le
  have hl3 : 3 * Real.log (1 + T) + 2 ≤ 8 * L := by linarith
  have hbr : truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64 ≤
      (8 * (C + 2) ^ 2 + 64) * L ^ 3 := by
    have hsq : truncationLog T ^ 2 ≤ (C + 2) ^ 2 * L ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ htr0 htr 2
    have hl0 : 0 ≤ 3 * Real.log (1 + T) + 2 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + T by linarith); linarith
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hl1
    calc truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64
        ≤ (C + 2) ^ 2 * L ^ 2 * (8 * L) + 64 := by gcongr
      _ = 8 * (C + 2) ^ 2 * L ^ 3 + 64 := by ring
      _ ≤ 8 * (C + 2) ^ 2 * L ^ 3 + 64 * L ^ 3 := by nlinarith
      _ = (8 * (C + 2) ^ 2 + 64) * L ^ 3 := by ring
  have hT78 : T ^ (7 / 8 : ℝ) * T ^ (1 / 8 : ℝ) = T := by
    rw [← Real.rpow_add hT0]; norm_num
  have hpos78 : 0 < T ^ (7 / 8 : ℝ) := Real.rpow_pos_of_pos hT0 _
  rw [div_le_iff₀ hpos78] at hd
  have hd' : 1024 * K * L ^ 3 ≤ T ^ (7 / 8 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 1024 * K by positivity)
    rw [show 1024 * K * (1 / (1024 * K) * T ^ (7 / 8 : ℝ)) = T ^ (7 / 8 : ℝ) by
      field_simp] at this
    linarith
  have h18 : 0 < T ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hT0 _
  calc 131072 * T ^ (1 / 8 : ℝ) * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64)
      ≤ 131072 * T ^ (1 / 8 : ℝ) * ((8 * (C + 2) ^ 2 + 64) * L ^ 3) := by gcongr
    _ = (K * L ^ 3) * T ^ (1 / 8 : ℝ) := by rw [hK]; ring
    _ ≤ (T ^ (7 / 8 : ℝ) / 1024) * T ^ (1 / 8 : ℝ) := by gcongr; linarith
    _ = T / 1024 := by rw [div_mul_eq_mul_div, hT78]

/-- The remainder energy against `T x log x` once `x ≥ (log T)³`. -/
theorem nine_mul_le_of_remainder_bound {T x D E : ℝ} (hT : 0 < T) (hx : 1 ≤ x)
    (hlogx : 1 ≤ Real.log x) (hxT : 165888 * x ≤ T) (hTbig : 2654208 ≤ T) (hD : 5184 * D ≤ x ^ 2)
    (hE : E ≤ 96 * x ^ 2 + 3 * T * D / x + 1536 / x ^ 4) :
    9 * E ≤ 1 / 64 * (T * x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hA : 9 * (96 * x ^ 2) ≤ T * x / 192 := by
    have h2 : (165888 * x) * x ≤ T * x := mul_le_mul_of_nonneg_right hxT hx0.le
    have e : 9 * (96 * x ^ 2) * 192 = (165888 * x) * x := by ring
    linarith
  have hB : 9 * (3 * T * D / x) ≤ T * x / 192 := by
    rw [show 9 * (3 * T * D / x) = 27 * T * D / x by ring, div_le_div_iff₀ hx0 (by norm_num)]
    have h3 := mul_le_mul_of_nonneg_left hD hT.le
    have e1 : 27 * T * D * 192 = T * (5184 * D) := by ring
    have e2 : T * x * x = T * x ^ 2 := by ring
    rw [e1, e2]
    exact h3
  have hC : 9 * (1536 / x ^ 4) ≤ T * x / 192 := by
    have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
    have h1 : 1536 / x ^ 4 ≤ 1536 := div_le_self (by norm_num) hx4
    have h2 : T / 192 ≤ T * x / 192 := by
      have : T * 1 ≤ T * x := mul_le_mul_of_nonneg_left hx hT.le
      linarith
    linarith
  have hlog : T * x * 1 ≤ T * x * Real.log x := mul_le_mul_of_nonneg_left hlogx (by positivity)
  have hsum : 9 * E ≤ 9 * (96 * x ^ 2) + 9 * (3 * T * D / x) + 9 * (1536 / x ^ 4) := by
    linarith
  linarith

/-- **Montgomery's pair form, uniformly in `x ∈ [(log T)³, T^{1/8}]`.** -/
theorem eventually_montgomeryForm_lower_uniform :
    ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, Real.log T ^ 3 ≤ x → x ≤ T ^ (1 / 8 : ℝ) →
      5 / 8 * ((T / 4) * Real.log x) ≤
        Real.pi / 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x).re := by
  set B := xbBlockConstant with hBdef
  have hB0 : 0 ≤ B := xbBlockConstant_nonneg
  -- prime-side facts, eventually in `x`
  have E4 := (Metric.tendsto_nhds.mp tendsto_tsum_primeAmp_sq_div) (1 / 64) (by norm_num)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (E4.and eventually_tsum_mul_primeAmp_sq_le)
  have hlog3 : Tendsto (fun T : ℝ => Real.log T ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  -- the remainder's middle term
  have hmid : ∀ᶠ T : ℝ in atTop, 5184 * (B + Real.log (T + 4)) ^ 2 ≤ (Real.log T ^ 3) ^ 2 := by
    have hlim := (tendsto_pow_atTop (n := 4) (by norm_num)).comp Real.tendsto_log_atTop
    filter_upwards [eventually_log_bounds, hlim.eventually_ge_atTop (5184 * (B + 2) ^ 2),
      eventually_gt_atTop (1 : ℝ)] with T hb hT4 hT1
    obtain ⟨hl1, -, -, h4⟩ := hb
    simp only [Function.comp] at hT4
    have hle : B + Real.log (T + 4) ≤ (B + 2) * Real.log T := by nlinarith
    have hge : 0 ≤ B + Real.log (T + 4) := by
      have : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
      linarith
    have hsq : (B + Real.log (T + 4)) ^ 2 ≤ (B + 2) ^ 2 * Real.log T ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hge hle 2
    have hL2 : 0 ≤ Real.log T ^ 2 := sq_nonneg _
    calc 5184 * (B + Real.log (T + 4)) ^ 2 ≤ 5184 * (B + 2) ^ 2 * Real.log T ^ 2 := by
          nlinarith
      _ ≤ Real.log T ^ 4 * Real.log T ^ 2 := by gcongr
      _ = (Real.log T ^ 3) ^ 2 := by ring
  have hsmall : ∀ᶠ T : ℝ in atTop, 165888 * T ^ (1 / 8 : ℝ) ≤ T := by
    have := (tendsto_rpow_div_self (α := 1 / 8) (by norm_num)).eventually
      (eventually_le_nhds (show (0 : ℝ) < 1 / 165888 by norm_num))
    filter_upwards [this, eventually_gt_atTop (0 : ℝ)] with T hT hT0
    rw [div_le_iff₀ hT0] at hT
    linarith
  filter_upwards [hlog3.eventually_ge_atTop (max X₀ 3), hmid, hsmall,
    eventually_truncation_le_uniform, eventually_ge_atTop (2654208 : ℝ)]
    with T hX hm hs htrunc hTbig x hx1 hx2
  have hT0 : 0 < T := by linarith
  have hxX : X₀ ≤ x := le_trans (le_max_left _ _) (hX.trans hx1)
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) (hX.trans hx1)
  have hx1' : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ x by
      linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at this
  obtain ⟨e4, e5⟩ := hX₀ x hxX
  set N : ℝ := (T / 4) * Real.log x with hN
  set Q : ℝ := T * x * Real.log x with hQ
  have hlogx0 : 0 < Real.log x := by linarith
  have hN0 : 0 < N := by positivity
  have hQN : Q = 4 * x * N := by rw [hQ, hN]; ring
  have hδ0 : (0 : ℝ) < 1 / 8 := by norm_num
  -- (1) truncation
  have h1 : |(∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll x t‖ ^ 2)
      - Real.pi / 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x).re|
      ≤ 1 / 8 / 8 * N := by
    have := integral_normSq_lorentzZeroSumAll_sub_montgomeryForm_le (x := x) (T := T) hx1'.le
      hT0.le
    rw [setIntegral_Icc_normSq_lorentzZeroSumAll hT0.le] at this
    refine this.trans ?_
    have hP : 0 ≤ truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + T by linarith)
      positivity
    have hx18 : 131072 * x * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) ≤
        131072 * T ^ (1 / 8 : ℝ) * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) :=
      mul_le_mul_of_nonneg_right (by linarith) hP
    have hNT : T / 1024 ≤ 1 / 8 / 8 * N := by
      have e : 1 / 8 / 8 * N = T / 256 * Real.log x := by rw [hN]; ring
      rw [e]
      have : T / 256 ≤ T / 256 * Real.log x := le_mul_of_one_le_right (by positivity) hlogx
      linarith
    linarith
  -- (2) `IS = J/(4x)`
  have h2 := integral_normSq_lorentzZeroSumAll_eq hx1' T
  -- (3) the `δ`-inequalities
  have h3u := integral_normSq_add_le_delta hx1' hT0.le hδ0
  have h3l := integral_normSq_add_ge_delta hx1' hT0.le hδ0
  -- (4) the prime-side mean square
  have h4 : |(∫ t in (0 : ℝ)..T, ‖primeSide x t‖ ^ 2) - T * ∑' n : ℕ, primeAmp x n ^ 2|
      ≤ 1 / 8 / 8 * Q := by
    refine (integral_normSq_primeSide_sub_le hx1'.le hT0.le).trans ?_
    have hxT : 19968 * x ≤ T := by linarith
    have hxl : 0 ≤ x * Real.log x := by positivity
    calc 104 * ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2 ≤ 104 * (3 * (x ^ 2 * Real.log x)) := by
          linarith
      _ = (312 * x) * (x * Real.log x) := by ring
      _ ≤ (T / 64) * (x * Real.log x) := mul_le_mul_of_nonneg_right (by linarith) hxl
      _ = 1 / 8 / 8 * Q := by rw [hQ]; ring
  -- (5) `|T Σd − Q| ≤ (δ/8) Q`
  have h5 : |T * ∑' n : ℕ, primeAmp x n ^ 2 - Q| ≤ 1 / 8 / 8 * Q := by
    rw [Real.dist_eq] at e4
    have hxl : 0 < x * Real.log x := mul_pos hx0 hlogx0
    have hTxl : 0 < T * (x * Real.log x) := mul_pos hT0 hxl
    have heq : |T * ∑' n : ℕ, primeAmp x n ^ 2 - Q|
        = T * (x * Real.log x) * |(∑' n : ℕ, primeAmp x n ^ 2) / (x * Real.log x) - 1| := by
      rw [← abs_of_pos hTxl, ← abs_mul, hQ]
      congr 1
      field_simp
    rw [heq]
    calc T * (x * Real.log x) * |(∑' n : ℕ, primeAmp x n ^ 2) / (x * Real.log x) - 1|
        ≤ T * (x * Real.log x) * (1 / 64) := mul_le_mul_of_nonneg_left e4.le hTxl.le
      _ = 1 / 8 / 8 * Q := by rw [hQ]; ring
  -- (6) the remainder energy
  have h6 : (1 + 1 / (1 / 8 : ℝ)) * ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x t‖ ^ 2 ≤
      1 / 8 / 8 * Q := by
    have hIE := integral_normSq_montgomeryRemainder_le hx1' hT0.le (x := x) (T := T)
    have hx2' : (Real.log T ^ 3) ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ (pow_nonneg (Real.log_nonneg (by linarith)) 3) hx1 2
    have key := nine_mul_le_of_remainder_bound hT0 hx1'.le hlogx (by linarith) hTbig
      (hm.trans hx2') hIE
    have e9 : (1 + 1 / (1 / 8 : ℝ)) = 9 := by norm_num
    rw [e9, hQ]
    linarith
  obtain ⟨hIPl, hIPu⟩ := assembly_ip_bounds h4 h5
  have hmain := assembly_bound hδ0 le_rfl hN0 hx0 hQN h1 h2 h3u h3l hIPu hIPl h6
  have := (abs_le.mp hmain).1
  linarith

end RHTower
