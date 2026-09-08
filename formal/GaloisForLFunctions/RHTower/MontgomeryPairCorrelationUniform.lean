import GaloisForLFunctions.RHTower.MontgomeryPairCorrelationLeadingOrder

/-!
# Montgomery's pair correlation, uniformly in the scale exponent

The unconditional leading-order asymptotic `F(T^α, T) ~ (T/2π) α log T` holds uniformly for
`α` in every compact subinterval `[a, b]` of `(0, 1)`: all error terms of the assembly are
monotone in `α` or depend on `α` only through `x = T^α ≥ T^a`, so one threshold `T₀(a, b, ε)`
serves every `α ∈ [a, b]`.  This is the analytic input for every scale-averaged use of the pair
form (Montgomery–Vaughan detection over windows in `α`).
-/

open Filter Topology Set

namespace RHTower

/-- The per-scale assembly of the leading-order asymptotic from its five error bounds. -/
theorem montgomeryForm_ratio_lt_of_errors {α T δ ε : ℝ} (hα0 : 0 < α) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 8) (hδε : δ ≤ ε / 8) (hT1 : 1 < T)
    (e1 : 131072 * T ^ α *
        ((xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) ^ 2 * (3 * Real.log (1 + T) + 2) + 64)
        / ((T / 4) * (α * Real.log T)) ≤ δ / 8)
    (e2 : (96 * (T ^ α) ^ 2 + 3 * T * (xbBlockConstant + Real.log (T + 4)) ^ 2 / T ^ α
        + 1536 / (T ^ α) ^ 4) / (T * T ^ α * (α * Real.log T)) ≤ δ ^ 2 / (8 * (1 + δ)))
    (e3 : 312 * (T ^ α / T) ≤ δ / 8)
    (e4 : |(∑' n : ℕ, primeAmp (T ^ α) n ^ 2) / (T ^ α * Real.log (T ^ α)) - 1| < δ / 8)
    (e5 : ∑' n : ℕ, (n : ℝ) * primeAmp (T ^ α) n ^ 2 ≤ 3 * ((T ^ α) ^ 2 * Real.log (T ^ α))) :
    |(montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        / ((T / (2 * Real.pi)) * (α * Real.log T)) - 1| < ε := by
  have hT0 : 0 < T := by linarith
  have hx1 : 1 < T ^ α := Real.one_lt_rpow hT1 hα0
  have hx0 : 0 < T ^ α := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hlogx : Real.log (T ^ α) = α * Real.log T := Real.log_rpow hT0 α
  have hlogx0 : 0 < Real.log (T ^ α) := by rw [hlogx]; positivity
  have hN0 : 0 < (T / 4) * (α * Real.log T) := by positivity
  have hQN : T * T ^ α * Real.log (T ^ α) = 4 * T ^ α * ((T / 4) * (α * Real.log T)) := by
    rw [hlogx]; ring
  have hQ0 : 0 < T * T ^ α * Real.log (T ^ α) := by positivity
  -- (1) truncation
  have h1 : |(∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2)
      - Real.pi / 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re|
      ≤ δ / 8 * ((T / 4) * (α * Real.log T)) := by
    have := integral_normSq_lorentzZeroSumAll_sub_montgomeryForm_le (x := T ^ α) (T := T) hx1.le hT0.le
    rw [setIntegral_Icc_normSq_lorentzZeroSumAll hT0.le] at this
    refine this.trans ?_
    rw [div_le_iff₀ hN0] at e1
    unfold truncationLog
    exact e1
  -- (2) `IS = J/(4x)`
  have h2 := integral_normSq_lorentzZeroSumAll_eq hx1 T
  -- (3) the `δ`-inequalities
  have h3u := integral_normSq_add_le_delta hx1 hT0.le hδ0
  have h3l := integral_normSq_add_ge_delta hx1 hT0.le hδ0
  -- (4) the prime-side mean square
  have h4 : |(∫ t in (0 : ℝ)..T, ‖primeSide (T ^ α) t‖ ^ 2) - T * ∑' n : ℕ, primeAmp (T ^ α) n ^ 2|
      ≤ δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by
    refine (integral_normSq_primeSide_sub_le hx1.le hT0.le).trans ?_
    calc 104 * ∑' n : ℕ, (n : ℝ) * primeAmp (T ^ α) n ^ 2
        ≤ 104 * (3 * ((T ^ α) ^ 2 * Real.log (T ^ α))) := by gcongr
      _ = 312 * (T ^ α / T) * (T * T ^ α * Real.log (T ^ α)) := by field_simp; ring
      _ ≤ δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by gcongr
  -- (5) `|T Σd − Q| ≤ (δ/8) Q`
  have h5 : |T * ∑' n : ℕ, primeAmp (T ^ α) n ^ 2 - T * T ^ α * Real.log (T ^ α)|
      ≤ δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by
    have hxl : 0 < T ^ α * Real.log (T ^ α) := by positivity
    have heq : |T * ∑' n : ℕ, primeAmp (T ^ α) n ^ 2 - T * T ^ α * Real.log (T ^ α)|
        = T * (T ^ α * Real.log (T ^ α)) *
          |(∑' n : ℕ, primeAmp (T ^ α) n ^ 2) / (T ^ α * Real.log (T ^ α)) - 1| := by
      rw [← abs_of_pos (show 0 < T * (T ^ α * Real.log (T ^ α)) by positivity), ← abs_mul]
      congr 1
      field_simp
    rw [heq]
    calc T * (T ^ α * Real.log (T ^ α)) *
          |(∑' n : ℕ, primeAmp (T ^ α) n ^ 2) / (T ^ α * Real.log (T ^ α)) - 1|
        ≤ T * (T ^ α * Real.log (T ^ α)) * (δ / 8) := by gcongr
      _ = δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by ring
  -- (6) the remainder energy
  have h6 : (1 + 1 / δ) * ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder (T ^ α) t‖ ^ 2
      ≤ δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by
    have hIE := integral_normSq_montgomeryRemainder_le hx1 hT0.le (x := T ^ α) (T := T)
    rw [div_le_iff₀ (by positivity), ← hlogx] at e2
    have hIE0 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder (T ^ α) t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT0.le fun t _ => by positivity
    calc (1 + 1 / δ) * ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder (T ^ α) t‖ ^ 2
        ≤ (1 + 1 / δ) * (δ ^ 2 / (8 * (1 + δ)) * (T * T ^ α * Real.log (T ^ α))) := by
          gcongr; exact hIE.trans e2
      _ = δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by field_simp; ring
  -- assemble
  obtain ⟨hIPl, hIPu⟩ := assembly_ip_bounds h4 h5
  have hmain := assembly_bound hδ0 hδ1 hN0 hx0 hQN h1 h2 h3u h3l hIPu hIPl h6
  -- conclude
  have hden : (T / (2 * Real.pi)) * (α * Real.log T) = ((T / 4) * (α * Real.log T)) * (2 / Real.pi) := by
    field_simp; ring
  rw [hden]
  have hπ : 0 < Real.pi := Real.pi_pos
  have hratio : (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        / (((T / 4) * (α * Real.log T)) * (2 / Real.pi)) - 1
      = (Real.pi / 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        - (T / 4) * (α * Real.log T)) / ((T / 4) * (α * Real.log T)) := by
    field_simp
  rw [hratio, abs_div, abs_of_pos hN0, div_lt_iff₀ hN0]
  calc |Real.pi / 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        - (T / 4) * (α * Real.log T)|
      ≤ 3 * δ * ((T / 4) * (α * Real.log T)) := hmain
    _ < ε * ((T / 4) * (α * Real.log T)) := by
        have : 3 * δ < ε := by linarith
        exact mul_lt_mul_of_pos_right this hN0

/-- Uniform truncation error: one threshold for all `α ∈ [a, b]`. -/
theorem eventually_truncation_error_le_uniform {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (C : ℝ) (hC : 0 ≤ C) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ α ∈ Icc a b,
      131072 * T ^ α * ((C + Real.log (2 * T + 5)) ^ 2 * (3 * Real.log (1 + T) + 2) + 64)
        / ((T / 4) * (α * Real.log T)) ≤ η := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hlim := (tendsto_truncation_error_div hb0 hb C hC).eventually
    (eventually_le_nhds (show (0 : ℝ) < a / b * η by positivity))
  filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with T hTb hT1
  intro α hα
  obtain ⟨hαa, hαb⟩ := hα
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT1
  have hα0 : 0 < α := lt_of_lt_of_le ha hαa
  set M : ℝ := (C + Real.log (2 * T + 5)) ^ 2 * (3 * Real.log (1 + T) + 2) + 64 with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
    positivity
  set K : ℝ := 131072 * M * 4 / (T * Real.log T) with hK
  have hK0 : 0 ≤ K := by positivity
  have hform : ∀ γ : ℝ, 0 < γ →
      131072 * T ^ γ * M / ((T / 4) * (γ * Real.log T)) = K * (T ^ γ / γ) := by
    intro γ hγ
    rw [hK]
    field_simp
  rw [hform α hα0]
  rw [hform b hb0] at hTb
  have hpow : T ^ α ≤ T ^ b := Real.rpow_le_rpow_of_exponent_le hT1.le hαb
  have hxα : T ^ α / α ≤ T ^ b / a := by
    have : 0 < T ^ b := Real.rpow_pos_of_pos hT0 b
    calc T ^ α / α ≤ T ^ b / α := by gcongr
      _ ≤ T ^ b / a := by gcongr
  calc K * (T ^ α / α) ≤ K * (T ^ b / a) := by gcongr
    _ = (b / a) * (K * (T ^ b / b)) := by field_simp
    _ ≤ (b / a) * (a / b * η) := by gcongr
    _ = η := by field_simp

/-- Uniform remainder-energy error: one threshold for all `α ∈ [a, b]`. -/
theorem eventually_remainder_energy_le_uniform {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (C : ℝ) (hC : 0 ≤ C) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ α ∈ Icc a b,
      (96 * (T ^ α) ^ 2 + 3 * T * (C + Real.log (T + 4)) ^ 2 / T ^ α
        + 1536 / (T ^ α) ^ 4) / (T * T ^ α * (α * Real.log T)) ≤ η := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  -- the three dominating terms, with the extreme exponents
  have h1 : Tendsto (fun T : ℝ => 96 * (T ^ b / T)) atTop (𝓝 0) := by
    have := (tendsto_rpow_div_self hb).const_mul 96; rwa [mul_zero] at this
  have h2 : Tendsto (fun T : ℝ => (3 * (C + 2) ^ 2 / a) * (Real.log T ^ 2 / T ^ (2 * a)))
      atTop (𝓝 0) := by
    have := (tendsto_log_pow_div_rpow 2 (s := 2 * a) (by linarith)).const_mul (3 * (C + 2) ^ 2 / a)
    rwa [mul_zero] at this
  have h3 : Tendsto (fun T : ℝ => 1536 * T⁻¹) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.const_mul (1536 : ℝ); rwa [mul_zero] at this
  have hsum := (h1.add h2).add h3
  simp only [add_zero] at hsum
  have hsmall := hsum.eventually (eventually_le_nhds hη)
  have halog : ∀ᶠ T : ℝ in atTop, 1 ≤ a * Real.log T :=
    (Real.tendsto_log_atTop.const_mul_atTop ha).eventually_ge_atTop 1
  filter_upwards [hsmall, eventually_log_bounds, eventually_gt_atTop (1 : ℝ), halog]
    with T hsT hlb hT hal
  intro α hα
  obtain ⟨hαa, hαb⟩ := hα
  obtain ⟨hl1, _, _, h4⟩ := hlb
  have hα0 : 0 < α := lt_of_lt_of_le ha hαa
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := by linarith
  have hx : 0 < T ^ α := Real.rpow_pos_of_pos hT0 α
  have hx1 : 1 ≤ T ^ α := Real.one_le_rpow hT.le hα0.le
  have hxa : T ^ a ≤ T ^ α := Real.rpow_le_rpow_of_exponent_le hT.le hαa
  have hxb : T ^ α ≤ T ^ b := Real.rpow_le_rpow_of_exponent_le hT.le hαb
  have hxa0 : 0 < T ^ a := Real.rpow_pos_of_pos hT0 a
  have hαl : 1 ≤ α * Real.log T := by
    calc (1 : ℝ) ≤ a * Real.log T := hal
      _ ≤ α * Real.log T := by gcongr
  have hden : 0 < T * T ^ α * (α * Real.log T) := by positivity
  have hA : 96 * (T ^ α) ^ 2 / (T * T ^ α * (α * Real.log T)) ≤ 96 * (T ^ b / T) := by
    rw [div_le_iff₀ hden]
    have : 96 * (T ^ b / T) * (T * T ^ α * (α * Real.log T))
        = 96 * (T ^ b * T ^ α) * (α * Real.log T) := by field_simp
    rw [this]
    have h1' : (T ^ α) ^ 2 ≤ T ^ b * T ^ α := by nlinarith
    nlinarith
  have hB : 3 * T * (C + Real.log (T + 4)) ^ 2 / T ^ α / (T * T ^ α * (α * Real.log T))
      ≤ (3 * (C + 2) ^ 2 / a) * (Real.log T ^ 2 / T ^ (2 * a)) := by
    have hL : C + Real.log (T + 4) ≤ (C + 2) * Real.log T := by nlinarith
    have hL0 : 0 ≤ C + Real.log (T + 4) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 4); linarith
    have hLsq : (C + Real.log (T + 4)) ^ 2 ≤ (C + 2) ^ 2 * Real.log T ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hL0 hL 2
    have hx2 : T ^ (2 * a) = (T ^ a) ^ 2 := by
      rw [mul_comm, Real.rpow_mul hT0.le]; norm_cast
    have hxa2 : (T ^ a) ^ 2 ≤ (T ^ α) ^ 2 := by gcongr
    rw [hx2, div_div, div_le_iff₀ (by positivity)]
    -- reduce to the comparison with the exponent `α` itself
    have hstep : 3 * (C + 2) ^ 2 / α * (Real.log T ^ 2 / (T ^ α) ^ 2)
        ≤ 3 * (C + 2) ^ 2 / a * (Real.log T ^ 2 / (T ^ a) ^ 2) := by
      gcongr
    calc 3 * T * (C + Real.log (T + 4)) ^ 2
        ≤ 3 * T * ((C + 2) ^ 2 * Real.log T ^ 2) := by gcongr
      _ = 3 * T * ((C + 2) ^ 2 * Real.log T ^ 2) * 1 := (mul_one _).symm
      _ ≤ 3 * T * ((C + 2) ^ 2 * Real.log T ^ 2) * Real.log T := by gcongr
      _ = 3 * (C + 2) ^ 2 / α * (Real.log T ^ 2 / (T ^ α) ^ 2)
          * (T ^ α * (T * T ^ α * (α * Real.log T))) := by field_simp
      _ ≤ 3 * (C + 2) ^ 2 / a * (Real.log T ^ 2 / (T ^ a) ^ 2)
          * (T ^ α * (T * T ^ α * (α * Real.log T))) := by gcongr
  have hCc : 1536 / (T ^ α) ^ 4 / (T * T ^ α * (α * Real.log T)) ≤ 1536 * T⁻¹ := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have hx5 : 1 ≤ (T ^ α) ^ 4 * T ^ α := by
      have : 1 ≤ (T ^ α) ^ 4 := one_le_pow₀ hx1
      nlinarith
    have : 1536 * T⁻¹ * ((T ^ α) ^ 4 * (T * T ^ α * (α * Real.log T)))
        = 1536 * (((T ^ α) ^ 4 * T ^ α) * (α * Real.log T)) := by field_simp
    rw [this]
    nlinarith
  calc (96 * (T ^ α) ^ 2 + 3 * T * (C + Real.log (T + 4)) ^ 2 / T ^ α + 1536 / (T ^ α) ^ 4)
        / (T * T ^ α * (α * Real.log T))
      = 96 * (T ^ α) ^ 2 / (T * T ^ α * (α * Real.log T))
        + 3 * T * (C + Real.log (T + 4)) ^ 2 / T ^ α / (T * T ^ α * (α * Real.log T))
        + 1536 / (T ^ α) ^ 4 / (T * T ^ α * (α * Real.log T)) := by
        rw [add_div, add_div]
    _ ≤ 96 * (T ^ b / T) + (3 * (C + 2) ^ 2 / a) * (Real.log T ^ 2 / T ^ (2 * a)) + 1536 * T⁻¹ :=
        add_le_add (add_le_add hA hB) hCc
    _ ≤ η := hsT

/-- **Montgomery's leading-order asymptotic, uniformly on `[a, b] ⊂ (0, 1)`.** -/
theorem eventually_montgomeryForm_div_leadingOrder_uniform {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ α ∈ Icc a b,
      |(montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        / ((T / (2 * Real.pi)) * (α * Real.log T)) - 1| < ε := by
  obtain ⟨δ, hδ0, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ δ ≤ ε / 8 :=
    ⟨min (ε / 8) (1 / 8), lt_min (by positivity) (by norm_num), min_le_right _ _, min_le_left _ _⟩
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have E1 := eventually_truncation_error_le_uniform ha hab hb xiLineTwoLogDerivConstant
    xiLineTwoLogDerivConstant_nonneg (η := δ / 8) (by positivity)
  have E2 := eventually_remainder_energy_le_uniform ha hab hb xbBlockConstant
    xbBlockConstant_nonneg (η := δ ^ 2 / (8 * (1 + δ))) (by positivity)
  have E3 := (tendsto_prime_error_div hb).eventually
    (eventually_le_nhds (show (0 : ℝ) < δ / 8 by positivity))
  obtain ⟨x₀, hx₀⟩ := Metric.tendsto_atTop.mp tendsto_tsum_primeAmp_sq_div (δ / 8) (by positivity)
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp eventually_tsum_mul_primeAmp_sq_le
  have E4 := (tendsto_rpow_atTop ha).eventually_ge_atTop (max x₀ x₁)
  filter_upwards [E1, E2, E3, E4, eventually_gt_atTop (1 : ℝ)] with T e1 e2 e3 e4 hT1
  intro α hα
  have hα0 : 0 < α := lt_of_lt_of_le ha hα.1
  have hxa : T ^ a ≤ T ^ α := Real.rpow_le_rpow_of_exponent_le hT1.le hα.1
  have hxb : T ^ α ≤ T ^ b := Real.rpow_le_rpow_of_exponent_le hT1.le hα.2
  have hT0 : 0 < T := by linarith
  have e3' : 312 * (T ^ α / T) ≤ δ / 8 := by
    refine le_trans ?_ e3
    gcongr
  have hx0' : x₀ ≤ T ^ α := le_trans (le_max_left _ _) (le_trans e4 hxa)
  have hx1' : x₁ ≤ T ^ α := le_trans (le_max_right _ _) (le_trans e4 hxa)
  have e4' := hx₀ (T ^ α) hx0'
  rw [Real.dist_eq] at e4'
  have e5' := hx₁ (T ^ α) hx1'
  exact montgomeryForm_ratio_lt_of_errors hα0 hδ0 hδ1 hδε hT1 (e1 α hα) (e2 α hα) e3' e4' e5'

end RHTower
