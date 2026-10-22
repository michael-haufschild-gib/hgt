import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeXiStripBound

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

section Dominance

variable {t : ℝ}

theorem xiStripConst_chBeta_le (ht : 0 < t) (ht0 : t ≤ 1 / 1000000000) :
    xiStripConst (chBeta t) ≤ 3000000 / t ^ 16 := by
  have ht1 : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 3 / 4 := by
    have := pow_le_of_le_one ht.le ht1 (by norm_num : (4:ℕ) ≠ 0); linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have := pow_le_of_le_one ht.le ht1 (by norm_num : (2:ℕ) ≠ 0); linarith
  have hκ := chKap_ge ht4
  have hκ2 : chKap t ≤ 2 * t ^ 2 := by
    unfold chKap; have := chB_le_one (t := t); nlinarith [pow_pos ht 2]
  have hcos : Real.cos (2 * chBeta t) = chKap t := cos_two_chBeta (by linarith)
  unfold xiStripConst
  rw [hcos]
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_d2
  set γ : ℝ := π * chKap t / 2 with hγ
  have hγt : t ^ 2 ≤ γ := by rw [hγ]; nlinarith [pow_pos ht 2]
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγt
  have hγ1 : γ ≤ 1 := by
    rw [hγ]
    have : t ^ 2 ≤ (1 / 1000000000) ^ 2 := pow_le_pow_left₀ ht.le ht0 2
    nlinarith
  have hS4 := thetaGaussianPowerSum_le hγ0 hγ1 (k := 4) (by norm_num)
  have hS2 := thetaGaussianPowerSum_le hγ0 hγ1 (k := 2) (by norm_num)
  norm_num [Nat.factorial] at hS4 hS2
  have hS4' : thetaGaussianPowerSum γ 4 ≤ 1152 / t ^ 10 := by
    refine le_trans hS4 ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have := pow_le_pow_left₀ (by positivity) hγt 5
    rw [← pow_mul] at this; exact this
  have hS2' : thetaGaussianPowerSum γ 2 ≤ 24 / t ^ 10 := by
    refine le_trans hS2 ?_
    have h1 : 24 / γ ^ 3 ≤ 24 / t ^ 6 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have := pow_le_pow_left₀ (by positivity) hγt 3
      rw [← pow_mul] at this; exact this
    have h2 : 24 / t ^ 6 ≤ 24 / t ^ 10 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact pow_le_pow_of_le_one ht.le ht1 (by norm_num)
    linarith
  have hc : 2 / (π * chKap t) ≤ 2 / t ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith [pow_pos ht 2]
  have hκ0 : 0 < chKap t := lt_of_lt_of_le (by positivity) hκ
  have hc3 : (2 / (π * chKap t)) ^ 3 ≤ 8 / t ^ 6 := by
    calc (2 / (π * chKap t)) ^ 3 ≤ (2 / t ^ 2) ^ 3 :=
          pow_le_pow_left₀ (div_pos two_pos (mul_pos Real.pi_pos hκ0)).le hc 3
      _ = 8 / t ^ 6 := by rw [div_pow]; ring
  have hS4n := thetaGaussianPowerSum_nonneg γ 4
  have hS2n := thetaGaussianPowerSum_nonneg γ 2
  calc 2 * π * (2 * π * thetaGaussianPowerSum γ 4 + 3 * thetaGaussianPowerSum γ 2) *
        (6 * (2 / (π * chKap t)) ^ 3)
      ≤ 2 * π * (2 * π * (1152 / t ^ 10) + 3 * (24 / t ^ 10)) * (6 * (8 / t ^ 6)) := by
        gcongr
    _ = 96 * π * (2304 * π + 72) / t ^ 16 := by field_simp; ring
    _ ≤ 3000000 / t ^ 16 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith

/-- `e^x ≥ x¹⁰/10!` for `x ≥ 0`. -/
theorem pow_ten_div_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 10 / 3628800 ≤ Real.exp x := by
  have h := Real.pow_div_factorial_le_exp x hx 10
  have : ((Nat.factorial 10 : ℕ) : ℝ) = 3628800 := by norm_num [Nat.factorial]
  rwa [this] at h

/-- **Cusp-charge dominance at the saddle frequencies.** -/
theorem cuspCharge_dominance_chU :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t : ℝ, 0 < t → t ≤ t₁ →
      (thetaGroupXi 1 (chU t : ℂ)).re < 0 ∧
        ‖XiC (chU t : ℂ)‖ ≤ 2 ^ 16 * 3000000 * 3628800 * t * ‖thetaGroupXi 1 (chU t : ℂ)‖ := by
  obtain ⟨t₂, ht₂, hpos⟩ := exists_re_chLineInt_pos
  refine ⟨min t₂ (1 / 1000000000), lt_min ht₂ (by norm_num), fun t ht htt => ?_⟩
  have ht0 : t ≤ 1 / 1000000000 := le_trans htt (min_le_right _ _)
  have ht1 : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 3 / 4 := by
    have := pow_le_of_le_one ht.le ht1 (by norm_num : (4:ℕ) ≠ 0); linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have := pow_le_of_le_one ht.le ht1 (by norm_num : (2:ℕ) ≠ 0); linarith
  have hL := hpos t ht (le_trans htt (min_le_left _ _))
  have hG : (2 ^ 8)⁻¹ * Real.exp (chR0 t) ≤ chG0 t := by
    unfold chG0; have := one_le_chP0 ht ht2; have := Real.exp_pos (chR0 t); nlinarith
  have hLpos : 0 < (chLineInt t).re := lt_of_lt_of_le (by
    have := Real.exp_pos (chR0 t); unfold chG0; have := chP0_pos (t := t); positivity) hL
  have hXi := thetaGroupXi_one_chU ht ht2
  set u := chU t with hu
  set β := chBeta t with hβ
  have hβ0 : 0 ≤ β := chBeta_nonneg ht2
  have hβ4 : 2 * β < π / 2 := by have := chBeta_lt ht (by linarith); linarith
  set E : ℝ := Real.exp (-(u * β)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hpref : -((u : ℂ) ^ 2 + 1 / 4) * Complex.exp (-(u * β : ℝ)) =
      ((-((u ^ 2 + 1 / 4) * E) : ℝ) : ℂ) := by
    simp only [hE, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [← mul_assoc, hpref] at hXi
  have hre : (thetaGroupXi 1 (u : ℂ)).re = -((u ^ 2 + 1 / 4) * E) * (chLineInt t).re := by
    rw [hXi, Complex.re_ofReal_mul]
  have hnorm : (u ^ 2 + 1 / 4) * E * (chLineInt t).re ≤ ‖thetaGroupXi 1 (u : ℂ)‖ := by
    have h1 := Complex.abs_re_le_norm (thetaGroupXi 1 (u : ℂ))
    rw [hre] at h1
    have : 0 ≤ (u ^ 2 + 1 / 4) * E * (chLineInt t).re := by positivity
    rw [abs_of_nonpos (by nlinarith)] at h1
    linarith
  refine ⟨?_, ?_⟩
  · rw [hre]
    have : 0 < (u ^ 2 + 1 / 4) * E := by positivity
    nlinarith
  · have hX := norm_XiC_ofReal_le_strip hβ0 hβ4 u
    have hK := xiStripConst_chBeta_le ht ht0
    rw [← hE] at hX
    have hR := chR0_ge ht ht4
    have hR0 : 0 ≤ chR0 t := le_trans (by positivity) hR
    have hRt : 1 ≤ chR0 t * t ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hR; linarith
    have hexp : 1 / 3628800 ≤ t ^ 20 * Real.exp (chR0 t) := by
      have h1 := pow_ten_div_le_exp hR0
      have h2 : 1 ≤ (chR0 t * t ^ 2) ^ 10 := one_le_pow₀ hRt
      have h3 : (chR0 t * t ^ 2) ^ 10 = chR0 t ^ 10 * t ^ 20 := by ring
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ t ^ 20)
      nlinarith
    -- lower bound for `‖Ξ₁‖ / E`
    have hlow : E * (2 ^ 8)⁻¹ * Real.exp (chR0 t) * t ^ 3 / 128 ≤ ‖thetaGroupXi 1 (u : ℂ)‖ := by
      refine le_trans ?_ hnorm
      have hu2 : 1 / 4 ≤ u ^ 2 + 1 / 4 := by nlinarith [sq_nonneg u]
      have hLb : (2 ^ 8)⁻¹ * Real.exp (chR0 t) * t ^ 3 / 32 ≤ (chLineInt t).re :=
        le_trans (by gcongr) hL
      calc E * (2 ^ 8)⁻¹ * Real.exp (chR0 t) * t ^ 3 / 128
          = 1 / 4 * E * ((2 ^ 8)⁻¹ * Real.exp (chR0 t) * t ^ 3 / 32) := by ring
        _ ≤ (u ^ 2 + 1 / 4) * E * (chLineInt t).re := by gcongr
    calc ‖XiC (u : ℂ)‖ ≤ E * (2 * xiStripConst β) := hX
      _ ≤ E * (2 * (3000000 / t ^ 16)) := by gcongr
      _ ≤ 2 ^ 16 * 3000000 * 3628800 * t *
          (E * (2 ^ 8)⁻¹ * Real.exp (chR0 t) * t ^ 3 / 128) := by
          rw [show E * (2 * (3000000 / t ^ 16)) = E * 6000000 / t ^ 16 by ring,
            div_le_iff₀ (by positivity)]
          have e : 2 ^ 16 * 3000000 * 3628800 * t * (E * (2 ^ 8)⁻¹ * Real.exp (chR0 t) * t ^ 3 / 128) *
              t ^ 16 = E * (2 ^ 16 * 3000000 * 3628800 / 2 ^ 8 / 128) * (t ^ 20 * Real.exp (chR0 t)) := by
            ring
          rw [e]
          have : E * 6000000 ≤ E * (2 ^ 16 * 3000000 * 3628800 / 2 ^ 8 / 128) * (1 / 3628800) := by
            norm_num; nlinarith
          calc E * 6000000 ≤ E * (2 ^ 16 * 3000000 * 3628800 / 2 ^ 8 / 128) * (1 / 3628800) := this
            _ ≤ _ := by gcongr
      _ ≤ 2 ^ 16 * 3000000 * 3628800 * t * ‖thetaGroupXi 1 (u : ℂ)‖ := by gcongr

end Dominance

end RHTower
