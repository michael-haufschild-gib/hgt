import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeLineIntegral

open Complex MeasureTheory Set
open scoped Real

namespace RHTower

noncomputable section

section Link

variable {t : ℝ}

/-- **The charge transform at the saddle frequency is the shifted-line integral.** -/
theorem thetaGroupXi_one_chU (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) :
    thetaGroupXi 1 (chU t : ℂ) = -((chU t : ℂ) ^ 2 + 1 / 4) *
      (Complex.exp (-(chU t * chBeta t : ℝ)) * chLineInt t) := by
  obtain ⟨M, hM⟩ := exists_thetaGroupBasis_one_cusp
  have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis 1 τ - 0‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; rw [sub_zero]; exact hM τ hτ
  have hF := differentiableOn_thetaGroupBasis 1
  have hβ := chBeta_lt ht (by linarith)
  have hβ0 := chBeta_nonneg ht2
  unfold thetaGroupXi
  rw [modXi_eq_tailTransform hF (thetaGroupBasis_axis 1) hM' (chU t : ℂ)]
  rw [integral_tail_shift hF (fun τ hτ => thetaGroupBasis_S 1 hτ) hM hβ0 hβ (chU t)]
  rfl

end Link

section Absorb

variable {t : ℝ}

theorem chKap_ge (ht4 : t ^ 4 ≤ 3 / 4) : t ^ 2 ≤ chKap t := by
  unfold chKap; have := half_le_chB (t := t) ht4; nlinarith [sq_nonneg t]

theorem chR0_ge (ht : 0 < t) (ht4 : t ^ 4 ≤ 3 / 4) : 1 / t ^ 2 ≤ chR0 t := by
  unfold chR0
  have hb := half_le_chB (t := t) ht4
  have hπ := Real.pi_gt_three
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hπ.le) (le_trans (by norm_num) hb))
    (pow_pos ht 2).le, mul_nonneg (sub_nonneg.mpr hb) (pow_pos ht 2).le, pow_pos ht 2]

theorem one_le_chP0 (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) : 1 ≤ chP0 t := by
  have h := chP0_sq ht
  have hp := chP0_pos (t := t)
  have h1 : 1 ≤ chP0 t ^ 2 := by
    rw [h, le_div_iff₀ (by positivity)]; linarith
  nlinarith

/-- `e^x ≥ x⁶/720` for `x ≥ 0`. -/
theorem pow_six_div_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 6 / 720 ≤ Real.exp x := by
  have h := Real.pow_div_factorial_le_exp x hx 6
  have : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rwa [this] at h

/-- **The far field is exponentially negligible against the saddle.** -/
theorem two_chBfar_le (ht : 0 < t) (ht0 : t ≤ 1 / 1000000000) {M : ℝ} (hM0 : 0 ≤ M)
    (htM : 720 * 8192 * (M + 1) * t ≤ 1) :
    2 * chBfar t M ≤ chG0 t * t ^ 3 / 32 := by
  have ht1 : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 3 / 4 := by
    have := pow_le_of_le_one ht.le ht1 (by norm_num : (4:ℕ) ≠ 0); linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by nlinarith
  have hκ := chKap_ge ht4
  have hκ0 : 0 < chKap t := lt_of_lt_of_le (by positivity) hκ
  have hR := chR0_ge ht ht4
  have hR0 : 0 ≤ chR0 t := le_trans (by positivity) hR
  have hp := one_le_chP0 ht ht2
  have ht2p : 0 < t ^ 2 := by positivity
  -- lower bound for the saddle
  have hG : (2 ^ 8)⁻¹ * Real.exp (chR0 t) ≤ chG0 t := by
    unfold chG0
    have := Real.exp_pos (chR0 t)
    nlinarith
  have hRt : 1 ≤ chR0 t * t ^ 2 := by
    rw [div_le_iff₀ ht2p] at hR; linarith
  -- first branch
  have hX1 : 3 ^ 8 * 2 ^ 7 * (chKap t)⁻¹ ^ 3 * Real.exp (chR0 t / 3) ≤ chG0 t * t ^ 3 / 32 := by
    have hinv : (chKap t)⁻¹ ≤ 1 / t ^ 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le ht2p hκ
    have hA := pow_six_div_le_exp (x := 2 * chR0 t / 3) (by positivity)
    have hsplit : Real.exp (chR0 t) = Real.exp (chR0 t / 3) * Real.exp (2 * chR0 t / 3) := by
      rw [← Real.exp_add]; ring_nf
    have hA2 : (2 / 3) ^ 6 / 720 ≤ t ^ 12 * Real.exp (2 * chR0 t / 3) := by
      have h6 : (2 / 3 : ℝ) ^ 6 ≤ (2 * chR0 t / 3) ^ 6 * t ^ 12 := by
        have : (2 * chR0 t / 3) ^ 6 * t ^ 12 = (2 / 3) ^ 6 * (chR0 t * t ^ 2) ^ 6 := by ring
        rw [this]
        have := one_le_pow₀ hRt (n := 6)
        nlinarith
      nlinarith [pow_pos ht 12]
    have ht3 : t ^ 3 ≤ (1 / 1000000000) ^ 3 := pow_le_pow_left₀ ht.le ht0 3
    have hE3 := Real.exp_pos (chR0 t / 3)
    have hinv3 : (chKap t)⁻¹ ^ 3 ≤ (1 / t ^ 2) ^ 3 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hκ0.le) hinv 3
    calc 3 ^ 8 * 2 ^ 7 * (chKap t)⁻¹ ^ 3 * Real.exp (chR0 t / 3)
        ≤ 3 ^ 8 * 2 ^ 7 * (1 / t ^ 2) ^ 3 * Real.exp (chR0 t / 3) := by gcongr
      _ ≤ (2 ^ 8)⁻¹ * Real.exp (chR0 t) * t ^ 3 / 32 := by
          rw [hsplit]
          have e : (1 / t ^ 2) ^ 3 = 1 / t ^ 6 := by rw [div_pow, one_pow]; ring
          rw [e]
          rw [show (2 ^ 8 : ℝ)⁻¹ * (Real.exp (chR0 t / 3) * Real.exp (2 * chR0 t / 3)) * t ^ 3 / 32
            = Real.exp (chR0 t / 3) * (t ^ 3 * Real.exp (2 * chR0 t / 3) / 8192) by ring]
          rw [show 3 ^ 8 * 2 ^ 7 * (1 / t ^ 6) * Real.exp (chR0 t / 3) =
            Real.exp (chR0 t / 3) * (3 ^ 8 * 2 ^ 7 / t ^ 6) by ring]
          apply mul_le_mul_of_nonneg_left _ hE3.le
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have hmain : (2 / 3) ^ 6 / 720 * 1000000000 ^ 3 ≤ t ^ 12 * Real.exp (2 * chR0 t / 3) / t ^ 3 := by
            rw [le_div_iff₀ (by positivity)]
            calc (2 / 3) ^ 6 / 720 * 1000000000 ^ 3 * t ^ 3
                ≤ (2 / 3) ^ 6 / 720 * 1000000000 ^ 3 * (1 / 1000000000) ^ 3 := by gcongr
              _ = (2 / 3) ^ 6 / 720 := by norm_num
              _ ≤ t ^ 12 * Real.exp (2 * chR0 t / 3) := hA2
          have e2 : t ^ 12 * Real.exp (2 * chR0 t / 3) / t ^ 3 = t ^ 9 * Real.exp (2 * chR0 t / 3) := by
            field_simp
          rw [e2] at hmain
          have : (3 ^ 8 * 2 ^ 7 * 8192 : ℝ) ≤ (2 / 3) ^ 6 / 720 * 1000000000 ^ 3 := by norm_num
          have e3 : t ^ 3 * Real.exp (2 * chR0 t / 3) * t ^ 6 =
              t ^ 9 * Real.exp (2 * chR0 t / 3) := by ring
          linarith
      _ ≤ chG0 t * t ^ 3 / 32 := by gcongr
  -- second branch
  have hX2 : M / 2 * (1 / (π * chKap t)) * 2 ≤ chG0 t * t ^ 3 / 32 := by
    have hπ1 : 1 ≤ π := by linarith [Real.pi_gt_three]
    have h1 : M / 2 * (1 / (π * chKap t)) * 2 ≤ M / t ^ 2 := by
      rw [show M / 2 * (1 / (π * chKap t)) * 2 = M / (π * chKap t) by field_simp]
      apply div_le_div_of_nonneg_left hM0 ht2p
      nlinarith
    have hE := pow_six_div_le_exp hR0
    have hR6 : 1 ≤ (chR0 t * t ^ 2) ^ 6 := one_le_pow₀ hRt
    have ht7 : t ^ 7 ≤ t := pow_le_of_le_one ht.le ht1 (by norm_num)
    have hMt : M * t ^ 7 * (720 * 8192) ≤ 1 := by nlinarith [pow_pos ht 7]
    calc M / 2 * (1 / (π * chKap t)) * 2 ≤ M / t ^ 2 := h1
      _ ≤ (2 ^ 8)⁻¹ * Real.exp (chR0 t) * t ^ 3 / 32 := by
          rw [div_le_iff₀ ht2p]
          have hkey : 8192 * M ≤ t ^ 5 * Real.exp (chR0 t) := by
            have h12 : 1 ≤ chR0 t ^ 6 * t ^ 12 := by
              have : (chR0 t * t ^ 2) ^ 6 = chR0 t ^ 6 * t ^ 12 := by ring
              linarith
            have h720 : 1 ≤ 720 * (t ^ 12 * Real.exp (chR0 t)) := by
              have := mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ) ≤ t ^ 12)
              nlinarith
            have ht7p : 0 < 720 * t ^ 7 := by positivity
            have h2 : 720 * t ^ 7 * (8192 * M) ≤ 720 * t ^ 7 * (t ^ 5 * Real.exp (chR0 t)) := by
              have e1 : 720 * t ^ 7 * (t ^ 5 * Real.exp (chR0 t)) =
                  720 * (t ^ 12 * Real.exp (chR0 t)) := by ring
              rw [e1]; nlinarith
            exact le_of_mul_le_mul_left h2 ht7p
          have e2 : (2 ^ 8 : ℝ)⁻¹ * Real.exp (chR0 t) * t ^ 3 / 32 * t ^ 2 =
              t ^ 5 * Real.exp (chR0 t) / 8192 := by ring
          rw [e2]; linarith
      _ ≤ chG0 t * t ^ 3 / 32 := by gcongr
  unfold chBfar
  rw [mul_comm, max_mul_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  refine max_le ?_ hX2
  linarith

/-- **Positivity of the saddle-line integral.** -/
theorem exists_re_chLineInt_pos :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t : ℝ, 0 < t → t ≤ t₁ → chG0 t * t ^ 3 / 32 ≤ (chLineInt t).re := by
  obtain ⟨M, hM⟩ := exists_thetaGroupBasis_one_cusp
  have hM0 : 0 ≤ M := by
    have h := hM Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  refine ⟨min (1 / 1000000000) (1 / (720 * 8192 * (M + 1))), by positivity, fun t ht htt => ?_⟩
  have ht0 : t ≤ 1 / 1000000000 := le_trans htt (min_le_left _ _)
  have htM : 720 * 8192 * (M + 1) * t ≤ 1 := by
    have := le_trans htt (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have h1 := re_chLineInt_ge ht ht0 hM
  have h2 := two_chBfar_le ht ht0 hM0 htM
  linarith

end Absorb

end

end RHTower
