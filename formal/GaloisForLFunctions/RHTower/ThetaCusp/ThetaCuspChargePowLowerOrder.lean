import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargePowIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeXiStripBound

open Complex MeasureTheory Set
open scoped Real

namespace RHTower

noncomputable section

section LowerOrder

variable {t : ℝ}

theorem chSmall_mono {n n' : ℕ} (hnn : n' ≤ n) (h : chSmall n t) : chSmall n' t := by
  refine ⟨h.1, le_trans ?_ h.2⟩
  apply mul_le_mul_of_nonneg_left _ h.1.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply pow_le_pow_left₀ (by positivity)
  have : (n' : ℝ) ≤ n := by exact_mod_cast hnn
  linarith

theorem exp_neg_inv_sq_le (k : ℕ) (ht : 0 < t) :
    Real.exp (-(1 / t ^ 2)) ≤ (k.factorial : ℝ) * t ^ (2 * k) := by
  have hx : 0 ≤ 1 / t ^ 2 := by positivity
  have h := Real.pow_div_factorial_le_exp (1 / t ^ 2) hx k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  have e : (1 / t ^ 2) ^ k / (k.factorial : ℝ) * ((k.factorial : ℝ) * t ^ (2 * k)) = 1 := by
    rw [div_pow, one_pow, ← pow_mul]; field_simp
  calc (1 : ℝ) = (1 / t ^ 2) ^ k / (k.factorial : ℝ) * ((k.factorial : ℝ) * t ^ (2 * k)) := e.symm
    _ ≤ Real.exp (1 / t ^ 2) * ((k.factorial : ℝ) * t ^ (2 * k)) := by gcongr
    _ = _ := by ring

/-- Uniform bound for the tail of `θ₃hⁿ'⁺¹` on the saddle line. -/
theorem norm_chargeTailPow_le_all (n' : ℕ) (ht : chSmall n' t) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis (n' + 1) τ‖ ≤ M * Real.exp (-π * τ.im)) (s : ℝ) :
    ‖chargeTailC (thetaGroupBasis (n' + 1)) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)‖ ≤
      (2 * chP0 t * Real.exp (chR0m (chM n') t) + chBfarP n' t M) * Real.exp (-|s|) := by
  have ht0 := ht.1
  have htle := ht.le
  have ht1 : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 1 / 6 := by
    have := pow_le_of_le_one ht0.le ht1 (by norm_num : (4:ℕ) ≠ 0); linarith
  have ht44 : t ^ 4 ≤ 3 / 4 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by nlinarith
  have hBf := chBfarP_nonneg n' ht0 ht44 M
  have hp := chP0_pos (t := t)
  have hEpos := Real.exp_pos (chR0m (chM n') t)
  rcases le_or_gt |s| (2 * t ^ 2) with hs | hs
  · have hw := norm_chLineP_le_window ht hs
    have hnorm : ‖chLineP n' t s‖ =
        ‖chargeTailC (thetaGroupBasis (n' + 1)) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)‖ := by
      rw [chLineP_eq_chLineJ, norm_chLineJ]
    rw [← hnorm]
    have hdef' : 0 ≤ chR0m (chM n') t - (chPsim (chM n') t s).re := by
      rw [chR0m_sub_psim_re ht0 (by linarith)]
      have := chB_nonneg (t := t); have := chM_ge n'; positivity
    have he1 : Real.exp ((chPsim (chM n') t s).re - chR0m (chM n') t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hG : chG0p n' t ≤ chP0 t * Real.exp (chR0m (chM n') t) := by
      unfold chG0p
      have : (2 ^ (8 * (n' + 1)) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      have h0 : 0 ≤ chP0 t * Real.exp (chR0m (chM n') t) := by positivity
      calc (2 ^ (8 * (n' + 1)) : ℝ)⁻¹ * chP0 t * Real.exp (chR0m (chM n') t)
          = (2 ^ (8 * (n' + 1)) : ℝ)⁻¹ * (chP0 t * Real.exp (chR0m (chM n') t)) := by ring
        _ ≤ 1 * (chP0 t * Real.exp (chR0m (chM n') t)) := mul_le_mul_of_nonneg_right this h0
        _ = _ := one_mul _
    have hG0 : 0 ≤ chG0p n' t := by unfold chG0p; positivity
    have hes : 3 / 4 ≤ Real.exp (-|s|) := by
      have := Real.add_one_le_exp (-|s|)
      have : |s| ≤ 1 / 4 := by nlinarith
      linarith
    calc ‖chLineP n' t s‖
        ≤ 9 / 8 * (chG0p n' t * Real.exp ((chPsim (chM n') t s).re - chR0m (chM n') t)) := hw
      _ ≤ 9 / 8 * (chP0 t * Real.exp (chR0m (chM n') t) * 1) := by gcongr
      _ ≤ 2 * chP0 t * Real.exp (chR0m (chM n') t) * Real.exp (-|s|) := by
          have h0 : 0 ≤ chP0 t * Real.exp (chR0m (chM n') t) := by positivity
          nlinarith
      _ ≤ (2 * chP0 t * Real.exp (chR0m (chM n') t) + chBfarP n' t M) * Real.exp (-|s|) := by
          nlinarith [Real.exp_pos (-|s|)]
  · have hf := norm_chargeTailPow_far n' ht0 ht4 hM hs.le
    calc _ ≤ chBfarP n' t M * Real.exp (-|s|) := hf
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have : 0 ≤ 2 * chP0 t * Real.exp (chR0m (chM n') t) := by positivity
          linarith

theorem norm_integral_chLineJ_le (n' : ℕ) (ht : chSmall n' t) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis (n' + 1) τ‖ ≤ M * Real.exp (-π * τ.im)) (u : ℝ) :
    ‖∫ s : ℝ, chLineJ (n' + 1) u t s‖ ≤
      2 * (2 * chP0 t * Real.exp (chR0m (chM n') t) + chBfarP n' t M) := by
  set K : ℝ := 2 * chP0 t * Real.exp (chR0m (chM n') t) + chBfarP n' t M
  have hmaj : Integrable (fun s : ℝ => K * Real.exp (-(1 * |s|))) :=
    (integrable_exp_neg_mul_abs' one_pos).const_mul _
  calc ‖∫ s : ℝ, chLineJ (n' + 1) u t s‖ ≤ ∫ s : ℝ, ‖chLineJ (n' + 1) u t s‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ, K * Real.exp (-(1 * |s|)) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => norm_nonneg _) hmaj
        refine Filter.Eventually.of_forall fun s => ?_
        show ‖chLineJ (n' + 1) u t s‖ ≤ K * Real.exp (-(1 * |s|))
        rw [norm_chLineJ, one_mul]
        exact norm_chargeTailPow_le_all n' ht hM s
    _ = 2 * K := by rw [integral_const_mul, integral_exp_neg_mul_abs_eq one_pos]; ring

end LowerOrder

end

end RHTower
