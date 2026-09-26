import GaloisForLFunctions.RHTower.ThetaCuspChargePowSaddle

open Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace RHTower

noncomputable section

open Bottcher

section FarFieldP

variable {t : ℝ}

theorem thetaGroupBasis_succ_eq_farey (n : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaGroupBasis (n + 1) τ =
      thetaTwo τ ^ (4 * (n + 1)) * thetaFour τ ^ (4 * (n + 1)) / thetaThree τ ^ (8 * n + 7) := by
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  unfold thetaGroupBasis thetaGroupHauptmodul
  rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  have e : 8 * (n + 1) = 8 * n + 7 + 1 := by ring
  rw [e, pow_succ]
  field_simp

/-- **Farey bound for `θ₃hⁿ⁺¹` on the saddle ray.** -/
theorem norm_basisPow_line_farey (n : ℕ) (ht : 0 < t) (ht4 : t ^ 4 ≤ 1 / 6) {s : ℝ}
    (hs : 2 * t ^ 2 ≤ |s|) (hin : chKap t ≤ Real.exp (2 * s)) :
    ‖thetaGroupBasis (n + 1) ((Real.exp (2 * s) : ℂ) * chOmega t)‖ ≤
      3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * (chKap t)⁻¹ *
        Real.exp (chR0m (chM n) t / 3) := by
  have ht4' : t ^ 4 ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by nlinarith [pow_pos ht 2]
  have hκ := chKap_pos ht (by linarith)
  have hκ1 := chKap_le_one ht2
  have him : 0 < ((Real.exp (2 * s) : ℂ) * chOmega t).im := by
    rw [im_line_point]; have := chB_nonneg (t := t); positivity
  set τ : ℍ := ⟨(Real.exp (2 * s) : ℂ) * chOmega t, him⟩ with hτ
  have hτc : (τ : ℂ) = (Real.exp (2 * s) : ℂ) * chOmega t := rfl
  have hτim : τ.im = Real.exp (2 * s) * chKap t := by
    show ((τ : ℂ)).im = _; rw [hτc, im_line_point]; rfl
  rw [thetaGroupBasis_succ_eq_farey n him]
  obtain ⟨g, -, hg⟩ := norm_thetaForm_farey_pow n τ
  rw [hτc] at hg
  refine le_trans hg ?_
  have hR : 0 ≤ chR0m (chM n) t := by
    unfold chR0m; have := chB_nonneg (t := t); have := chM_ge n; positivity
  have hden : ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) ≤ (chKap t)⁻¹ := by
    by_cases hc : g 1 0 = 0
    · have hdet := Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      have hd : g 1 1 = 1 ∨ g 1 1 = -1 :=
        Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hdet)
      have hn : ‖slDen g τ‖ = 1 := by
        unfold slDen; rw [hc]; rcases hd with h | h <;> rw [h] <;> simp
      rw [hn, Real.one_rpow]
      rw [le_inv_comm₀ one_pos hκ, inv_one]; exact hκ1
    · have hlow : chKap t * chKap t ≤ ‖slDen g τ‖ := by
        have h1 : |(slDen g τ).im| ≤ ‖slDen g τ‖ := Complex.abs_im_le_norm _
        have h2 : (slDen g τ).im = (g 1 0 : ℝ) * τ.im := by
          unfold slDen; simp
        have h3 : (1 : ℝ) ≤ |(g 1 0 : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
        rw [h2, abs_mul, abs_of_pos τ.im_pos, hτim] at h1
        have h4 : chKap t * chKap t ≤ Real.exp (2 * s) * chKap t :=
          mul_le_mul_of_nonneg_right hin hκ.le
        nlinarith [Real.exp_pos (2 * s)]
      have hpos : 0 < chKap t * chKap t := by positivity
      calc ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) ≤ (chKap t * chKap t) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
        _ = (chKap t)⁻¹ := by
            rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self hκ.le]
  have hexp : (if Odd (g 1 0) ∧ Odd (g 1 1) then
      Real.exp ((8 * n + 7 : ℕ) * Real.pi / 4 * (g • τ).im) else 1)
      ≤ Real.exp (chR0m (chM n) t / 3) := by
    split_ifs with hodd
    · apply Real.exp_le_exp.mpr
      rw [sl_im_smul_eq, hτim]
      have hN := normSq_den_line_ge ht (by linarith) hodd.1 hodd.2 hs
      have hNeq := normSq_den_line ht4' (g 1 0) (g 1 1) s
      have hsl : slDen g τ = ((g 1 0 : ℤ) : ℂ) * ((Real.exp (2 * s) : ℂ) * chOmega t) +
          ((g 1 1 : ℤ) : ℂ) := by unfold slDen; rw [hτc]
      rw [hsl, hNeq]
      have hNpos : 0 < 12 * Real.exp (2 * s) * t ^ 4 := by positivity
      have hq : Real.exp (2 * s) * chKap t /
          ((g 1 0 : ℝ) ^ 2 * Real.exp (2 * s) ^ 2 +
            2 * (g 1 0 : ℝ) * (g 1 1 : ℝ) * Real.exp (2 * s) * (1 - 2 * t ^ 4) + (g 1 1 : ℝ) ^ 2)
          ≤ Real.exp (2 * s) * chKap t / (12 * Real.exp (2 * s) * t ^ 4) :=
        div_le_div_of_nonneg_left (by positivity) hNpos hN
      have hval : Real.exp (2 * s) * chKap t / (12 * Real.exp (2 * s) * t ^ 4) =
          chB t / (6 * t ^ 2) := by
        unfold chKap; field_simp; ring
      rw [hval] at hq
      have h7 : ((8 * n + 7 : ℕ) : ℝ) * Real.pi / 4 * (chB t / (6 * t ^ 2)) = chR0m (chM n) t / 3 := by
        unfold chR0m chM; field_simp; ring
      calc ((8 * n + 7 : ℕ) : ℝ) * Real.pi / 4 * _ ≤
            ((8 * n + 7 : ℕ) : ℝ) * Real.pi / 4 * (chB t / (6 * t ^ 2)) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = chR0m (chM n) t / 3 := h7
    · exact Real.one_le_exp (by linarith)
  calc 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) *
        (if Odd (g 1 0) ∧ Odd (g 1 1) then
          Real.exp ((8 * n + 7 : ℕ) * Real.pi / 4 * (g • τ).im) else 1)
      ≤ 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * (chKap t)⁻¹ *
          Real.exp (chR0m (chM n) t / 3) := by
        gcongr

/-- The far-field constant for `θ₃hⁿ⁺¹`. -/
def chBfarP (n : ℕ) (t M : ℝ) : ℝ :=
  max (3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * (chKap t)⁻¹ ^ 3 *
    Real.exp (chR0m (chM n) t / 3) / 2) (M / 2 * (1 / (π * chKap t)))

theorem chBfarP_nonneg (n : ℕ) (ht : 0 < t) (ht4 : t ^ 4 ≤ 3 / 4) (M : ℝ) : 0 ≤ chBfarP n t M := by
  refine le_trans ?_ (le_max_left _ _)
  have hκ := chKap_pos ht ht4
  have hκ' := inv_nonneg.mpr hκ.le
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hκ' 3))
    (Real.exp_pos _).le) (by norm_num)

/-- **Far field of the tail of `θ₃hⁿ⁺¹` on the saddle line.** -/
theorem norm_chargeTailPow_far (n : ℕ) (ht : 0 < t) (ht4 : t ^ 4 ≤ 1 / 6) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis (n + 1) τ‖ ≤ M * Real.exp (-π * τ.im))
    {s : ℝ} (hs : 2 * t ^ 2 ≤ |s|) :
    ‖chargeTailC (thetaGroupBasis (n + 1)) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)‖ ≤
      chBfarP n t M * Real.exp (-|s|) := by
  have ht2 : t ^ 2 ≤ 1 / 2 := by nlinarith [pow_pos ht 2]
  have ht21 : t ^ 2 ≤ 1 := by linarith
  have hκ := chKap_pos ht (by linarith)
  have hκ1 := chKap_le_one ht2
  have hβ0 := chBeta_nonneg ht2
  have hβ := chBeta_lt ht ht21
  have hcos : Real.cos (2 * chBeta t) = chKap t := cos_two_chBeta ht21
  set z : ℂ := (s : ℂ) - (chBeta t : ℂ) * Complex.I with hz
  have hzre : z.re = s := by simp [hz]
  have hzim : |z.im| ≤ chBeta t := by simp [hz, abs_of_nonneg hβ0]
  have hS : ∀ τ : ℂ, 0 < τ.im → thetaGroupBasis (n + 1) (-1 / τ) =
      (-Complex.I * τ) ^ (1 / 2 : ℂ) * thetaGroupBasis (n + 1) τ :=
    fun τ hτ => thetaGroupBasis_S (n + 1) hτ
  obtain ⟨hA, hB⟩ := norm_chargeTailC_le_cusp hS hM hβ hzim
  rw [hzre, hcos] at hA hB
  have hM0 : 0 ≤ M := by
    have h := hM Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  by_cases h1 : 1 ≤ Real.exp (2 * s) * chKap t
  · have hs0 : 0 ≤ s := by
      by_contra hneg; push Not at hneg
      have : Real.exp (2 * s) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have hkey := exp_half_mul_exp_neg_pi_le hκ hκ1 h1
    rw [abs_of_nonneg hs0]
    calc ‖chargeTailC (thetaGroupBasis (n + 1)) z‖
        ≤ M / 2 * (Real.exp (s / 2) * Real.exp (-π * (Real.exp (2 * s) * chKap t))) := by
          rw [← mul_assoc]; exact hA h1
      _ ≤ M / 2 * (1 / (π * chKap t) * Real.exp (-s)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ chBfarP n t M * Real.exp (-s) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  by_cases h2 : 1 ≤ Real.exp (-2 * s) * chKap t
  · have hs0 : s ≤ 0 := by
      by_contra hneg; push Not at hneg
      have : Real.exp (-2 * s) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have hkey := exp_half_mul_exp_neg_pi_le (x := -s) hκ hκ1
      (by rw [show 2 * -s = -2 * s by ring]; exact h2)
    rw [abs_of_nonpos hs0]
    calc ‖chargeTailC (thetaGroupBasis (n + 1)) z‖
        ≤ M / 2 * (Real.exp (-s / 2) * Real.exp (-π * (Real.exp (-2 * s) * chKap t))) := by
          rw [← mul_assoc]; exact hB h2
      _ = M / 2 * (Real.exp (-s / 2) * Real.exp (-π * (Real.exp (2 * -s) * chKap t))) := by
          ring_nf
      _ ≤ M / 2 * (1 / (π * chKap t) * Real.exp (- -s)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ chBfarP n t M * Real.exp (- -s) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · push Not at h1 h2
    have hin : chKap t ≤ Real.exp (2 * s) := by
      have h3 : Real.exp (-2 * s) * Real.exp (2 * s) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (2 * s), Real.exp_pos (-2 * s)]
    have hF := norm_basisPow_line_farey n ht ht4 hs hin
    have habs : Real.exp (2 * |s|) * chKap t < 1 := by
      rcases abs_cases s with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
      · exact h1
      · rw [show 2 * -s = -2 * s by ring]; exact h2
    have he1 : Real.exp (s / 2) ≤ (chKap t)⁻¹ := by
      rw [le_inv_comm₀ (Real.exp_pos _) hκ]
      have : Real.exp (s / 2) ≤ Real.exp (2 * |s|) :=
        Real.exp_le_exp.mpr (by have := le_abs_self s; have := abs_nonneg s; linarith)
      rw [inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
      nlinarith
    have he2 : 1 ≤ (chKap t)⁻¹ * Real.exp (-|s|) := by
      have : Real.exp |s| ≤ Real.exp (2 * |s|) :=
        Real.exp_le_exp.mpr (by have := abs_nonneg s; linarith)
      have h4 : Real.exp |s| * Real.exp (-|s|) = 1 := by rw [← Real.exp_add]; simp
      rw [← div_eq_inv_mul, le_div_iff₀ hκ]
      nlinarith [Real.exp_pos (-|s|), Real.exp_pos |s|]
    have hval : ‖chargeTailC (thetaGroupBasis (n + 1)) z‖ =
        Real.exp (s / 2) * ‖thetaGroupBasis (n + 1) ((Real.exp (2 * s) : ℂ) * chOmega t)‖ / 2 := by
      unfold chargeTailC
      rw [hz, I_mul_cexp_line ht21, norm_div, norm_mul, norm_cexp_half, Complex.norm_ofNat]
      simp
    rw [hval]
    have hFnn := norm_nonneg (thetaGroupBasis (n + 1) ((Real.exp (2 * s) : ℂ) * chOmega t))
    calc Real.exp (s / 2) * ‖thetaGroupBasis (n + 1) ((Real.exp (2 * s) : ℂ) * chOmega t)‖ / 2
        ≤ (chKap t)⁻¹ * (3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * (chKap t)⁻¹ *
            Real.exp (chR0m (chM n) t / 3)) / 2 := by
          gcongr
      _ ≤ (chKap t)⁻¹ * (3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * (chKap t)⁻¹ *
            Real.exp (chR0m (chM n) t / 3)) / 2 * ((chKap t)⁻¹ * Real.exp (-|s|)) :=
          le_mul_of_one_le_right (by positivity) he2
      _ = 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * (chKap t)⁻¹ ^ 3 *
            Real.exp (chR0m (chM n) t / 3) / 2 * Real.exp (-|s|) := by ring
      _ ≤ chBfarP n t M * Real.exp (-|s|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end FarFieldP

end

end RHTower
