import GaloisForLFunctions.RHTower.ThetaCuspChargePowWindow

open Complex
open scoped Real

namespace RHTower

noncomputable section

/-! ### The saddle line for the pole order `m = 8n+7` -/

/-- Saddle frequency `u = mπ/(8a²)`. -/
def chUm (m t : ℝ) : ℝ := m * π / (8 * t ^ 4)

/-- Saddle height `R₀ = mπb/(8a)`. -/
def chR0m (m t : ℝ) : ℝ := m * π * chB t / (8 * t ^ 2)

/-- Phase function for pole order `m`. -/
def chPsim (m t s : ℝ) : ℂ := -(m * π * Complex.I * chV t s / 4) - Complex.I * chUm m t * s

section GeometryM

variable {m t : ℝ}

theorem chPsim_re (s : ℝ) : (chPsim m t s).re = m * π / 4 * (chV t s).im := by
  simp [chPsim, Complex.mul_re, Complex.mul_im]; ring

theorem chPsim_im (s : ℝ) : (chPsim m t s).im = -(m * π / 4 * (chV t s).re) - chUm m t * s := by
  simp [chPsim, Complex.mul_re, Complex.mul_im]; ring

theorem chR0m_sub_psim_re (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    chR0m m t - (chPsim m t s).re =
      m * π * chB t * chSigma s ^ 2 / (8 * t ^ 2 * (chSigma s ^ 2 + 4 * t ^ 4)) := by
  rw [chPsim_re, chV_im ht ht4, chR0m]
  have hq : 0 < chSigma s ^ 2 + 4 * t ^ 4 := by positivity
  field_simp
  ring

theorem chPsim_im_add (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    (chPsim m t s).im + m * π / 8 =
      m * π / 8 * (t ^ 4 * (chSigma s * chKappa s - 4 * s) - s * chSigma s ^ 2) /
        (t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4)) := by
  rw [chPsim_im, chV_re ht ht4, chUm, chD_eq]
  have hq : 0 < chSigma s ^ 2 + 4 * t ^ 4 := by positivity
  have hE : 0 < Real.exp (2 * s) := Real.exp_pos _
  have hsk : chSigma s * chKappa s = Real.exp (2 * s) - Real.exp (-(2 * s)) := by
    unfold chSigma chKappa
    have h1 : Real.exp s * Real.exp s = Real.exp (2 * s) := by rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-s) * Real.exp (-s) = Real.exp (-(2 * s)) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination h1 - h2
  have hinv : Real.exp (2 * s) * Real.exp (-(2 * s)) = 1 := by rw [← Real.exp_add]; simp
  have hsig := chSigma_sq_mul s
  rw [hsk]
  field_simp
  linear_combination (4 * t ^ 4 * m / 7 * 7) * hsig + (4 * t ^ 4 * m / 7 * 7) * hinv


theorem chR0m_sub_psim_re_le_inner (ht : 0 < t) (ht1 : t ≤ 1) {n : ℕ} (hm0 : 0 ≤ m)
    (hm : m ≤ 8 * (n + 1)) {s : ℝ} (hs : |s| ≤ t ^ 3 / (4 * (n + 1))) :
    chR0m m t - (chPsim m t s).re ≤ 1 / 2 := by
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  have hn1 : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hs1 : |s| ≤ 1 := by
    have : t ^ 3 ≤ 1 := pow_le_one₀ ht.le ht1
    have : t ^ 3 / (4 * (n + 1)) ≤ t ^ 3 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [pow_pos ht 3]
    linarith
  rw [chR0m_sub_psim_re ht ht4]
  have hb1 := chB_le_one (t := t)
  have hb0 := chB_nonneg (t := t)
  have hσ := abs_chSigma_le hs1
  have hσ2 : chSigma s ^ 2 ≤ 9 * s ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hσ 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  have hs2 : s ^ 2 ≤ t ^ 6 / (16 * (n + 1) ^ 2) := by
    have := pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs] at this
    calc s ^ 2 ≤ (t ^ 3 / (4 * (n + 1))) ^ 2 := this
      _ = t ^ 6 / (16 * (n + 1) ^ 2) := by field_simp; ring
  have ht0 : 0 < t ^ 2 := by positivity
  have hq : 4 * t ^ 4 ≤ chSigma s ^ 2 + 4 * t ^ 4 := by nlinarith [sq_nonneg (chSigma s)]
  rw [div_le_iff₀ (by positivity)]
  have hπ := Real.pi_lt_d2
  have hkey : m * π * 9 * (t ^ 6 / (16 * (n + 1) ^ 2)) ≤ 1 / 2 * (8 * t ^ 2 * (4 * t ^ 4)) := by
    have h1 : m * π * 9 ≤ 8 * (n + 1) * 3.15 * 9 := by
      have := mul_le_mul hm hπ.le Real.pi_pos.le (by positivity); nlinarith
    have h2 : 0 ≤ t ^ 6 / (16 * (n + 1) ^ 2) := by positivity
    calc m * π * 9 * (t ^ 6 / (16 * (n + 1) ^ 2))
        ≤ 8 * (n + 1) * 3.15 * 9 * (t ^ 6 / (16 * (n + 1) ^ 2)) := mul_le_mul_of_nonneg_right h1 h2
      _ = 3.15 * 9 / (2 * (n + 1)) * t ^ 6 := by field_simp; ring
      _ ≤ 3.15 * 9 / 2 * t ^ 6 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ ≤ 1 / 2 * (8 * t ^ 2 * (4 * t ^ 4)) := by nlinarith [pow_pos ht 6]
  calc m * π * chB t * chSigma s ^ 2 ≤ m * π * 1 * (9 * (t ^ 6 / (16 * (n + 1) ^ 2))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by positivity))
          (le_trans hσ2 (by nlinarith)) (sq_nonneg _) (by positivity)
    _ = m * π * 9 * (t ^ 6 / (16 * (n + 1) ^ 2)) := by ring
    _ ≤ 1 / 2 * (8 * t ^ 2 * (4 * t ^ 4)) := hkey
    _ ≤ 1 / 2 * (8 * t ^ 2 * (chSigma s ^ 2 + 4 * t ^ 4)) := by gcongr

theorem chR0m_sub_psim_re_ge_mid (hm : 7 ≤ m) (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 4) {s : ℝ}
    (hs : |s| ≤ 2 * t ^ 2) : s ^ 2 / (4 * t ^ 6) ≤ chR0m m t - (chPsim m t s).re := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have hb := half_le_chB (t := t) (by nlinarith)
  rw [chR0m_sub_psim_re ht ht4]
  have hσ := two_abs_le_abs_chSigma s
  have hσ2 : 4 * s ^ 2 ≤ chSigma s ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hσ 2
    rw [mul_pow, sq_abs, sq_abs] at this; linarith
  have hs2 : s ^ 2 ≤ 4 * t ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs] at this; nlinarith
  have ht2p : 0 < t ^ 2 := by positivity
  have hX : s ^ 2 / (s ^ 2 + t ^ 4) ≤ chSigma s ^ 2 / (chSigma s ^ 2 + 4 * t ^ 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg s, pow_pos ht 4]
  have hY : s ^ 2 / (5 * t ^ 4) ≤ s ^ 2 / (s ^ 2 + t ^ 4) := by
    rcases eq_or_lt_of_le (sq_nonneg s) with h0 | h0
    · rw [← h0]; simp
    · exact div_le_div_of_nonneg_left h0.le (by positivity) (by linarith)
  have hπ := Real.pi_gt_three
  have hmain : m * π * chB t * chSigma s ^ 2 / (8 * t ^ 2 * (chSigma s ^ 2 + 4 * t ^ 4)) =
      m * π * chB t / (8 * t ^ 2) * (chSigma s ^ 2 / (chSigma s ^ 2 + 4 * t ^ 4)) := by
    field_simp
  rw [hmain]
  calc s ^ 2 / (4 * t ^ 6) ≤ m * π * (1 / 2) / (8 * t ^ 2) * (s ^ 2 / (5 * t ^ 4)) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        have h21 : (21:ℝ) ≤ m * π := by
          nlinarith [mul_le_mul hm (le_of_lt hπ) (by norm_num) (by linarith)]
        have hst : 0 ≤ s ^ 2 * t ^ 6 := mul_nonneg (sq_nonneg s) (pow_pos ht 6).le
        have h1 := mul_le_mul_of_nonneg_right h21 hst
        have e1 : s ^ 2 * (8 * t ^ 2 * (5 * t ^ 4)) = 40 * (s ^ 2 * t ^ 6) := by ring
        have e2 : m * π * (1 / 2) * s ^ 2 * (4 * t ^ 6) = 2 * (m * π * (s ^ 2 * t ^ 6)) := by ring
        rw [e1, e2]; nlinarith
    _ ≤ m * π * chB t / (8 * t ^ 2) * (chSigma s ^ 2 / (chSigma s ^ 2 + 4 * t ^ 4)) := by
        apply mul_le_mul _ (le_trans hY hX) (by positivity) (by
          have : 0 ≤ chB t := chB_nonneg; positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : 0 ≤ m * π := by positivity
        nlinarith

theorem abs_chPhim_le (ht : 0 < t) (ht1 : t ≤ 1) {n : ℕ} (hm0 : 0 ≤ m)
    (hm : m ≤ 8 * (n + 1)) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |(chPsim m t s).im + m * π / 8| ≤ 11 * (n + 1) * |s| ^ 3 / t ^ 8 := by
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  rw [chPsim_im_add ht ht4]
  have hsk := abs_chSigma_mul_chKappa_sub_le hs
  have hσ := abs_chSigma_le (s := s) (by linarith)
  have hσ2 : chSigma s ^ 2 ≤ 9 * s ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hσ 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  have ht8 : 0 < t ^ 8 := by positivity
  have hden : 4 * t ^ 8 ≤ t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4) := by
    nlinarith [sq_nonneg (chSigma s), pow_pos ht 4]
  have hnum : |t ^ 4 * (chSigma s * chKappa s - 4 * s) - s * chSigma s ^ 2| ≤ 13 * |s| ^ 3 := by
    calc _ ≤ |t ^ 4 * (chSigma s * chKappa s - 4 * s)| + |s * chSigma s ^ 2| := abs_sub _ _
      _ = t ^ 4 * |chSigma s * chKappa s - 4 * s| + |s| * chSigma s ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 4),
            abs_of_nonneg (sq_nonneg (chSigma s))]
      _ ≤ 1 * (4 * |s| ^ 3) + |s| * (9 * s ^ 2) := by gcongr
      _ = 13 * |s| ^ 3 := by rw [← sq_abs s]; ring
  have hmpi : 0 < m * π / 8 ∨ m = 0 := by
    rcases eq_or_lt_of_le hm0 with h | h
    · exact Or.inr h.symm
    · exact Or.inl (by positivity)
  have hq : 0 < t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4) := by positivity
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ m * π / 8), abs_of_pos hq]
  rw [div_le_div_iff₀ hq ht8]
  have hπ := Real.pi_lt_d2
  have hmπ : m * π / 8 ≤ (n + 1) * 3.15 := by
    have := mul_le_mul hm hπ.le Real.pi_pos.le (by positivity); nlinarith
  have hs3 := pow_nonneg (abs_nonneg s) 3
  calc m * π / 8 * |t ^ 4 * (chSigma s * chKappa s - 4 * s) - s * chSigma s ^ 2| * t ^ 8
      ≤ (n + 1) * 3.15 * (13 * |s| ^ 3) * t ^ 8 := by gcongr
    _ ≤ 11 * (n + 1) * |s| ^ 3 * (4 * t ^ 8) := by
        have : (0:ℝ) ≤ (n + 1) * |s| ^ 3 * t ^ 8 := by positivity
        nlinarith
    _ ≤ 11 * (n + 1) * |s| ^ 3 * (t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4)) := by gcongr

theorem chV_im_ge_window (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 160) {s : ℝ} (hs : |s| ≤ 2 * t ^ 2) :
    1 / (40 * t ^ 2) ≤ (chV t s).im := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have hb := half_le_chB (t := t) (by nlinarith)
  rw [chV_im ht ht4]
  have hσ := abs_chSigma_le (s := s) (by nlinarith)
  have hσ2 : chSigma s ^ 2 ≤ 9 * s ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hσ 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  have hs2 : s ^ 2 ≤ 4 * t ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs] at this; nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos ht 2, pow_pos ht 4]

theorem chV_im_le_window (ht : 0 < t) (ht4 : t ^ 4 ≤ 1) (s : ℝ) :
    (chV t s).im ≤ chB t / (2 * t ^ 2) := by
  rw [chV_im ht ht4]
  have := chB_nonneg (t := t)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (chSigma s), pow_pos ht 2]

end GeometryM

/-! ### Factorization for `θ₃hⁿ⁺¹` -/

/-- The pole order `m = 8n+7` as a real number. -/
def chM (n : ℕ) : ℝ := ((8 * n + 7 : ℕ) : ℝ)

/-- The saddle size for `θ₃hⁿ⁺¹`. -/
def chG0p (n : ℕ) (t : ℝ) : ℝ := (2 ^ (8 * (n + 1)))⁻¹ * chP0 t * Real.exp (chR0m (chM n) t)

/-- The shifted-line integrand for `θ₃hⁿ⁺¹`. -/
def chLineP (n : ℕ) (t s : ℝ) : ℂ :=
  Complex.exp (-Complex.I * chUm (chM n) t * s) *
    chargeTailC (thetaGroupBasis (n + 1)) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)

theorem chM_eq (n : ℕ) : chM n = 8 * n + 7 := by unfold chM; push_cast; ring

theorem chM_ge (n : ℕ) : 7 ≤ chM n := by rw [chM_eq]; have := Nat.cast_nonneg (α := ℝ) n; linarith

theorem chM_le (n : ℕ) : chM n ≤ 8 * (n + 1) := by rw [chM_eq]; linarith

section FactorizationP

variable {t : ℝ}

theorem chLineP_eq (n : ℕ) (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) (s : ℝ) :
    chLineP n t s = (chG0p n t : ℂ) * (Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) : ℂ) *
      (chA t s * Complex.exp (Complex.I * ((chPsim (chM n) t s).im + chM n * π / 8 : ℝ)) *
        (1 + chargeErrPow n (chV t s))) := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have ht21 : t ^ 2 ≤ 1 := by linarith
  have hb : 0 < chB t := lt_of_lt_of_le (by norm_num) (half_le_chB (t := t) (by nlinarith))
  have hv := chV_im_pos ht ht4 hb s
  have hF : thetaGroupBasis (n + 1)
      (Complex.I * Complex.exp (2 * ((s : ℂ) - (chBeta t : ℂ) * Complex.I))) =
      (-1) ^ (n + 1) * chP t s * ((2 : ℂ) ^ (8 * n + 7))⁻¹ *
        Complex.exp (-((8 * n + 7 : ℕ) * π * Complex.I * chV t s / 4)) *
        (1 + chargeErrPow n (chV t s)) := by
    rw [I_mul_cexp_line ht21, ← one_add_neg_one_div_chV ht ht4, thetaGroupBasis_succ_window n hv]
    rfl
  have hz : Complex.exp (((s : ℂ) - (chBeta t : ℂ) * Complex.I) / 2) =
      (Real.exp (s / 2) : ℂ) * Complex.exp (-Complex.I * ((chBeta t / 2 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  have hΨ : Complex.exp (-Complex.I * (chUm (chM n) t : ℂ) * (s : ℂ)) *
      Complex.exp (-((8 * n + 7 : ℕ) * π * Complex.I * chV t s / 4)) =
      (Real.exp (chPsim (chM n) t s).re : ℂ) *
        Complex.exp (Complex.I * ((chPsim (chM n) t s).im + chM n * π / 8 : ℝ)) *
        Complex.exp (-Complex.I * ((chM n * π / 8 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    rw [show -Complex.I * (chUm (chM n) t : ℂ) * (s : ℂ) +
        -((8 * n + 7 : ℕ) * π * Complex.I * chV t s / 4) = chPsim (chM n) t s by
      unfold chPsim chM; push_cast; ring]
    conv_lhs => rw [← Complex.re_add_im (chPsim (chM n) t s)]
    rw [Complex.exp_add, ← Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  have key : Complex.exp (-Complex.I * ((chBeta t / 2 : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * ((chM n * π / 8 : ℝ) : ℂ)) =
      (-1) ^ (n + 1) * Complex.exp (Complex.I * ((chTheta t / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    rw [show -Complex.I * ((chBeta t / 2 : ℝ) : ℂ) + -Complex.I * ((chM n * π / 8 : ℝ) : ℂ) =
      Complex.I * ((chTheta t / 2 : ℝ) : ℂ) + ((n + 1 : ℕ) : ℂ) * (-(π * Complex.I)) by
      unfold chBeta; rw [chM_eq]; push_cast; ring]
    rw [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp; ring
  have hp : ((chP0 t : ℝ) : ℂ) * ((chP0 t : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr chP0_pos.ne')
  have hE : (Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) : ℂ) *
      (Real.exp (chR0m (chM n) t) : ℂ) = (Real.exp (chPsim (chM n) t s).re : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  have hsgn : ((-1 : ℂ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have h2 : ((2 : ℂ) ^ (8 * n + 7))⁻¹ / 2 = ((2 : ℂ) ^ (8 * (n + 1)))⁻¹ := by
    rw [show 8 * (n + 1) = 8 * n + 7 + 1 by ring, pow_succ, mul_inv]; ring
  unfold chLineP chargeTailC
  rw [hF, hz]
  unfold chG0p chA
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat]
  set Es : ℂ := (Real.exp (s / 2) : ℂ)
  set Cb : ℂ := Complex.exp (-Complex.I * ((chBeta t / 2 : ℝ) : ℂ))
  set C7 : ℂ := Complex.exp (-Complex.I * ((chM n * π / 8 : ℝ) : ℂ))
  set Ct : ℂ := Complex.exp (Complex.I * ((chTheta t / 2 : ℝ) : ℂ))
  set Cp : ℂ := Complex.exp (Complex.I * ((chPsim (chM n) t s).im + chM n * π / 8 : ℝ))
  set EP : ℂ := (Real.exp (chPsim (chM n) t s).re : ℂ)
  set ER : ℂ := (Real.exp (chR0m (chM n) t) : ℂ)
  set Ed : ℂ := (Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) : ℂ)
  set pp : ℂ := ((chP0 t : ℝ) : ℂ)
  set X : ℂ := Complex.exp (-Complex.I * (chUm (chM n) t : ℂ) * (s : ℂ))
  set Y : ℂ := Complex.exp (-((8 * n + 7 : ℕ) * π * Complex.I * chV t s / 4))
  set P : ℂ := chP t s
  set ε : ℂ := chargeErrPow n (chV t s)
  set c : ℂ := ((2 : ℂ) ^ (8 * (n + 1)))⁻¹
  set sg : ℂ := (-1 : ℂ) ^ (n + 1)
  have h2' : ((2 : ℂ) ^ (8 * n + 7))⁻¹ = 2 * c := by rw [← h2]; ring
  rw [h2']
  linear_combination (sg * c * Es * Cb * P * (1 + ε)) * hΨ +
    (sg * c * Es * P * (1 + ε) * EP * Cp) * key +
    (c * Es * P * (1 + ε) * EP * Cp * Ct) * hsgn +
    (-(c * Es * P * (1 + ε) * Cp * Ct * ER * Ed)) * hp +
    (-(c * Es * P * (1 + ε) * Cp * Ct)) * hE


/-- Smallness of the saddle parameter for pole order `8n+7`. -/
def chSmall (n : ℕ) (t : ℝ) : Prop := 0 < t ∧ t * (10000000000 * ((n : ℝ) + 1) ^ 4) ≤ 1

theorem chSmall.le {n : ℕ} {t : ℝ} (h : chSmall n t) : t ≤ 1 / 10000000000 := by
  obtain ⟨ht, h⟩ := h
  have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 4 := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  rw [le_div_iff₀ (by norm_num)]; nlinarith

theorem chSmall.mul_le {n : ℕ} {t : ℝ} (h : chSmall n t) {K : ℝ} (hK : 0 ≤ K)
    (hK4 : K ≤ 10000000000 * ((n : ℝ) + 1) ^ 4) : t * K ≤ 1 :=
  le_trans (mul_le_mul_of_nonneg_left hK4 h.1.le) h.2

theorem norm_chargeErrPow_window {n : ℕ} (ht : chSmall n t) {s : ℝ} (hs : |s| ≤ 2 * t ^ 2) :
    ‖chargeErrPow n (chV t s)‖ ≤ 1 / 8 := by
  have ht0 := ht.1
  have htle := ht.le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have ht2 : t ^ 2 ≤ 1 / 160 := by nlinarith
  have hv := chV_im_ge_window ht0 ht2 hs
  have ht2p : 0 < t ^ 2 := by positivity
  have hbig : 16000 * ((n : ℝ) + 1) ≤ 1 / t ^ 2 := by
    rw [le_div_iff₀ ht2p]
    have h1 : t * (10000000000 * ((n : ℝ) + 1) ^ 4) ≤ 1 := ht.2
    have h2 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 4 := by
      calc ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ 1 := (pow_one _).symm
        _ ≤ ((n : ℝ) + 1) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
    have h3 : t * (16000 * ((n : ℝ) + 1)) ≤ 1 / 100000 := by
      have := mul_le_mul_of_nonneg_left h2 ht0.le
      nlinarith
    nlinarith
  apply norm_chargeErrPow_le n
  · have : 1 / (40 * t ^ 2) ≥ 2 := by
      rw [ge_iff_le, le_div_iff₀ (by positivity)]; nlinarith
    linarith
  · have hx : (π / 2) * (chV t s).im ≥ 600 * ((n : ℝ) + 1) := by
      have hπ := Real.pi_gt_three
      have : 1 / (40 * t ^ 2) = (1 / t ^ 2) / 40 := by field_simp
      rw [this] at hv
      nlinarith
    have he := Real.add_one_le_exp ((π / 2) * (chV t s).im)
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    linarith

theorem norm_chLineP_le_window {n : ℕ} (ht : chSmall n t) {s : ℝ} (hs : |s| ≤ 2 * t ^ 2) :
    ‖chLineP n t s‖ ≤ 9 / 8 * (chG0p n t * Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t)) := by
  have ht0 := ht.1
  have htle := ht.le
  have ht4 : t ^ 4 ≤ 1 := by nlinarith [pow_le_one₀ ht0.le (by linarith : t ≤ 1) (n := 4)]
  rw [chLineP_eq n ht0 (by nlinarith)]
  have hε := norm_chargeErrPow_window ht hs
  have hA := norm_chA_le_one ht0 ht4 s
  have hG : 0 ≤ chG0p n t := by unfold chG0p; have := chP0_pos (t := t); positivity
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG, abs_of_pos (Real.exp_pos _)]
  have hc : ‖Complex.exp (Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [hc, mul_one]
  have h1 : ‖1 + chargeErrPow n (chV t s)‖ ≤ 9 / 8 := by
    refine le_trans (norm_add_le _ _) ?_; rw [norm_one]; linarith
  have hE := Real.exp_pos ((chPsim (chM n) t s).re - chR0m (chM n) t)
  calc chG0p n t * Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) *
        (‖chA t s‖ * ‖1 + chargeErrPow n (chV t s)‖)
      ≤ chG0p n t * Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) * (1 * (9 / 8)) := by
        gcongr
    _ = _ := by ring

theorem half_le_re_chLineP_core {n : ℕ} (ht : chSmall n t) {s : ℝ}
    (hs : |s| ≤ 144 * ((n : ℝ) + 1) * t ^ 3) :
    chG0p n t * Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) / 2 ≤ (chLineP n t s).re := by
  have ht0 := ht.1
  have htle := ht.le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have ht1 : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1
  have hn4 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 4 := by
    calc ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((n : ℝ) + 1) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
  have htn : t * ((n : ℝ) + 1) ≤ 1 / 10000000000 := by
    have := mul_le_mul_of_nonneg_left hn4 ht0.le; nlinarith [ht.2]
  have hs2 : |s| ≤ 2 * t ^ 2 := by
    have : 144 * ((n : ℝ) + 1) * t ^ 3 ≤ 2 * t ^ 2 := by
      have e : 144 * ((n : ℝ) + 1) * t ^ 3 = 144 * (t * ((n : ℝ) + 1)) * t ^ 2 := by ring
      rw [e]; nlinarith [pow_pos ht0 2]
    linarith
  have hs12 : |s| ≤ 1 / 2 := by nlinarith [pow_pos ht0 2]
  rw [chLineP_eq n ht0 (by nlinarith)]
  set U : ℂ := chA t s * Complex.exp (Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ)) *
    (1 + chargeErrPow n (chV t s)) with hU
  have hε := norm_chargeErrPow_window ht hs2
  have hAd := norm_chA_sub_one_le ht0 ht1 hs12
  have hφ := abs_chPhim_le ht0 ht1 (by linarith [chM_ge n]) (chM_le n) hs12
  have hA8 : ‖chA t s - 1‖ ≤ 1 / 8 := by
    refine le_trans hAd ?_
    rw [div_le_iff₀ (by positivity)]
    have : 10 * |s| ≤ 10 * (144 * ((n : ℝ) + 1) * t ^ 3) := by linarith
    have e : 10 * (144 * ((n : ℝ) + 1) * t ^ 3) = 1440 * (t * ((n : ℝ) + 1)) * t ^ 2 := by ring
    nlinarith [pow_pos ht0 2]
  have hφ16 : |(chPsim (chM n) t s).im + chM n * π / 8| ≤ 1 / 16 := by
    refine le_trans hφ ?_
    rw [div_le_iff₀ (by positivity)]
    have h3 : |s| ^ 3 ≤ (144 * ((n : ℝ) + 1) * t ^ 3) ^ 3 := pow_le_pow_left₀ (abs_nonneg s) hs 3
    have e : 11 * ((n : ℝ) + 1) * (144 * ((n : ℝ) + 1) * t ^ 3) ^ 3 =
        11 * 144 ^ 3 * (t * ((n : ℝ) + 1) ^ 4) * t ^ 8 := by ring
    have h4 : t * ((n : ℝ) + 1) ^ 4 ≤ 1 / 10000000000 := by
      have := ht.2; rw [le_div_iff₀ (by norm_num)]; nlinarith
    calc 11 * ((n : ℝ) + 1) * |s| ^ 3 ≤ 11 * ((n : ℝ) + 1) * (144 * ((n : ℝ) + 1) * t ^ 3) ^ 3 := by
          gcongr
      _ = 11 * 144 ^ 3 * (t * ((n : ℝ) + 1) ^ 4) * t ^ 8 := e
      _ ≤ 11 * 144 ^ 3 * (1 / 10000000000) * t ^ 8 := by gcongr
      _ ≤ 1 / 16 * t ^ 8 := by nlinarith [pow_pos ht0 8]
  have hexp1 : ‖Complex.exp (Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ)) - 1‖ ≤
      1 / 8 := by
    have h := Complex.norm_exp_sub_one_le
      (x := Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ))
      (by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; linarith)
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hc : ‖Complex.exp (Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hU1 : ‖U - 1‖ ≤ 1 / 2 := by
    have e : U - 1 = (chA t s - 1) *
        Complex.exp (Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ)) *
        (1 + chargeErrPow n (chV t s)) +
        (Complex.exp (Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ)) - 1) *
          (1 + chargeErrPow n (chV t s)) + chargeErrPow n (chV t s) := by rw [hU]; ring
    have h1e : ‖1 + chargeErrPow n (chV t s)‖ ≤ 9 / 8 := by
      refine le_trans (norm_add_le _ _) ?_; rw [norm_one]; linarith
    rw [e]
    calc _ ≤ ‖(chA t s - 1) *
            Complex.exp (Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ)) *
            (1 + chargeErrPow n (chV t s))‖ +
          ‖(Complex.exp (Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ)) - 1) *
            (1 + chargeErrPow n (chV t s))‖ + ‖chargeErrPow n (chV t s)‖ := norm_add₃_le
      _ = ‖chA t s - 1‖ * 1 * ‖1 + chargeErrPow n (chV t s)‖ +
          ‖Complex.exp (Complex.I * (((chPsim (chM n) t s).im + chM n * π / 8 : ℝ) : ℂ)) - 1‖ *
            ‖1 + chargeErrPow n (chV t s)‖ + ‖chargeErrPow n (chV t s)‖ := by
          rw [norm_mul, norm_mul, norm_mul, hc]
      _ ≤ 1 / 8 * 1 * (9 / 8) + 1 / 8 * (9 / 8) + 1 / 8 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hReU : 1 / 2 ≤ U.re := by
    have h := Complex.abs_re_le_norm (U - 1)
    rw [Complex.sub_re, Complex.one_re] at h
    have := abs_le.mp (le_trans h hU1)
    linarith [this.1]
  have hG : 0 ≤ chG0p n t := by unfold chG0p; have := chP0_pos (t := t); positivity
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hpos : 0 ≤ chG0p n t * Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) :=
    mul_nonneg hG (Real.exp_pos _).le
  nlinarith

end FactorizationP

end

end RHTower
