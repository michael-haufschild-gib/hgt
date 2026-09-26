import GaloisForLFunctions.RHTower.ThetaCuspChargePowFarField

open Complex MeasureTheory Set
open scoped Real

namespace RHTower

noncomputable section

section IntegrationP

variable {t : ℝ}

/-- The shifted-line function of the tail of `θ₃hʲ` at frequency `u`. -/
def chLineJ (j : ℕ) (u t s : ℝ) : ℂ :=
  Complex.exp (-Complex.I * u * s) *
    chargeTailC (thetaGroupBasis j) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)

theorem continuous_chLineJ (j : ℕ) (u : ℝ) (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) :
    Continuous (chLineJ j u t) := by
  have hβ := chBeta_lt ht (by linarith)
  have hβ0 := chBeta_nonneg ht2
  have hc := continuousOn_chargeTailC (differentiableOn_thetaGroupBasis j) hβ
  have h1 : Continuous (fun s : ℝ => (s : ℂ) - (chBeta t : ℂ) * Complex.I) := by fun_prop
  have h2 := hc.comp_continuous h1 (fun s => by simp [abs_of_nonneg hβ0])
  unfold chLineJ
  exact (by fun_prop : Continuous fun s : ℝ => Complex.exp (-Complex.I * u * s)).mul h2

theorem norm_chLineJ (j : ℕ) (u t s : ℝ) :
    ‖chLineJ j u t s‖ =
      ‖chargeTailC (thetaGroupBasis j) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)‖ := by
  unfold chLineJ; rw [norm_mul, Complex.norm_exp]
  have : (-Complex.I * (u : ℂ) * (s : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, one_mul]

theorem integrable_chLineJ (j : ℕ) (hj : j ≠ 0) (u : ℝ) (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) :
    Integrable (chLineJ j u t) := by
  have hβ := chBeta_lt ht (by linarith)
  have hβ0 := chBeta_nonneg ht2
  obtain ⟨M, hM⟩ := thetaGroupBasis_cuspDecay j
  have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis j τ‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; have := hM τ hτ; simpa [thetaGroupBasisCusp, hj] using this
  obtain ⟨C, hC, hbd⟩ := exists_norm_chargeTailC_le (differentiableOn_thetaGroupBasis j)
    (fun τ hτ => thetaGroupBasis_S j hτ) hM' hβ0 hβ
  refine MeasureTheory.Integrable.mono' ((integrable_exp_neg_mul_abs' one_pos).const_mul C)
    (continuous_chLineJ j u ht ht2).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  have hz : |((s : ℂ) - (chBeta t : ℂ) * Complex.I).im| ≤ chBeta t := by
    simp [abs_of_nonneg hβ0]
  have h := hbd _ hz
  have hre : ((s : ℂ) - (chBeta t : ℂ) * Complex.I).re = s := by simp
  rw [hre] at h
  rw [norm_chLineJ]
  simpa using h

theorem chLineP_eq_chLineJ (n : ℕ) (t s : ℝ) :
    chLineP n t s = chLineJ (n + 1) (chUm (chM n) t) t s := rfl

/-- The full shifted-line integral for `θ₃hⁿ⁺¹`. -/
def chLinePInt (n : ℕ) (t : ℝ) : ℂ := ∫ s : ℝ, chLineP n t s

theorem re_chLinePInt_ge {n : ℕ} (ht : chSmall n t) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis (n + 1) τ‖ ≤ M * Real.exp (-π * τ.im)) :
    chG0p n t * t ^ 3 / (16 * ((n : ℝ) + 1)) - 2 * chBfarP n t M ≤ (chLinePInt n t).re := by
  have ht0 := ht.1
  have htle := ht.le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 160 := by nlinarith
  have ht2' : t ^ 2 ≤ 1 / 2 := by linarith
  have ht4 : t ^ 4 ≤ 1 / 6 := by nlinarith [pow_pos ht0 2]
  have hG : 0 < chG0p n t := by unfold chG0p; have := chP0_pos (t := t); positivity
  have hint : Integrable (chLineP n t) := by
    have := integrable_chLineJ (n + 1) (by omega) (chUm (chM n) t) ht0 ht2'
    exact this
  have hre_int : Integrable (fun s => (chLineP n t s).re) := hint.re
  set inner : Set ℝ := Icc (-(t ^ 3 / (4 * ((n : ℝ) + 1)))) (t ^ 3 / (4 * ((n : ℝ) + 1))) with hinner
  set k : ℝ := 36 * ((n : ℝ) + 1) / t ^ 3 with hk
  have hk0 : 0 < k := by positivity
  set lam : ℝ → ℝ := fun s =>
    9 / 8 * chG0p n t * Real.exp (-(k * |s|)) + chBfarP n t M * Real.exp (-(1 * |s|)) with hlam
  have hBf : 0 ≤ chBfarP n t M := chBfarP_nonneg n ht0 (by linarith) M
  have hlam_int : Integrable lam :=
    ((integrable_exp_neg_mul_abs' hk0).const_mul _).add
      ((integrable_exp_neg_mul_abs' one_pos).const_mul _)
  have hlam_val : ∫ s, lam s = chG0p n t * t ^ 3 / (16 * ((n : ℝ) + 1)) + 2 * chBfarP n t M := by
    rw [hlam, integral_add ((integrable_exp_neg_mul_abs' hk0).const_mul _)
      ((integrable_exp_neg_mul_abs' one_pos).const_mul _), integral_const_mul, integral_const_mul,
      integral_exp_neg_mul_abs_eq hk0, integral_exp_neg_mul_abs_eq one_pos, hk]
    field_simp; ring
  have hcore : ∀ s, |s| ≤ 144 * ((n : ℝ) + 1) * t ^ 3 → 0 ≤ (chLineP n t s).re := by
    intro s hs
    have h := half_le_re_chLineP_core ht hs
    have : 0 ≤ chG0p n t * Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) / 2 := by
      positivity
    linarith
  have hinner_lb : ∀ s ∈ inner, chG0p n t / 4 ≤ (chLineP n t s).re := by
    intro s hs
    have hs' : |s| ≤ t ^ 3 / (4 * ((n : ℝ) + 1)) := abs_le.mpr ⟨hs.1, hs.2⟩
    have hs144 : |s| ≤ 144 * ((n : ℝ) + 1) * t ^ 3 := by
      have : t ^ 3 / (4 * ((n : ℝ) + 1)) ≤ 144 * ((n : ℝ) + 1) * t ^ 3 := by
        rw [div_le_iff₀ (by positivity)]
        have h576 : (1:ℝ) ≤ 144 * ((n : ℝ) + 1) * (4 * ((n : ℝ) + 1)) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h576 (pow_pos ht0 3).le]
      linarith
    have h := half_le_re_chLineP_core ht hs144
    have hd := chR0m_sub_psim_re_le_inner ht0 ht1 (by linarith [chM_ge n]) (chM_le n) hs'
    have he : 1 / 2 ≤ Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) := by
      have := Real.add_one_le_exp ((chPsim (chM n) t s).re - chR0m (chM n) t); linarith
    nlinarith
  have hout : ∀ s, -lam s ≤ (chLineP n t s).re := by
    intro s
    have hl1 : 0 ≤ 9 / 8 * chG0p n t * Real.exp (-(k * |s|)) := by positivity
    have hl2 : 0 ≤ chBfarP n t M * Real.exp (-(1 * |s|)) := by positivity
    have hneg : -‖chLineP n t s‖ ≤ (chLineP n t s).re := by
      have := Complex.abs_re_le_norm (chLineP n t s); have := neg_abs_le (chLineP n t s).re; linarith
    rcases le_or_gt |s| (144 * ((n : ℝ) + 1) * t ^ 3) with h1 | h1
    · have := hcore s h1; simp only [hlam]; linarith
    rcases le_or_gt |s| (2 * t ^ 2) with h2 | h2
    · have hw := norm_chLineP_le_window ht h2
      have hmid := chR0m_sub_psim_re_ge_mid (chM_ge n) ht0 (by linarith) h2
      have hexp : Real.exp ((chPsim (chM n) t s).re - chR0m (chM n) t) ≤ Real.exp (-(k * |s|)) := by
        apply Real.exp_le_exp.mpr
        have hsq : 144 * ((n : ℝ) + 1) * t ^ 3 * |s| ≤ s ^ 2 := by
          rw [← sq_abs s]; nlinarith [abs_nonneg s]
        have : k * |s| ≤ s ^ 2 / (4 * t ^ 6) := by
          rw [hk, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_pos ht0 3, abs_nonneg s]
        linarith
      have : ‖chLineP n t s‖ ≤ 9 / 8 * chG0p n t * Real.exp (-(k * |s|)) := by
        refine le_trans hw ?_
        have := mul_le_mul_of_nonneg_left hexp hG.le
        nlinarith
      simp only [hlam]; linarith
    · have hf := norm_chargeTailPow_far n ht0 ht4 hM h2.le
      have hnorm : ‖chLineP n t s‖ =
          ‖chargeTailC (thetaGroupBasis (n + 1)) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)‖ := by
        rw [chLineP_eq_chLineJ, norm_chLineJ]
      rw [hnorm] at hneg
      simp only [hlam, one_mul]
      linarith
  have hsplit := integral_add_compl (μ := volume) measurableSet_Icc hre_int (s := inner)
  unfold chLinePInt
  have hre_eq : (∫ s, chLineP n t s).re = ∫ s, (chLineP n t s).re := (integral_re hint).symm
  rw [hre_eq, ← hsplit]
  have hA : chG0p n t / 4 * (t ^ 3 / (2 * ((n : ℝ) + 1))) ≤ ∫ s in inner, (chLineP n t s).re := by
    have hc : ∫ s in inner, (chG0p n t / 4 : ℝ) = chG0p n t / 4 * (t ^ 3 / (2 * ((n : ℝ) + 1))) := by
      rw [setIntegral_const, smul_eq_mul, hinner, Real.volume_real_Icc_of_le (by
        have : 0 ≤ t ^ 3 / (4 * ((n : ℝ) + 1)) := by positivity
        linarith)]
      field_simp; ring
    rw [← hc]
    exact setIntegral_mono_on (integrableOn_const (by simp [hinner, Real.volume_Icc]))
      hre_int.integrableOn measurableSet_Icc hinner_lb
  have hB : -(∫ s, lam s) ≤ ∫ s in innerᶜ, (chLineP n t s).re := by
    have h1 : ∫ s in innerᶜ, -lam s ≤ ∫ s in innerᶜ, (chLineP n t s).re :=
      setIntegral_mono_on hlam_int.neg.integrableOn hre_int.integrableOn
        measurableSet_Icc.compl (fun s _ => hout s)
    have h2 : ∫ s in innerᶜ, lam s ≤ ∫ s, lam s :=
      setIntegral_le_integral hlam_int (Filter.Eventually.of_forall fun s => by
        simp only [hlam]; positivity)
    rw [integral_neg] at h1
    linarith
  rw [hlam_val] at hB
  have e : chG0p n t / 4 * (t ^ 3 / (2 * ((n : ℝ) + 1))) =
      2 * (chG0p n t * t ^ 3 / (16 * ((n : ℝ) + 1))) := by field_simp; ring
  linarith


theorem chR0m_ge (n : ℕ) (ht : 0 < t) (ht4 : t ^ 4 ≤ 3 / 4) : 1 / t ^ 2 ≤ chR0m (chM n) t := by
  unfold chR0m
  have hb := half_le_chB (t := t) ht4
  have hπ := Real.pi_gt_three
  have hm := chM_ge n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (21 : ℝ) ≤ chM n * π := by nlinarith [mul_le_mul hm (le_of_lt hπ) (by norm_num) (by linarith)]
  nlinarith [pow_pos ht 2, mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ chB t)]

theorem far_branch_one_le (n : ℕ) {t κ R : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hκ : t ^ 2 ≤ κ)
    (hRt : 1 ≤ R * t ^ 2)
    (htQ : t * (10000 * 3 ^ (8 * (n + 1)) * 2 ^ (16 * (n + 1)) * (32 * ((n : ℝ) + 1))) ≤ 1) :
    3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * κ⁻¹ ^ 3 * Real.exp (R / 3) ≤
      (2 ^ (8 * (n + 1)))⁻¹ / (32 * ((n : ℝ) + 1)) * Real.exp R * t ^ 3 := by
  have ht2p : 0 < t ^ 2 := by positivity
  have hκ0 : 0 < κ := lt_of_lt_of_le ht2p hκ
  have hR0 : 0 ≤ R := by
    by_contra h; push Not at h; nlinarith
  set c : ℝ := (2 ^ (8 * (n + 1)))⁻¹ / (32 * ((n : ℝ) + 1)) with hc
  set Q : ℝ := 3 ^ (8 * (n + 1)) * 2 ^ (16 * (n + 1)) * (32 * ((n : ℝ) + 1)) with hQ
  have hinv : κ⁻¹ ≤ 1 / t ^ 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le ht2p hκ
  have hinv3 : κ⁻¹ ^ 3 ≤ (1 / t ^ 2) ^ 3 := pow_le_pow_left₀ (inv_nonneg.mpr hκ0.le) hinv 3
  have hA := pow_six_div_le_exp (x := 2 * R / 3) (by positivity)
  have hsplit : Real.exp R = Real.exp (R / 3) * Real.exp (2 * R / 3) := by
    rw [← Real.exp_add]; ring_nf
  have hA2 : (2 / 3) ^ 6 / 720 ≤ t ^ 12 * Real.exp (2 * R / 3) := by
    have h6 : (2 / 3 : ℝ) ^ 6 ≤ (2 * R / 3) ^ 6 * t ^ 12 := by
      have e : (2 * R / 3) ^ 6 * t ^ 12 = (2 / 3) ^ 6 * (R * t ^ 2) ^ 6 := by ring
      rw [e]
      have := one_le_pow₀ hRt (n := 6)
      have h23 : (0:ℝ) ≤ (2 / 3) ^ 6 := by positivity
      calc (2 / 3 : ℝ) ^ 6 = (2 / 3) ^ 6 * 1 := by ring
        _ ≤ (2 / 3) ^ 6 * (R * t ^ 2) ^ 6 := mul_le_mul_of_nonneg_left this h23
    have h7 := mul_le_mul_of_nonneg_right hA (by positivity : (0:ℝ) ≤ t ^ 12)
    calc (2 / 3 : ℝ) ^ 6 / 720 ≤ (2 * R / 3) ^ 6 * t ^ 12 / 720 := by gcongr
      _ = (2 * R / 3) ^ 6 / 720 * t ^ 12 := by ring
      _ ≤ Real.exp (2 * R / 3) * t ^ 12 := h7
      _ = t ^ 12 * Real.exp (2 * R / 3) := by ring
  have hkey : Q ≤ t ^ 9 * Real.exp (2 * R / 3) := by
    have h1 : 1 / 10000 ≤ t ^ 12 * Real.exp (2 * R / 3) := le_trans (by norm_num) hA2
    have ht3 : t ^ 3 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
    have hQ0 : 0 ≤ Q := by positivity
    have h2 : t ^ 3 * Q ≤ 1 / 10000 := by
      have := mul_le_mul_of_nonneg_right ht3 hQ0
      have e : t * (10000 * 3 ^ (8 * (n + 1)) * 2 ^ (16 * (n + 1)) * (32 * ((n : ℝ) + 1))) =
          10000 * (t * Q) := by rw [hQ]; ring
      rw [e] at htQ
      linarith
    have e : t ^ 12 * Real.exp (2 * R / 3) = t ^ 3 * (t ^ 9 * Real.exp (2 * R / 3)) := by ring
    rw [e] at h1
    have ht3p : 0 < t ^ 3 := by positivity
    by_contra hc'
    push Not at hc'
    have := mul_lt_mul_of_pos_left hc' ht3p
    linarith
  have h22 : (2 : ℝ) ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) = 2 ^ (16 * (n + 1)) := by
    rw [← pow_add]; congr 1; ring
  have h2a : (2 : ℝ) ^ (8 * (n + 1)) ≠ 0 := by positivity
  have h32 : (32 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  have hcQ : c * Q = 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) := by
    calc c * Q = 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) *
          (((2 : ℝ) ^ (8 * (n + 1)))⁻¹ * 2 ^ (8 * (n + 1))) *
          ((32 * ((n : ℝ) + 1))⁻¹ * (32 * ((n : ℝ) + 1))) := by
          rw [hc, hQ, ← h22]; ring
      _ = 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) := by
          rw [inv_mul_cancel₀ h2a, inv_mul_cancel₀ h32]; ring
  have ht9 : t ^ 9 * (1 / t ^ 2) ^ 3 = t ^ 3 := by field_simp
  have hcpos : 0 ≤ c := by positivity
  calc 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * κ⁻¹ ^ 3 * Real.exp (R / 3)
      ≤ 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * (1 / t ^ 2) ^ 3 * Real.exp (R / 3) := by gcongr
    _ = c * (Q * (1 / t ^ 2) ^ 3) * Real.exp (R / 3) := by rw [← hcQ]; ring
    _ ≤ c * (t ^ 9 * Real.exp (2 * R / 3) * (1 / t ^ 2) ^ 3) * Real.exp (R / 3) := by gcongr
    _ = c * (t ^ 9 * (1 / t ^ 2) ^ 3) * (Real.exp (R / 3) * Real.exp (2 * R / 3)) := by ring
    _ = c * Real.exp R * t ^ 3 := by rw [ht9, ← hsplit]; ring

theorem far_branch_two_le (n : ℕ) {t κ R M : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hκ : t ^ 2 ≤ κ)
    (hRt : 1 ≤ R * t ^ 2) (hM0 : 0 ≤ M)
    (htM : t * (720 * 2 ^ (8 * (n + 1)) * (32 * ((n : ℝ) + 1)) * (M + 1)) ≤ 1) :
    M / 2 * (1 / (π * κ)) * 2 ≤ (2 ^ (8 * (n + 1)))⁻¹ / (32 * ((n : ℝ) + 1)) * Real.exp R * t ^ 3 := by
  have ht2p : 0 < t ^ 2 := by positivity
  have hκ0 : 0 < κ := lt_of_lt_of_le ht2p hκ
  have hR0 : 0 ≤ R := by
    by_contra h; push Not at h; nlinarith
  have hπ1 : 1 ≤ π := by linarith [Real.pi_gt_three]
  set W : ℝ := 2 ^ (8 * (n + 1)) * (32 * ((n : ℝ) + 1)) with hW
  have hWpos : 0 < W := by positivity
  have h1 : M / 2 * (1 / (π * κ)) * 2 ≤ M / t ^ 2 := by
    rw [show M / 2 * (1 / (π * κ)) * 2 = M / (π * κ) by field_simp]
    apply div_le_div_of_nonneg_left hM0 ht2p
    calc t ^ 2 ≤ κ := hκ
      _ ≤ π * κ := le_mul_of_one_le_left hκ0.le hπ1
  have hE := pow_six_div_le_exp hR0
  have hR6 : 1 ≤ (R * t ^ 2) ^ 6 := one_le_pow₀ hRt
  have ht7 : t ^ 7 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
  have hMt : (M + 1) * t ^ 7 * (720 * W) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left ht7 (by positivity : (0:ℝ) ≤ (M + 1) * (720 * W))
    have e : t * (720 * 2 ^ (8 * (n + 1)) * (32 * ((n : ℝ) + 1)) * (M + 1)) =
        (M + 1) * (720 * W) * t := by rw [hW]; ring
    calc (M + 1) * t ^ 7 * (720 * W) = (M + 1) * (720 * W) * t ^ 7 := by ring
      _ ≤ (M + 1) * (720 * W) * t := h1
      _ = t * (720 * 2 ^ (8 * (n + 1)) * (32 * ((n : ℝ) + 1)) * (M + 1)) := e.symm
      _ ≤ 1 := htM
  have hkey : W * M ≤ t ^ 5 * Real.exp R := by
    have h12 : 1 ≤ R ^ 6 * t ^ 12 := by
      have : (R * t ^ 2) ^ 6 = R ^ 6 * t ^ 12 := by ring
      linarith
    have h720 : 1 ≤ 720 * (t ^ 12 * Real.exp R) := by
      have h3 := mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ) ≤ t ^ 12)
      have e : t ^ 12 * (R ^ 6 / 720) = R ^ 6 * t ^ 12 / 720 := by ring
      rw [e] at h3
      linarith
    have ht7p : 0 < 720 * t ^ 7 := by positivity
    have h2 : 720 * t ^ 7 * (W * M) ≤ 720 * t ^ 7 * (t ^ 5 * Real.exp R) := by
      have e1 : 720 * t ^ 7 * (t ^ 5 * Real.exp R) = 720 * (t ^ 12 * Real.exp R) := by ring
      rw [e1]
      have e2 : 720 * t ^ 7 * (W * M) ≤ (M + 1) * t ^ 7 * (720 * W) := by
        have : 0 ≤ t ^ 7 * (720 * W) := by positivity
        nlinarith
      linarith
    exact le_of_mul_le_mul_left h2 ht7p
  calc M / 2 * (1 / (π * κ)) * 2 ≤ M / t ^ 2 := h1
    _ ≤ (2 ^ (8 * (n + 1)))⁻¹ / (32 * ((n : ℝ) + 1)) * Real.exp R * t ^ 3 := by
        rw [div_le_iff₀ ht2p]
        have e2 : (2 ^ (8 * (n + 1)))⁻¹ / (32 * ((n : ℝ) + 1)) * Real.exp R * t ^ 3 * t ^ 2 =
            t ^ 5 * Real.exp R / W := by rw [hW]; field_simp
        rw [e2, le_div_iff₀ hWpos]; linarith

/-- **The far field is negligible for pole order `8n+7`.** -/
theorem two_chBfarP_le {n : ℕ} (ht : chSmall n t) {M : ℝ} (hM0 : 0 ≤ M)
    (htQ : t * (10000 * 3 ^ (8 * (n + 1)) * 2 ^ (16 * (n + 1)) * (32 * ((n : ℝ) + 1))) ≤ 1)
    (htM : t * (720 * 2 ^ (8 * (n + 1)) * (32 * ((n : ℝ) + 1)) * (M + 1)) ≤ 1) :
    2 * chBfarP n t M ≤ chG0p n t * t ^ 3 / (32 * ((n : ℝ) + 1)) := by
  have ht0 := ht.1
  have htle := ht.le
  have ht1 : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 3 / 4 := by
    have := pow_le_of_le_one ht0.le ht1 (by norm_num : (4:ℕ) ≠ 0); linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have := pow_le_of_le_one ht0.le ht1 (by norm_num : (2:ℕ) ≠ 0); linarith
  have hκ := chKap_ge ht4
  have hR := chR0m_ge n ht0 ht4
  have ht2p : 0 < t ^ 2 := by positivity
  have hRt : 1 ≤ chR0m (chM n) t * t ^ 2 := by rw [div_le_iff₀ ht2p] at hR; linarith
  have hp := one_le_chP0 ht0 ht2
  have hGt : (2 ^ (8 * (n + 1)))⁻¹ / (32 * ((n : ℝ) + 1)) * Real.exp (chR0m (chM n) t) * t ^ 3 ≤
      chG0p n t * t ^ 3 / (32 * ((n : ℝ) + 1)) := by
    unfold chG0p
    have e : (2 ^ (8 * (n + 1)))⁻¹ / (32 * ((n : ℝ) + 1)) * Real.exp (chR0m (chM n) t) * t ^ 3 =
        (2 ^ (8 * (n + 1)))⁻¹ * 1 * Real.exp (chR0m (chM n) t) * t ^ 3 / (32 * ((n : ℝ) + 1)) := by
      ring
    rw [e]
    gcongr
  have h1 := far_branch_one_le n ht0 ht1 hκ hRt htQ
  have h2 := far_branch_two_le n ht0 ht1 hκ hRt hM0 htM
  unfold chBfarP
  rw [mul_comm, max_mul_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  refine le_trans (max_le ?_ h2) hGt
  linarith

/-- **Positivity of the saddle-line integral for `θ₃hⁿ⁺¹`.** -/
theorem exists_re_chLinePInt_pos (n : ℕ) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t : ℝ, 0 < t → t ≤ t₁ →
      chSmall n t ∧ chG0p n t * t ^ 3 / (32 * ((n : ℝ) + 1)) ≤ (chLinePInt n t).re := by
  obtain ⟨M, hM⟩ := thetaGroupBasis_cuspDecay (n + 1)
  have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis (n + 1) τ‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; have := hM τ hτ; simpa [thetaGroupBasisCusp] using this
  have hM0 : 0 ≤ M := by
    have h := hM' Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  set A : ℝ := 10000000000 * ((n : ℝ) + 1) ^ 4 with hA
  set B : ℝ := 10000 * 3 ^ (8 * (n + 1)) * 2 ^ (16 * (n + 1)) * (32 * ((n : ℝ) + 1)) with hB
  set C : ℝ := 720 * 2 ^ (8 * (n + 1)) * (32 * ((n : ℝ) + 1)) * (M + 1) with hC
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hCpos : 0 < C := by positivity
  refine ⟨min (1 / A) (min (1 / B) (1 / C)), by positivity, fun t ht htt => ?_⟩
  have h1 : t * A ≤ 1 := by
    have := le_trans htt (min_le_left _ _); rw [le_div_iff₀ hApos] at this; linarith
  have h2 : t * B ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [le_div_iff₀ hBpos] at this; linarith
  have h3 : t * C ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [le_div_iff₀ hCpos] at this; linarith
  have hs : chSmall n t := ⟨ht, h1⟩
  refine ⟨hs, ?_⟩
  have hlo := re_chLinePInt_ge hs hM'
  have hab := two_chBfarP_le hs hM0 h2 h3
  have : chG0p n t * t ^ 3 / (16 * ((n : ℝ) + 1)) =
      2 * (chG0p n t * t ^ 3 / (32 * ((n : ℝ) + 1))) := by field_simp; ring
  linarith

/-- **The transform of `θ₃hⁿ⁺¹` at its saddle frequency.** -/
theorem thetaGroupXi_succ_chU (n : ℕ) (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) (u : ℝ) :
    thetaGroupXi (n + 1) (u : ℂ) = -((u : ℂ) ^ 2 + 1 / 4) *
      (Complex.exp (-(u * chBeta t : ℝ)) * ∫ s : ℝ, chLineJ (n + 1) u t s) := by
  obtain ⟨M, hM⟩ := thetaGroupBasis_cuspDecay (n + 1)
  have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis (n + 1) τ‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; have := hM τ hτ; simpa [thetaGroupBasisCusp] using this
  have hM'' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis (n + 1) τ - 0‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; rw [sub_zero]; exact hM' τ hτ
  have hF := differentiableOn_thetaGroupBasis (n + 1)
  have hβ := chBeta_lt ht (by linarith)
  have hβ0 := chBeta_nonneg ht2
  unfold thetaGroupXi
  rw [modXi_eq_tailTransform hF (thetaGroupBasis_axis (n + 1)) hM'' (u : ℂ)]
  rw [integral_tail_shift hF (fun τ hτ => thetaGroupBasis_S (n + 1) hτ) hM' hβ0 hβ u]
  rfl

end IntegrationP

end

end RHTower
