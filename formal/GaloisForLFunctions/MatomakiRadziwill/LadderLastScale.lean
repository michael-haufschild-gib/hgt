import GaloisForLFunctions.MatomakiRadziwill.LadderFirstTerm

/-!
# The last ladder scale is large enough for the exceptional set

Let `J = ladderJ L X ≥ 2` and `a = a_{J−1}`.  Since `b_J = 4a^8 > (log X)^{0.93}` (`seqA_last_pow_gt`),
`a^8 > (log X)^{0.93}/4`, hence `a > ((log X)^{0.93}/4)^{1/8}`.  For `log X` large this gives
`a·(log X)^{0.93} ≥ 864 log X`, and then (`last_scale_condition`), for `W ≤ X`,

`18 (log W/(a − 1/H_{J−1}) + 1) ≤ H_{J−1} = a^8`,

the hypothesis of `exceptional_volume_le` at the last scale.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem ladderJ_pos {L : ℝ} (hL : 2 ^ 20 ≤ L) {X : ℝ} (hX : seqB L 1 ≤ ladderTopLow X) :
    2 ≤ ladderJ hL X := by
  by_contra h
  push Not at h
  have hlt := lt_seqB_ladderJ hL X
  have hmono := seqB_mono hL (show ladderJ hL X ≤ 1 by omega)
  linarith

/-- `b_J = 4 a_{J−1}^8 > (log X)^{0.93}` for `J ≥ 2`. -/
theorem seqA_last_pow_gt {L : ℝ} (hL : 2 ^ 20 ≤ L) {X : ℝ} (hJ : 2 ≤ ladderJ hL X) :
    ladderTopLow X < 4 * seqA L (ladderJ hL X - 1) ^ 8 := by
  have hlt := lt_seqB_ladderJ hL X
  obtain ⟨k, hk⟩ : ∃ k, ladderJ hL X = k + 2 := ⟨ladderJ hL X - 2, by omega⟩
  rw [hk] at hlt ⊢
  have h1 : seqB L (k + 2) = 4 * seqB L (k + 1) ^ 4 := rfl
  have h2 : seqB L (k + 1) = seqA L (k + 1) ^ 2 := seqB_succ_eq L k
  have h3 : k + 2 - 1 = k + 1 := by omega
  rw [h3]
  rw [h1, h2] at hlt
  calc ladderTopLow X < 4 * (seqA L (k + 1) ^ 2) ^ 4 := hlt
    _ = 4 * seqA L (k + 1) ^ 8 := by ring

/-- For large `log X`: `((log X)^{0.93}/4)^{1/8} · (log X)^{0.93} ≥ 864 log X`. -/
theorem eventually_last_scale_large :
    ∀ᶠ ℓ : ℝ in atTop, 864 * ℓ ≤ (ℓ ^ (93 / 100 : ℝ) / 4) ^ (1 / 8 : ℝ) * ℓ ^ (93 / 100 : ℝ) := by
  -- `(ℓ^{0.93}/4)^{1/8} ℓ^{0.93} = 4^{-1/8} ℓ^{1.04625}`, and `ℓ^{0.04625} → ∞`
  have hlim := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 37 / 800)).eventually_ge_atTop
    (864 * 4 ^ (1 / 8 : ℝ))
  filter_upwards [hlim, eventually_gt_atTop 0] with ℓ h hℓ
  have h4 : (0 : ℝ) < 4 ^ (1 / 8 : ℝ) := by positivity
  have e1 : (ℓ ^ (93 / 100 : ℝ) / 4) ^ (1 / 8 : ℝ)
      = ℓ ^ (93 / 800 : ℝ) / 4 ^ (1 / 8 : ℝ) := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hℓ.le]
    norm_num
  have e2 : ℓ ^ (93 / 800 : ℝ) * ℓ ^ (93 / 100 : ℝ) = ℓ ^ (37 / 800 : ℝ) * ℓ := by
    rw [← Real.rpow_add hℓ, ← Real.rpow_add_one hℓ.ne']
    norm_num
  rw [e1, div_mul_eq_mul_div, e2, le_div_iff₀ h4]
  have hℓ0 : 0 ≤ ℓ := hℓ.le
  nlinarith

/-- **The last ladder scale admits the exceptional set.** -/
theorem last_scale_condition {L : ℝ} (hL : 2 ^ 20 ≤ L) {X : ℝ} (hX1 : 1 ≤ X)
    (hJ : 2 ≤ ladderJ hL X)
    (hlarge : 864 * Real.log X
      ≤ (Real.log X ^ (93 / 100 : ℝ) / 4) ^ (1 / 8 : ℝ) * Real.log X ^ (93 / 100 : ℝ))
    {W : ℝ} (hW1 : 1 ≤ W) (hWX : W ≤ X) :
    18 * (Real.log W / (seqA L (ladderJ hL X - 1) - 1 / seqH L (ladderJ hL X - 1)) + 1)
      ≤ seqH L (ladderJ hL X - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, ladderJ hL X - 1 = k + 1 := ⟨ladderJ hL X - 2, by omega⟩
  have hpow := seqA_last_pow_gt hL hJ
  rw [hk] at hpow ⊢
  set a := seqA L (k + 1) with hadef
  have hH : seqH L (k + 1) = a ^ 8 := rfl
  rw [hH]
  have ha := seqA_succ_ge (by linarith : (2 : ℝ) ≤ L) k
  rw [← hadef] at ha
  have ha2 : (2 : ℝ) ^ 39 ≤ a := le_trans (by nlinarith) ha
  have ha1 : 1 ≤ a := by linarith
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlogW : Real.log W ≤ Real.log X := Real.log_le_log (by linarith) hWX
  have hlogW0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  -- `a ≥ ((log X)^{0.93}/4)^{1/8}`
  have hy : 0 ≤ ladderTopLow X / 4 := by unfold ladderTopLow; positivity
  have ha8 : ladderTopLow X / 4 ≤ a ^ 8 := by linarith
  have haroot : (ladderTopLow X / 4) ^ (1 / 8 : ℝ) ≤ a := by
    have h1 : (ladderTopLow X / 4) ^ (1 / 8 : ℝ) ≤ (a ^ 8) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow hy ha8 (by norm_num)
    have h2 : (a ^ 8) ^ (1 / 8 : ℝ) = a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    linarith
  -- `a^9 ≥ a · (log X)^{0.93}/4 ≥ 216 log X`
  have hkey : 216 * Real.log X ≤ a * a ^ 8 := by
    have h1 : (ladderTopLow X / 4) ^ (1 / 8 : ℝ) * ladderTopLow X ≤ a * (4 * a ^ 8) :=
      mul_le_mul haroot (by linarith) (by unfold ladderTopLow; positivity) (by linarith)
    unfold ladderTopLow at h1
    linarith
  have hinv : 1 / a ^ 8 ≤ a / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ a ^ 8 := one_le_pow₀ ha1
    nlinarith
  have hden : a / 2 ≤ a - 1 / a ^ 8 := by linarith
  have hratio : Real.log W / (a - 1 / a ^ 8) ≤ 2 * Real.log X / a := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h18 : 18 * (2 * Real.log X / a + 1) ≤ a ^ 8 := by
    have h1 : 36 * Real.log X / a ≤ a ^ 8 / 6 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    have h2 : 18 ≤ a ^ 8 / 2 := by
      have : (2 : ℝ) ^ 39 ≤ a ^ 8 := le_trans ha2 (by
        calc a = a ^ 1 := (pow_one a).symm
          _ ≤ a ^ 8 := pow_le_pow_right₀ ha1 (by norm_num))
      linarith
    have e : 18 * (2 * Real.log X / a + 1) = 36 * Real.log X / a + 18 := by ring
    linarith
  calc 18 * (Real.log W / (a - 1 / a ^ 8) + 1) ≤ 18 * (2 * Real.log X / a + 1) := by linarith
    _ ≤ a ^ 8 := h18

end

end GaloisForLFunctions.MatomakiRadziwill
