import GaloisForLFunctions.RHTower.XiSliceGaussianTailLimit
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance

/-!
# Cutoff decay of the actual Xi reciprocal mass

Unit ordinate windows control the reciprocal mass after removing the centered
distance head. Two telescoping tails retain cutoff decay in both the height
term and the contribution of remote ordinate windows.
-/

open Complex Filter Topology
namespace RHTower
noncomputable section

private theorem gaussian_sum_inv_sq_Ico {N K : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico N K, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / ((N : ℝ) - 1) := by
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hstrong : ∀ K : ℕ, N ≤ K →
      ∑ k ∈ Finset.Ico N K, (1 : ℝ) / (k : ℝ) ^ 2 ≤
        1 / ((N : ℝ) - 1) - 1 / ((K : ℝ) - 1) := by
    intro K hNK
    induction K, hNK using Nat.le_induction with
    | base => simp
    | succ K hNK ih =>
      rw [Finset.sum_Ico_succ_top hNK]
      have hK1 : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
      have hstep : (1 : ℝ) / (K : ℝ) ^ 2 ≤
          1 / ((K : ℝ) - 1) - 1 / (K : ℝ) := by
        rw [div_sub_div _ _ (by linarith) (by linarith),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [hK1]
      have heq : ((K + 1 : ℕ) : ℝ) - 1 = K := by push_cast; ring
      rw [heq]
      linarith only [ih, hstep]
  by_cases hNK : N ≤ K
  · exact (hstrong K hNK).trans (sub_le_self _ (by
      have hK : (2 : ℝ) ≤ K := by exact_mod_cast hN.trans hNK
      exact div_nonneg zero_le_one (by linarith only [hK])))
  · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]
    exact div_nonneg zero_le_one (by linarith only [hNreal])

private theorem gaussian_sum_inv_sqrt_Ico {N K : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico N K, (1 : ℝ) / ((k : ℝ) * Real.sqrt k) ≤
      2 / Real.sqrt ((N : ℝ) - 1) := by
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hstrong : ∀ K : ℕ, N ≤ K →
      ∑ k ∈ Finset.Ico N K, (1 : ℝ) / ((k : ℝ) * Real.sqrt k) ≤
        2 * (1 / Real.sqrt ((N : ℝ) - 1) - 1 / Real.sqrt ((K : ℝ) - 1)) := by
    intro K hNK
    induction K, hNK using Nat.le_induction with
    | base => simp
    | succ K hNK ih =>
      rw [Finset.sum_Ico_succ_top hNK]
      have hstep := inv_mul_sqrt_le_telescope (hN.trans hNK)
      have heq : ((K + 1 : ℕ) : ℝ) - 1 = K := by push_cast; ring
      rw [heq]
      linarith only [ih, hstep]
  by_cases hNK : N ≤ K
  · have h := hstrong K hNK
    have hnonneg : 0 ≤ 1 / Real.sqrt ((K : ℝ) - 1) := by positivity
    calc
      _ ≤ 2 * (1 / Real.sqrt ((N : ℝ) - 1) - 1 / Real.sqrt ((K : ℝ) - 1)) := h
      _ ≤ 2 * (1 / Real.sqrt ((N : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ hnonneg) (by norm_num)
      _ = _ := by ring
  · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]
    positivity

private theorem gaussian_sum_window_tail {t : ℝ} (ht : 4 ≤ t) {N K : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico N K,
      (80 * Real.log (180 * (t + k + 1)) + smallHeightCount) / (k : ℝ) ^ 2 ≤
        (480 * Real.log t + 240 + smallHeightCount) / ((N : ℝ) - 1) +
          320 / Real.sqrt ((N : ℝ) - 1) := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith only [ht])
  have hterm : ∀ k ∈ Finset.Ico N K,
      (80 * Real.log (180 * (t + k + 1)) + smallHeightCount) / (k : ℝ) ^ 2 ≤
        (480 * Real.log t + 240 + smallHeightCount) * (1 / (k : ℝ) ^ 2) +
          160 * (1 / ((k : ℝ) * Real.sqrt k)) := by
    intro k hk
    have hk2 := hN.trans (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hlog1 := log_zeroWindow_le ht k
    have hlog2 := log_add_two_le hk2
    have hsq := Real.mul_self_sqrt hk0.le
    have heq :
        ((480 * Real.log t + 240 + smallHeightCount) * (1 / (k : ℝ) ^ 2) +
          160 * (1 / ((k : ℝ) * Real.sqrt k))) * (k : ℝ) ^ 2 =
          480 * Real.log t + 240 + smallHeightCount + 160 * Real.sqrt k := by
      have hs0 : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
      field_simp
      nlinarith only [hsq]
    rw [div_le_iff₀ (sq_pos_of_pos hk0), heq]
    linarith only [hlog1, hlog2]
  calc
    _ ≤ ∑ k ∈ Finset.Ico N K,
        ((480 * Real.log t + 240 + smallHeightCount) * (1 / (k : ℝ) ^ 2) +
          160 * (1 / ((k : ℝ) * Real.sqrt k))) := Finset.sum_le_sum hterm
    _ = (480 * Real.log t + 240 + smallHeightCount) *
          (∑ k ∈ Finset.Ico N K, (1 : ℝ) / (k : ℝ) ^ 2) +
        160 * (∑ k ∈ Finset.Ico N K, (1 : ℝ) / ((k : ℝ) * Real.sqrt k)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (480 * Real.log t + 240 + smallHeightCount) * (1 / ((N : ℝ) - 1)) +
        160 * (2 / Real.sqrt ((N : ℝ) - 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left (gaussian_sum_inv_sq_Ico hN) (by positivity))
        (mul_le_mul_of_nonneg_left (gaussian_sum_inv_sqrt_Ico hN) (by norm_num))
    _ = _ := by ring

private theorem gaussian_windowIndex_le_distance (t : ℝ) (q : XiZeroCopy) :
    (windowIndex t q : ℝ) ≤ ‖xiSpectralPoint q - (t : ℂ)‖ := by
  have hre : (xiSpectralPoint q - (t : ℂ)).re = (q.1 : ℂ).im - t := by
    simp [xiSpectralPoint]
  have h := Complex.abs_re_le_norm (xiSpectralPoint q - (t : ℂ))
  rw [hre, abs_sub_comm] at h
  exact (windowIndex_le t q).trans h

private theorem gaussian_tail_windowIndex {t R : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hRN : 2 * (N : ℝ) ≤ R) (q : XiZeroCopy)
    (hq : q ∉ xiSliceGaussianRadiusHead t R) : N ≤ windowIndex t q := by
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  apply Nat.le_floor
  by_contra h
  have habs : |t - (q.1 : ℂ).im| < N := lt_of_not_ge h
  have hi : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
    nlinarith only [xiSpectralPoint_im_sq_lt_quarter q,
      sq_abs (xiSpectralPoint q).im, abs_nonneg (xiSpectralPoint q).im]
  have hn := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q - (t : ℂ))
  have hre : (xiSpectralPoint q - (t : ℂ)).re = (q.1 : ℂ).im - t := by
    simp [xiSpectralPoint]
  rw [hre, abs_sub_comm] at hn
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hn
  apply hq
  rw [mem_xiSliceGaussianRadiusHead]
  linarith only [hn, hi, habs, hRN, hNreal]

private theorem gaussian_finite_far_mass {t R : ℝ} (ht : 4 ≤ t) {N : ℕ} (hN : 2 ≤ N)
    (hRN : 2 * (N : ℝ) ≤ R) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, q ∉ xiSliceGaussianRadiusHead t R) :
    ∑ q ∈ F, ‖xiSliceGaussianReciprocal t q‖ ≤
      (480 * Real.log t + 240 + smallHeightCount) / ((N : ℝ) - 1) +
        320 / Real.sqrt ((N : ℝ) - 1) := by
  classical
  let K := F.sup (windowIndex t) + 1
  have hmaps : ∀ q ∈ F, windowIndex t q ∈ Finset.Ico N K := by
    intro q hq
    exact Finset.mem_Ico.mpr ⟨gaussian_tail_windowIndex hN hRN q (hF q hq),
      Nat.lt_succ_of_le (Finset.le_sup (f := windowIndex t) hq)⟩
  have hterm : ∀ q ∈ F,
      ‖xiSliceGaussianReciprocal t q‖ ≤ 1 / (windowIndex t q : ℝ) ^ 2 := by
    intro q hq
    have hk : 2 ≤ windowIndex t q := hN.trans (Finset.mem_Ico.mp (hmaps q hq)).1
    have hk0 : (0 : ℝ) < windowIndex t q := by exact_mod_cast (by omega : 0 < windowIndex t q)
    rw [xiSliceGaussianReciprocal, norm_inv, norm_pow, ← one_div]
    apply one_div_le_one_div_of_le (sq_pos_of_pos hk0)
    exact pow_le_pow_left₀ hk0.le (gaussian_windowIndex_le_distance t q) 2
  have hfiber : ∀ k ∈ Finset.Ico N K,
      ∑ q ∈ F with windowIndex t q = k, 1 / (windowIndex t q : ℝ) ^ 2 ≤
        (80 * Real.log (180 * (t + k + 1)) + smallHeightCount) / (k : ℝ) ^ 2 := by
    intro k hk
    have heq : (∑ q ∈ F with windowIndex t q = k, 1 / (windowIndex t q : ℝ) ^ 2) =
        ∑ q ∈ F with windowIndex t q = k, 1 / (k : ℝ) ^ 2 :=
      Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.mp hq).2]
    rw [heq, Finset.sum_const, nsmul_eq_mul, mul_one_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply card_zeroWindow_le ht k
    intro q hq
    exact (Nat.floor_eq_iff (abs_nonneg _)).mp (Finset.mem_filter.mp hq).2
  calc
    _ ≤ ∑ q ∈ F, 1 / (windowIndex t q : ℝ) ^ 2 := Finset.sum_le_sum hterm
    _ = ∑ k ∈ Finset.Ico N K,
        ∑ q ∈ F with windowIndex t q = k, 1 / (windowIndex t q : ℝ) ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.Ico N K,
        (80 * Real.log (180 * (t + k + 1)) + smallHeightCount) / (k : ℝ) ^ 2 :=
      Finset.sum_le_sum hfiber
    _ ≤ _ := gaussian_sum_window_tail ht hN

/-- Actual zero-window counts give reciprocal mass decaying with the cutoff. -/
theorem xiSliceGaussianTailMass_le_window_bound {t R : ℝ} (ht : 4 ≤ t) {N : ℕ}
    (hN : 2 ≤ N) (hRN : 2 * (N : ℝ) ≤ R) :
    xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) ≤
      (480 * Real.log t + 240 + smallHeightCount) / ((N : ℝ) - 1) +
        320 / Real.sqrt ((N : ℝ) - 1) := by
  classical
  let H := xiSliceGaussianRadiusHead t R
  let e : {q : XiZeroCopy // q ∉ H} ↪ XiZeroCopy :=
    ⟨Subtype.val, Subtype.val_injective⟩
  apply (summable_norm_xiSliceGaussianTail t H).tsum_le_of_sum_le
  intro F
  have h := gaussian_finite_far_mass ht hN hRN (F.map e) (by
    intro q hq
    obtain ⟨q', _hq', rfl⟩ := Finset.mem_map.mp hq
    exact q'.property)
  rw [Finset.sum_map] at h
  change (∑ q ∈ F, ‖xiSliceGaussianReciprocal t q.val‖) ≤ _ at h
  exact h

/-- A continuous-cutoff estimate retaining both the height and the remote-window tail. -/
theorem xiSliceGaussianTailMass_le_cutoff_bound {t R : ℝ} (ht : 4 ≤ t) (hR : 8 ≤ R) :
    xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) ≤
      4 * (480 * Real.log t + 240 + smallHeightCount) / R + 640 / Real.sqrt R := by
  let N : ℕ := ⌊R / 2⌋₊
  have hN2 : 2 ≤ N := Nat.le_floor (by linarith only [hR])
  have hRN : 2 * (N : ℝ) ≤ R := by
    have h := Nat.floor_le (show 0 ≤ R / 2 by linarith only [hR])
    change (N : ℝ) ≤ R / 2 at h
    linarith only [h]
  have hfloor : R / 2 < (N : ℝ) + 1 := Nat.lt_floor_add_one (R / 2)
  have hlower : R / 4 ≤ (N : ℝ) - 1 := by linarith only [hfloor, hR]
  have hR0 : 0 < R := by linarith only [hR]
  have hN0 : 0 < (N : ℝ) - 1 := lt_of_lt_of_le (by positivity) hlower
  have hfirst :
      (480 * Real.log t + 240 + smallHeightCount) / ((N : ℝ) - 1) ≤
        4 * (480 * Real.log t + 240 + smallHeightCount) / R := by
    have hlog := Real.log_nonneg (show 1 ≤ t by linarith only [ht])
    calc
      _ ≤ (480 * Real.log t + 240 + smallHeightCount) / (R / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlower
      _ = _ := by ring
  have hsqrt : Real.sqrt R ≤ 2 * Real.sqrt ((N : ℝ) - 1) := by
    nlinarith only [Real.sq_sqrt hR0.le, Real.sq_sqrt hN0.le,
      Real.sqrt_nonneg R, Real.sqrt_nonneg ((N : ℝ) - 1), hlower]
  have hsecond : 320 / Real.sqrt ((N : ℝ) - 1) ≤ 640 / Real.sqrt R := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hN0) (Real.sqrt_pos.mpr hR0)).2
    linarith only [hsqrt]
  exact (xiSliceGaussianTailMass_le_window_bound ht hN2 hRN).trans
    (add_le_add hfirst hsecond)

end
end RHTower
