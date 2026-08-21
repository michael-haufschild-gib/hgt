import GaloisForLFunctions.RHTower.Sieve.HuxleyExplicitLargeValues

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

theorem scratch_huxley_large_values_finset_explicit_energy
    {N : ℕ} (hN : 1 ≤ N) (a : EuclideanSpace ℂ (Fin N))
    {delta Ttot V G : ℝ} (hdelta : 0 < delta) (hV : 0 < V) (hTtot : 0 ≤ Ttot)
    (hmass : ‖a‖ ^ 2 ≤ G) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ Ttot)
    (hbig : ∀ x ∈ S, V ≤ ‖⟪dyadicDirRow N x, a⟫_ℂ‖)
    (hthresh : G * (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi))) ≤ V ^ 2 / 3) :
    (S.card : ℝ) * V ^ 2 ≤
      (Ttot * (1284 * G) ^ 2 / V ^ 4 + 1) *
        (2 * G * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) *
          (1 + Real.log (Ttot / delta + 1)))) := by
  have hbase := huxley_large_values_finset hN a hdelta hV hTtot hmass S
    hsep hspread hbig hthresh
  refine le_trans hbase ?_
  have hG : 0 ≤ G := le_trans (by positivity) hmass
  have hcnt := card_le_of_pairwise_spread hdelta hTtot S hsep hspread
  have hone : (1 : ℝ) ≤ Ttot / delta + 1 := by
    have : (0 : ℝ) ≤ Ttot / delta := div_nonneg hTtot hdelta.le
    linarith
  have hlog : Real.log (S.card : ℝ) ≤ Real.log (Ttot / delta + 1) := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hp
    · rw [h0]
      simpa using Real.log_nonneg hone
    · exact Real.log_le_log (by exact_mod_cast hp) hcnt
  have hharm : ∑ i ∈ Finset.range S.card, 1 / ((i : ℝ) + 1) ≤
      1 + Real.log (Ttot / delta + 1) := by
    calc
      ∑ i ∈ Finset.range S.card, 1 / ((i : ℝ) + 1)
          = ∑ i ∈ Finset.Icc 1 S.card, 1 / (i : ℝ) := by
            rw [sum_Icc_one_div_eq_sum_range]
      _ ≤ 1 + Real.log (S.card : ℝ) := sum_Icc_one_div_le_one_add_log S.card
      _ ≤ 1 + Real.log (Ttot / delta + 1) := by linarith
  have hcoef : 0 ≤ 12 * Real.pi * (N : ℝ) / delta := by positivity
  have hinner :
      (N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) *
          ∑ i ∈ Finset.range S.card, 1 / ((i : ℝ) + 1) ≤
        (N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) *
          (1 + Real.log (Ttot / delta + 1)) := by
    gcongr
  have hfac : 0 ≤ Ttot * (1284 * G) ^ 2 / V ^ 4 + 1 := by positivity
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hinner (mul_nonneg (by norm_num) hG)) hfac

end RHTower.Sieve
