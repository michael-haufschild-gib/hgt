import GaloisForLFunctions.ArithmeticHarmonicAnalysis.SubWeylShortLogarithmicBlocks
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.CriticalLinePartialWeylBlocks
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.GaussianAFEWeightedBlocks

/-! # Sub-Weyl blocks for both exact Gaussian AFE series

Short blocks use the fifth-dual estimate. Above its interval, the exact
Gaussian weights supply `sqrt(t)/N`, making the classical Weyl bound smaller
than `t^(33/200)`. Reflection preserves the unweighted prefix norms.
-/

noncomputable section
open RHTower Complex

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- A critical-line prefix bound together with its actual Gaussian scale saving. -/
theorem exists_criticalPrefix_subWeyl_weighted_bound {t : ℝ} (ht : 1024 * Real.pi ≤ t)
    {N : ℕ} (hN : 1 ≤ N) (hup : (N : ℝ) ≤ 10 * t ^ (7 / 3 : ℝ)) :
    ∃ P : ℝ, 0 ≤ P ∧
      (∀ M : ℕ, N ≤ M → M ≤ 2 * N →
        ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - I * (t : ℂ))‖ ≤ P) ∧
      P * min 1 (Real.sqrt t / (N : ℝ)) ≤ 10 ^ 13 * t ^ (33 / 200 : ℝ) := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have ht1 : 1 ≤ t := by linarith only [ht, hpi]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmu0 : 0 ≤ t ^ (33 / 200 : ℝ) := by positivity
  by_cases hshort : 200 * Real.log (N : ℝ) ≤ 101 * Real.log (t / (2 * Real.pi))
  · refine ⟨10 ^ 13 * t ^ (33 / 200 : ℝ), by positivity,
      fun M hNM hM => norm_criticalBlock_le_subWeyl_short_all ht hN hNM hM hshort, ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (min_le_left (1 : ℝ) (Real.sqrt t / (N : ℝ))) (by positivity : 0 ≤ 10 ^ 13 * t ^ (33 / 200 : ℝ))
  obtain ⟨T, hT⟩ : ∃ T, T = t / (2 * Real.pi) := ⟨_, rfl⟩
  have hT512 : 512 ≤ T := by
    rw [hT, le_div_iff₀ (by positivity)]
    linarith only [ht]
  have hT0 : 0 < T := by linarith only [hT512]
  have hshort' : 101 * Real.log T < 200 * Real.log (N : ℝ) := by
    rw [hT]
    exact lt_of_not_ge hshort
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogT : 9 * Real.log 2 ≤ Real.log T := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 512) hT512
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have ht8 : t ≤ 8 * T := by
    rw [hT, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    have hc : 2 * Real.pi ≤ (8 : ℝ) := by linarith only [hpi4]
    nlinarith only [mul_le_mul_of_nonneg_right hc ht0.le]
  have hlogtT : Real.log t ≤ Real.log 8 + Real.log T := by
    have h := Real.log_le_log ht0 ht8
    rw [Real.log_mul (by norm_num) hT0.ne'] at h
    exact h
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hN3 : t ≤ (N : ℝ) ^ 3 := by
    refine le_of_log_le_log ht0 (by positivity) ?_
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [hlog8] at hlogtT
    linarith only [hshort', hlogtT, hlogT, hlog2]
  refine ⟨1024 * t ^ (1 / 6 : ℝ), by positivity,
    fun M hNM hM => norm_criticalPartial_le_weyl ht1 hN hNM hM hN3 hup, ?_⟩
  have hrate : t ^ (1 / 6 : ℝ) * (Real.sqrt t / (N : ℝ)) ≤ 8 * t ^ (33 / 200 : ℝ) := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.sqrt_eq_rpow, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow ht0, Real.log_div (by positivity) hN0.ne', Real.log_rpow ht0,
      Real.log_mul (by norm_num) (by positivity), Real.log_rpow ht0]
    have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hl8 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
    linarith only [hshort', hlogtT, hlt, hl8]
  have hmin := mul_le_mul_of_nonneg_left
    (min_le_right (1 : ℝ) (Real.sqrt t / (N : ℝ)))
    (by positivity : 0 ≤ 1024 * t ^ (1 / 6 : ℝ))
  nlinarith only [hmin, hrate, hmu0]

/-- Reflection on the critical line preserves every finite Dirichlet prefix norm. -/
theorem norm_reflectedCritical_sum_eq (t : ℝ) (N M : ℕ) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (linePt t - 1)‖ =
      ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - I * (t : ℂ))‖ := by
  have he : linePt t - 1 = (starRingEnd ℂ) (-((1 / 2 : ℝ) : ℂ) - I * (t : ℂ)) := by
    apply Complex.ext <;> norm_num [linePt]
  rw [he]
  have hs : (∑ n ∈ Finset.Ico N M,
      (n : ℂ) ^ ((starRingEnd ℂ) (-((1 / 2 : ℝ) : ℂ) - I * (t : ℂ)))) =
      (starRingEnd ℂ) (∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - I * (t : ℂ))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [natCast_cpow_conj]
  rw [hs, Complex.norm_conj]

/-- Both actual Gaussian AFE blocks have exponent `33/200`, throughout the finite truncation range. -/
theorem exists_norm_gaussianAFE_blocks_le_subWeyl :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1024 * Real.pi ≤ t → ∀ N M : ℕ,
      1 ≤ N → N ≤ M → M ≤ 2 * N → (N : ℝ) ≤ 10 * t ^ (7 / 3 : ℝ) →
      ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-linePt t) *
        smoothAFECutoff ((n : ℝ) / Real.sqrt t)‖ ≤ C * t ^ (33 / 200 : ℝ) ∧
      ‖∑ n ∈ Finset.Ico N M, (zetaChi (linePt t) * (n : ℂ) ^ (linePt t - 1)) *
        smoothAFEZetaDualWeight t ((n : ℝ) * Real.sqrt t)‖ ≤ C * t ^ (33 / 200 : ℝ) := by
  obtain ⟨A, hA, hdir⟩ := exists_norm_sum_directWeight_mul_le
  obtain ⟨B, hB, hdual⟩ := exists_norm_sum_dualWeight_mul_le
  refine ⟨10 ^ 13 * (A + B), by positivity, fun t ht N M hN hNM hM hup => ?_⟩
  have hpi := Real.pi_gt_three
  have ht1 : 1 ≤ t := by linarith only [ht, hpi]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hx : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨P, -, hP, hrate⟩ := exists_criticalPrefix_subWeyl_weighted_bound ht hN hup
  have hd := hdir (Real.sqrt t) hx N M hN hNM (fun n => (n : ℂ) ^ (-linePt t)) P (by
    intro m hm1 hm2
    have he : -linePt t = -((1 / 2 : ℝ) : ℂ) - I * (t : ℂ) := by
      apply Complex.ext <;> simp [linePt]
    rw [he]
    exact hP m hm1 (hm2.trans hM))
  have hr := hdual t (Real.sqrt t) ht1 hx N M hN hNM hM
    (fun n => zetaChi (linePt t) * (n : ℂ) ^ (linePt t - 1)) P (by
      intro m hm1 hm2
      rw [← Finset.mul_sum, norm_mul, zetaChi_norm_on_line (by simp [linePt]), one_mul,
        norm_reflectedCritical_sum_eq]
      exact hP m hm1 (hm2.trans hM))
  have hquot : t / ((N : ℝ) * Real.sqrt t) = Real.sqrt t / (N : ℝ) := by
    have hs := Real.sq_sqrt ht0.le
    field_simp [hN0.ne', hx.ne']
    nlinarith only [hs]
  rw [hquot] at hr
  have hArate := mul_le_mul_of_nonneg_left hrate hA
  have hBrate := mul_le_mul_of_nonneg_left hrate hB
  have hmu : 0 ≤ t ^ (33 / 200 : ℝ) := by positivity
  have hextraA := mul_nonneg hA hmu
  have hextraB := mul_nonneg hB hmu
  constructor
  · nlinarith only [hd, hArate, hextraB]
  · nlinarith only [hr, hBrate, hextraA]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_norm_gaussianAFE_blocks_le_subWeyl
