import GaloisForLFunctions.RHTower.ZetaCriticalLineWeylBound

/-! # Weyl bounds for every critical-line partial block

The sharp third-derivative, second-derivative and first-derivative regimes
hold uniformly for all prefixes of a dyadic block. This uniformity permits
insertion of the exact Gaussian AFE weights by finite Abel summation.
-/

noncomputable section
open Complex RHTower RHTower.Sieve

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem norm_criticalPartial_le_kuzminLandau {t : ℝ} (ht : 0 < t) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N) (htN : 3 * t ≤ 4 * Real.pi * N) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖ ≤
      (6 * Real.pi * N / t + 1) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  refine dirichlet_block_sigma_bound (by norm_num) t N M hN hNM _ ?_
  intro m hm1 hm2
  have hP : 0 ≤ 6 * Real.pi * N / t + 1 := by positivity
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
  · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]
    exact hP
  · rw [Finset.sum_Ico_eq_sum_range]
    have h := norm_logPhase_dyadic_prefix_le_kuzminLandau t ht N (m - N) hN (by omega)
      (by omega) htN
    refine le_of_eq_of_le ?_ h
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [natCast_cpow_neg_I_mul t (N + j) (by omega)]
    push_cast
    ring_nf

private theorem norm_criticalPartial_le_second {t : ℝ} (ht : 0 < t) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖ ≤
      256 * ((N : ℝ) * (16 * (t / (8 * Real.pi * (N : ℝ) ^ 2))) ^ (1 / 2 : ℝ) +
        (t / (8 * Real.pi * (N : ℝ) ^ 2)) ^ (-(1 / 2 : ℝ))) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlamEq : t / (2 * Real.pi) * (Nat.factorial (2 - 1) : ℝ) / (2 * (N : ℝ)) ^ 2 =
      t / (8 * Real.pi * (N : ℝ) ^ 2) := by
    norm_num
    field_simp
    ring
  have hlam1 : t / (2 * Real.pi) * (Nat.factorial (2 - 1) : ℝ) / (2 * (N : ℝ)) ^ 2 ≤ 1 := by
    rw [hlamEq, div_le_one (by positivity)]
    exact hlam
  have hp := phase_prefix_bound t ht 2 N (2 * N) le_rfl hN (by omega) (by omega) hlam1
  rw [hlamEq, show 2 * N - N = N by omega] at hp
  norm_num at hp
  refine dirichlet_block_sigma_bound (by norm_num) t N M hN hNM _ ?_
  intro m hm1 hm2
  exact hp m hm1 (by omega)

private theorem norm_criticalPartial_le_third {t : ℝ} (ht : 0 < t) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖ ≤
      (128 * N * (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ) +
        128 * Real.sqrt N / (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ)) *
        (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hlam1 : t / (8 * Real.pi * (N : ℝ) ^ 3) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hlam
  refine dirichlet_block_sigma_bound (by norm_num) t N M hN hNM _ ?_
  intro m hm1 hm2
  have hP : 0 ≤ 128 * N * (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ) +
      128 * Real.sqrt N / (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ) := by positivity
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
  · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]
    exact hP
  · rw [Finset.sum_Ico_eq_sum_range]
    have h := dirichlet_block_bound_third_sharp ht (L := m - N) hN (by omega) (by omega) hlam1
    refine h.trans ?_
    have hmN : ((m - N : ℕ) : ℝ) ≤ N := by exact_mod_cast (show m - N ≤ N by omega)
    gcongr

/-- Weyl's `1/6` estimate holds for every partial dyadic block in the truncation range. -/
theorem norm_criticalPartial_le_weyl {t : ℝ} (ht : 1 ≤ t) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hNlow : t ≤ (N : ℝ) ^ 3) (hNup : (N : ℝ) ≤ 10 * t ^ (7 / 3 : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖ ≤
      1024 * t ^ (1 / 6 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hp := Real.pi_gt_three
  have hpow0 : 0 ≤ t ^ (1 / 6 : ℝ) := by positivity
  by_cases hkl : 3 * t ≤ 4 * Real.pi * N
  · exact (norm_criticalPartial_le_kuzminLandau ht0 hN hNM hM hkl).trans
      ((halfBlock_kl_num_sixth ht hN1 hNup).trans (by linarith only [hpow0]))
  have hkl' : 4 * Real.pi * N < 3 * t := lt_of_not_ge hkl
  by_cases h23 : t ^ (2 / 3 : ℝ) ≤ N
  · have hsq : t ^ (4 / 3 : ℝ) ≤ (N : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) h23 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le] at h
      norm_num at h
      exact h
    have h43 : t ≤ t ^ (4 / 3 : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (1 : ℝ) ≤ 4 / 3)
    have hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 2 := by
      have hc : (1 : ℝ) ≤ 8 * Real.pi := by linarith only [hp]
      have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ))
      linarith only [hsq, h43, hm]
    exact (norm_criticalPartial_le_second ht0 hN hNM hM hlam).trans
      (halfBlock_second_num_sixth ht hN1 h23 hkl')
  · have h23' : (N : ℝ) < t ^ (2 / 3 : ℝ) := lt_of_not_ge h23
    have hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 3 := by
      have hc : (1 : ℝ) ≤ 8 * Real.pi := by linarith only [hp]
      have hm := mul_le_mul_of_nonneg_right hc (pow_nonneg hN0.le 3)
      linarith only [hNlow, hm]
    exact (norm_criticalPartial_le_third ht0 hN hNM hM hlam).trans
      ((halfBlock_third_sharp_num ht hN1 h23').trans (by linarith only [hpow0]))

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_criticalPartial_le_weyl
