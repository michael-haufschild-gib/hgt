import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FifthLogarithmicSubWeylRange
import GaloisForLFunctions.RHTower.ZetaFiveSeventhsLineBound

/-! # Sub-Weyl bounds for short logarithmic blocks

Four overlapping intervals cover every block up to `T^(101/200)`: the
trivial estimate, the sharp fourth-derivative test, the fourth dual test,
and the fifth dual test. All estimates hold for every partial block.
-/

noncomputable section
open RHTower Complex

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The direct fourth-derivative estimate fills the interval between the
trivial bound and the fourth-dual differencing bound. -/
theorem fourthRange_numeric {t n : ℝ} (ht : 1 ≤ t) (hn : 0 < n)
    (hlo : 66 * Real.log t ≤ 200 * Real.log n)
    (hhi : 5 * Real.log n ≤ 2 * Real.log t) :
    3 * t / (16 * Real.pi * n ^ 4) ≤ 1 ∧
      224 * (n * (3 * t / (16 * Real.pi * n ^ 4)) ^ (1 / 14 : ℝ) +
        n ^ (3 / 4 : ℝ) * (3 * t / (16 * Real.pi * n ^ 4)) ^ (-(1 / 14 : ℝ)))
        ≤ 10000 * n ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  obtain ⟨lam, hlam⟩ : ∃ l, l = 3 * t / (16 * Real.pi * n ^ 4) := ⟨_, rfl⟩
  rw [← hlam]
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hupper : lam ≤ t / n ^ 4 := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : (3 : ℝ) ≤ 16 * Real.pi := by linarith only [hpi]
    nlinarith only [mul_le_mul_of_nonneg_right hc (mul_nonneg ht0.le (pow_nonneg hn.le 4))]
  have hlower : t / (32 * n ^ 4) ≤ lam := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : 16 * Real.pi ≤ (96 : ℝ) := by linarith only [hpi4]
    nlinarith only [mul_le_mul_of_nonneg_right hc (mul_nonneg ht0.le (pow_nonneg hn.le 4))]
  have hlogUpper : Real.log lam ≤ Real.log t - 4 * Real.log n := by
    have h := Real.log_le_log hlam0 hupper
    rw [Real.log_div ht0.ne' (by positivity), Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hlogLower : Real.log t - Real.log 32 - 4 * Real.log n ≤ Real.log lam := by
    have h := Real.log_le_log (by positivity : 0 < t / (32 * n ^ 4)) hlower
    rw [Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h]
  have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hlam1 : lam ≤ 1 := by
    refine le_of_log_le_log hlam0 zero_lt_one ?_
    rw [Real.log_one]
    linarith only [hlogUpper, hlo, hlt]
  obtain ⟨Q, hQ⟩ : ∃ q, q = n ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hlogQ : Real.log Q = 1 / 2 * Real.log n + 33 / 200 * Real.log t := by
    rw [hQ, Real.log_mul (by positivity) (by positivity), Real.log_rpow hn, Real.log_rpow ht0]
  have hA : n * lam ^ (1 / 14 : ℝ) ≤ Q := by
    refine le_of_log_le_log (by positivity) hQ0 ?_
    rw [Real.log_mul hn.ne' (by positivity), Real.log_rpow hlam0, hlogQ]
    linarith only [hlogUpper, hhi, hlt]
  have hB : n ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)) ≤ 32 * Q := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hn, Real.log_rpow hlam0,
      Real.log_mul (by norm_num) hQ0.ne', hlogQ]
    linarith only [hlogLower, hhi, hlt, hlog32]
  refine ⟨hlam1, ?_⟩
  rw [show 10000 * n ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ) = 10000 * Q by rw [hQ]; ring]
  linarith only [hA, hB, hQ0]

/-- Uniform prefixes in the direct fourth-derivative interval. -/
theorem norm_prefix_le_fourthRange {t : ℝ} (ht : 1 ≤ t) {N L : ℕ}
    (hN : 1 ≤ N) (hL : L ≤ N)
    (hlo : 66 * Real.log t ≤ 200 * Real.log (N : ℝ))
    (hhi : 5 * Real.log (N : ℝ) ≤ 2 * Real.log t) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 10000 * (N : ℝ) ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hlam1, hnum⟩ := fourthRange_numeric ht hN0 hlo hhi
  rcases Nat.eq_zero_or_pos L with rfl | hL0
  · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have hp := dirichlet_block_bound_fourth_sharp ht0 hN hL0 (by omega) hlam1
  refine hp.trans (le_trans ?_ hnum)
  have hLN : (L : ℝ) ≤ N := by exact_mod_cast hL
  gcongr

/-- Every logarithmic phase has unit modulus, so a prefix is bounded by its length. -/
theorem norm_logarithmic_prefix_le_length (t : ℝ) {N L : ℕ} (hN : 1 ≤ N) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ L := by
  have hterm : ∀ j : ℕ, ‖((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
    intro j
    rw [RHTower.Sieve.natCast_cpow_neg_I_mul t (N + j) (by omega)]
    exact Complex.norm_exp_ofReal_mul_I _
  calc _ ≤ ∑ j ∈ Finset.range L,
        ‖((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ := norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range L, (1 : ℝ) := Finset.sum_congr rfl fun j _ => hterm j
    _ = L := by simp

/-- Every prefix in a block below `T^(101/200)` has the strict sub-Weyl exponent `33/200`. -/
theorem norm_prefix_le_subWeyl_short {t : ℝ} (ht : 1024 * Real.pi ≤ t) {N L : ℕ}
    (hN : 3 ≤ N) (hL : L ≤ N)
    (hup : 200 * Real.log (N : ℝ) ≤ 101 * Real.log (t / (2 * Real.pi))) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 10 ^ 13 * (N : ℝ) ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ) := by
  have hpi := Real.pi_gt_three
  have ht1 : 1 ≤ t := by linarith only [ht, hpi]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
  obtain ⟨T, hT⟩ : ∃ T, T = t / (2 * Real.pi) := ⟨_, rfl⟩
  have hT512 : 512 ≤ T := by
    rw [hT, le_div_iff₀ (by positivity)]
    linarith only [ht]
  have hT0 : 0 < T := by linarith only [hT512]
  have hTt : T ≤ t := by
    rw [hT, div_le_iff₀ (by positivity)]
    have hc : (1 : ℝ) ≤ 2 * Real.pi := by linarith only [hpi]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc ht0.le
  have hlogT : Real.log T ≤ Real.log t := Real.log_le_log hT0 hTt
  obtain ⟨Q, hQ⟩ : ∃ q, q = (N : ℝ) ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hlogQ : Real.log Q = 1 / 2 * Real.log (N : ℝ) + 33 / 200 * Real.log t := by
    rw [hQ, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0, Real.log_rpow ht0]
  rw [show 10 ^ 13 * (N : ℝ) ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ) = 10 ^ 13 * Q by
    rw [hQ]; ring]
  by_cases hsmall : 200 * Real.log (N : ℝ) ≤ 66 * Real.log t
  · have hNQ : (N : ℝ) ≤ Q := by
      refine le_of_log_le_log hN0 hQ0 ?_
      rw [hlogQ]
      linarith only [hsmall]
    have hlen := norm_logarithmic_prefix_le_length (L := L) t (by omega : 1 ≤ N)
    have hLN : (L : ℝ) ≤ N := by exact_mod_cast hL
    linarith only [hlen, hLN, hNQ, hQ0]
  have hlo : 66 * Real.log t ≤ 200 * Real.log (N : ℝ) := (lt_of_not_ge hsmall).le
  by_cases hfour : 5 * Real.log (N : ℝ) ≤ 2 * Real.log t
  · have hb := norm_prefix_le_fourthRange ht1 (by omega : 1 ≤ N) hL hlo hfour
    rw [show 10000 * (N : ℝ) ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ) = 10000 * Q by
      rw [hQ]; ring] at hb
    linarith only [hb, hQ0]
  have hfour' : 2 * Real.log t < 5 * Real.log (N : ℝ) := lt_of_not_ge hfour
  by_cases hdual : 200 * Real.log (N : ℝ) ≤ 97 * Real.log T
  · have h5 : t ^ 5 ≤ (N : ℝ) ^ 13 := by
      refine le_of_log_le_log (by positivity) (by positivity) ?_
      rw [Real.log_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [hfour', hlt]
    have h2 : (N : ℝ) ^ 2 ≤ t := by
      refine le_of_log_le_log (by positivity) ht0 ?_
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [hdual, hlogT, hlt]
    have hb := norm_prefix_le_BRange ht h5 h2 hL
    have hpower : (N : ℝ) ^ (11 / 18 : ℝ) * t ^ (1 / 9 : ℝ) ≤ Q := by
      refine le_of_log_le_log (by positivity) hQ0 ?_
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0,
        Real.log_rpow ht0, hlogQ]
      linarith only [hdual, hlogT]
    have hm := mul_le_mul_of_nonneg_left hpower (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
    linarith only [hb, hm, hQ0]
  · have hb := norm_prefix_le_fifthRange (t := t) (by rw [← hT]; exact hT512) hN hL
      (by rw [← hT]; exact (lt_of_not_ge hdual).le) hup
    have hpow := Real.rpow_le_rpow hT0.le hTt (by norm_num : (0 : ℝ) ≤ 33 / 200)
    have hm := mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ 10 ^ 13 * (N : ℝ) ^ (1 / 2 : ℝ))
    have hTeq : t / (2 * Real.pi) = T := hT.symm
    rw [hTeq] at hb
    calc _ ≤ 10 ^ 13 * (N : ℝ) ^ (1 / 2 : ℝ) * T ^ (33 / 200 : ℝ) := hb
      _ ≤ 10 ^ 13 * (N : ℝ) ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ) := hm
      _ = _ := by rw [hQ]; ring

/-- The same exponent bounds every critical-line partial block. -/
theorem norm_criticalBlock_le_subWeyl_short {t : ℝ} (ht : 1024 * Real.pi ≤ t) {N M : ℕ}
    (hN : 3 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hup : 200 * Real.log (N : ℝ) ≤ 101 * Real.log (t / (2 * Real.pi))) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 10 ^ 13 * t ^ (33 / 200 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := RHTower.Sieve.dirichlet_block_sigma_bound (σ := 1 / 2) (by norm_num) t N M
    (by omega) hNM (10 ^ 13 * (N : ℝ) ^ (1 / 2 : ℝ) * t ^ (33 / 200 : ℝ)) (by
      intro m hm hmM
      rw [Finset.sum_Ico_eq_sum_range]
      exact norm_prefix_le_subWeyl_short ht hN (by omega) hup)
  refine hp.trans (le_of_eq ?_)
  have he : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hN0]
    norm_num
  calc _ = (10 ^ 13 * t ^ (33 / 200 : ℝ)) *
        ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
    _ = _ := by rw [he, mul_one]

/-- The two initial blocks satisfy the same bound by absolute values. -/
theorem norm_criticalBlock_le_subWeyl_short_all {t : ℝ} (ht : 1024 * Real.pi ≤ t) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hup : 200 * Real.log (N : ℝ) ≤ 101 * Real.log (t / (2 * Real.pi))) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖ ≤
      10 ^ 13 * t ^ (33 / 200 : ℝ) := by
  by_cases hN3 : 3 ≤ N
  · exact norm_criticalBlock_le_subWeyl_short ht hN3 hNM hM hup
  have hN2 : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb := RHTower.Sieve.dirichlet_block_sigma_bound (σ := 1 / 2) (by norm_num) t N M hN hNM
    (N : ℝ) (by
      intro m hm1 hm2
      rw [Finset.sum_Ico_eq_sum_range]
      exact (norm_logarithmic_prefix_le_length t hN).trans
        (by exact_mod_cast (show m - N ≤ N by omega)))
  have hw : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hpi := Real.pi_gt_three
  have ht1 : 1 ≤ t := by linarith only [ht, hpi]
  have hp : 1 ≤ t ^ (33 / 200 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  nlinarith only [hb, hm, hN2, hp]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_prefix_le_fourthRange

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_criticalBlock_le_subWeyl_short

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_criticalBlock_le_subWeyl_short_all
