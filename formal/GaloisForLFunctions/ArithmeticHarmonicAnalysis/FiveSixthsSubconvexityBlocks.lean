import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiveSixthsSubconvexityPowers
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.CriticalLinePartialWeylBlocks
import GaloisForLFunctions.RHTower.ZetaFiveSeventhsLineBound

/-! # The `2/53` bound on `5/6`-line Dirichlet blocks

The fifth and fourth derivative estimates meet at `N=t^(15/53)`.
Above square-root length, an additional decreasing `n^(-1/3)` weight
transfers the critical-line Weyl bound to the `5/6` line.
-/

noncomputable section
open RHTower RHTower.Sieve Complex

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem fiveSixths_cancel_weight {t n : ℝ} (hn : 0 < n) :
    (10 ^ 6 * n ^ (5 / 6 : ℝ) * t ^ (2 / 53 : ℝ)) * n ^ (-(5 / 6 : ℝ)) =
      10 ^ 6 * t ^ (2 / 53 : ℝ) := by
  have he : n ^ (5 / 6 : ℝ) * n ^ (-(5 / 6 : ℝ)) = 1 := by
    rw [← Real.rpow_add hn]
    norm_num
  calc _ = (10 ^ 6 * t ^ (2 / 53 : ℝ)) * (n ^ (5 / 6 : ℝ) * n ^ (-(5 / 6 : ℝ))) := by ring
    _ = _ := by rw [he, mul_one]

/-- Fifth derivatives control the first oscillatory interval on the `5/6` line. -/
theorem norm_fiveSixthsBlock_le_fifth {t : ℝ} (ht : 1 ≤ t) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hlo : 12 * Real.log t ≤ 53 * Real.log (N : ℝ))
    (hhi : 53 * Real.log (N : ℝ) ≤ 15 * Real.log t) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((5 / 6 : ℝ) : ℂ) - I * (t : ℂ))‖ ≤
      10 ^ 6 * t ^ (2 / 53 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hlam1, hnum⟩ := fiveSixths_fifth_numeric ht hN0 hlo hhi
  have hlamEq : t / (2 * Real.pi) * (Nat.factorial (5 - 1) : ℝ) / (2 * (N : ℝ)) ^ 5 =
      3 * t / (8 * Real.pi * (N : ℝ) ^ 5) := by
    norm_num
    field_simp
    ring
  have hp := phase_prefix_bound t ht0 5 N (2 * N) (by norm_num) hN (by omega) (by omega)
    (by rw [hlamEq]; exact hlam1)
  rw [hlamEq, show 2 * N - N = N by omega] at hp
  norm_num at hp
  have hb := dirichlet_block_sigma_bound (σ := 5 / 6) (by norm_num) t N M hN hNM
    (10 ^ 6 * (N : ℝ) ^ (5 / 6 : ℝ) * t ^ (2 / 53 : ℝ)) (by
      intro m hm1 hm2
      exact (hp m hm1 (by omega)).trans hnum)
  rw [fiveSixths_cancel_weight hN0] at hb
  exact hb

/-- The sharp fourth derivative continues the `2/53` bound up to square-root length. -/
theorem norm_fiveSixthsBlock_le_fourth {t : ℝ} (ht : 1 ≤ t) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hlo : 15 * Real.log t ≤ 53 * Real.log (N : ℝ))
    (hhi : 2 * Real.log (N : ℝ) ≤ Real.log t) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((5 / 6 : ℝ) : ℂ) - I * (t : ℂ))‖ ≤
      10 ^ 6 * t ^ (2 / 53 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hlam1, hnum⟩ := fiveSixths_fourth_numeric ht hN0 hlo hhi
  have hb := dirichlet_block_sigma_bound (σ := 5 / 6) (by norm_num) t N M hN hNM
    (10 ^ 6 * (N : ℝ) ^ (5 / 6 : ℝ) * t ^ (2 / 53 : ℝ)) (by
      intro m hm1 hm2
      rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
      · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]
        positivity
      · rw [Finset.sum_Ico_eq_sum_range]
        have hp := dirichlet_block_bound_fourth_sharp ht0 (L := m - N) hN (by omega) (by omega) hlam1
        refine hp.trans (le_trans ?_ hnum)
        have hmN : ((m - N : ℕ) : ℝ) ≤ N := by exact_mod_cast (show m - N ≤ N by omega)
        gcongr)
  rw [fiveSixths_cancel_weight hN0] at hb
  exact hb

/-- Above square-root length, the extra real weight makes the Weyl bound constant. -/
theorem norm_fiveSixthsBlock_le_weyl {t : ℝ} (ht : 1 ≤ t) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hlo : Real.log t ≤ 2 * Real.log (N : ℝ))
    (hup : (N : ℝ) ≤ 10 * t ^ (7 / 3 : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((5 / 6 : ℝ) : ℂ) - I * (t : ℂ))‖ ≤ 1024 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hlN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hN3 : t ≤ (N : ℝ) ^ 3 := by
    refine le_of_log_le_log ht0 (by positivity) ?_
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlo, hlN]
  let a : ℕ → ℂ := fun n => (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - I * (t : ℂ))
  let w : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / 3 : ℝ))
  have hterm : ∀ n ∈ Finset.Ico N M,
      (n : ℂ) ^ (-((5 / 6 : ℝ) : ℂ) - I * (t : ℂ)) = (w n : ℂ) * a n := by
    intro n hn
    have hn1 : 1 ≤ n := hN.trans (Finset.mem_Ico.mp hn).1
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    dsimp only [w, a]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
    rw [← Complex.cpow_add _ _ hn0]
    congr 1
    push_cast
    ring
  have hanti : ∀ n, N ≤ n → n < M → w (n + 1) ≤ w n := by
    intro n hn _
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact Real.rpow_le_rpow_of_nonpos hn0 (by push_cast; linarith) (by norm_num)
  have hab := abel_block_bound a w N M hNM (by dsimp only [w]; positivity) hanti
    (1024 * t ^ (1 / 6 : ℝ)) (by
      intro m hm1 hm2
      exact norm_criticalPartial_le_weyl ht hN hm1 (by omega) hN3 hup)
  rw [Finset.sum_congr rfl hterm]
  refine hab.trans ?_
  have hpower : t ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := by
    refine le_of_log_le_log (by positivity) zero_lt_one ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow ht0, Real.log_rpow hN0,
      Real.log_one]
    linarith only [hlo]
  dsimp only [w]
  nlinarith only [hpower]

/-- Every dyadic block above the trivial head has exponent `2/53` on `Re s=5/6`. -/
theorem norm_fiveSixthsBlock_le {t : ℝ} (ht : 1 ≤ t) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hlo : 12 * Real.log t ≤ 53 * Real.log (N : ℝ))
    (hup : (N : ℝ) ≤ 10 * t ^ (7 / 3 : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((5 / 6 : ℝ) : ℂ) - I * (t : ℂ))‖ ≤
      10 ^ 6 * t ^ (2 / 53 : ℝ) := by
  by_cases h5 : 53 * Real.log (N : ℝ) ≤ 15 * Real.log t
  · exact norm_fiveSixthsBlock_le_fifth ht hN hNM hM hlo h5
  have h5' : 15 * Real.log t ≤ 53 * Real.log (N : ℝ) := (lt_of_not_ge h5).le
  by_cases h4 : 2 * Real.log (N : ℝ) ≤ Real.log t
  · exact norm_fiveSixthsBlock_le_fourth ht hN hNM hM h5' h4
  have hb := norm_fiveSixthsBlock_le_weyl ht hN hNM hM (lt_of_not_ge h4).le hup
  have hp : 1 ≤ t ^ (2 / 53 : ℝ) := Real.one_le_rpow ht (by norm_num)
  linarith only [hb, hp]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_fiveSixthsBlock_le
