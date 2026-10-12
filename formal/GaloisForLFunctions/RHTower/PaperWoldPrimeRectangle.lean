import GaloisForLFunctions.RHTower.PaperWoldPrimeWindows

/-! # A literal prime-rectangle lower bound

The native Wold prime coefficient dominates its logarithmic cell at large
scales. No prime term, cell subtraction, or matrix weight is discarded.
-/

namespace RHTower
noncomputable section
open Filter Topology

private theorem prime_increment_window_lower (N n : ℕ) (hN : 2 ≤ N)
    (hlog : 64 ≤ Real.log N) (hp : (n + 2).Prime)
    (hlo : N < n + 2) (hhi : n + 2 ≤ 4 * N) :
    Real.log N / (64 * (N : ℝ)) ≤ xiHeatCassiniWoldNatIncrement n := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpp : (0 : ℝ) < n + 2 := by positivity
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hloR : (N : ℝ) ≤ n + 1 := by exact_mod_cast (show N ≤ n + 1 by omega)
  have hhiR : (n : ℝ) + 2 ≤ 4 * N := by exact_mod_cast hhi
  have hlogmono : Real.log N ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hNp (by linarith)
  have hw := (woldCoeff_one_le_harmonic_le_eight_mul_woldCoeff_one ⟨n + 2, hp⟩).2
  change Real.log ((n + 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) ≤
    8 * woldCoeff 1 ⟨n + 2, hp⟩ at hw
  push_cast at hw
  have hbase : Real.log N / (4 * (N : ℝ)) ≤ 8 * woldCoeff 1 ⟨n + 2, hp⟩ := by
    apply le_trans _ hw
    exact (div_le_div_of_nonneg_left hlog0 hpp hhiR).trans
      (div_le_div_of_nonneg_right hlogmono hpp.le)
  have he : Real.log N / (4 * (N : ℝ)) = 8 * (Real.log N / (32 * (N : ℝ))) := by
    field_simp
    ring
  rw [he] at hbase
  have hwlo : Real.log N / (32 * (N : ℝ)) ≤ woldCoeff 1 ⟨n + 2, hp⟩ := by linarith
  have hg : Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) ≤ 1 / (N : ℝ) := by
    apply le_trans _ (one_div_le_one_div_of_le hNp hloR)
    simpa only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] using
      log_succ_sub_log_le (j := n + 1) (by omega)
  have hpaid : Real.log N / (64 * (N : ℝ)) ≤ Real.log N / (32 * (N : ℝ)) - 1 / N := by
    have heq : Real.log N / (32 * (N : ℝ)) - 1 / N =
        (Real.log N - 32) / (32 * (N : ℝ)) := by field_simp
    rw [heq]
    apply (div_le_div_iff₀ (by positivity : 0 < 64 * (N : ℝ)) (by positivity)).mpr
    nlinarith
  rw [xiHeatCassiniWoldNatIncrement_eq, xiHeatCassiniWoldNatWeight, dif_pos hp]
  linarith

/-- Every entry of two separated original prime windows has a common positive lower bound. -/
theorem paperWoldPrimeRectangle_eventual_lower (t : {t : ℝ // 1 / 2 ≤ t}) :
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ paperWoldPrimeIndices N,
      ∀ j ∈ paperWoldPrimeIndices (2 * N),
        Real.log N ^ 2 / (4096 * (N : ℝ)) ≤ (paperWoldDirectedKernel t (n, j)).re := by
  filter_upwards [paperWoldPrimeIndices_eventual_pair_card] with N hN
  intro n hn j hj
  obtain ⟨hnp, hnlo, hnhi⟩ := (paperWoldPrimeIndices_mem N n).mp hn
  obtain ⟨hjp, hjlo, hjhi⟩ := (paperWoldPrimeIndices_mem (2 * N) j).mp hj
  have hnloR : (N : ℝ) ≤ n + 1 := by exact_mod_cast (show N ≤ n + 1 by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from lt_of_lt_of_le (by omega) hN.1)
  have hnloD := prime_increment_window_lower N n hN.1 hN.2.1 hnp hnlo (by omega)
  have hjloD := prime_increment_window_lower N j hN.1 hN.2.1 hjp (by omega) (by omega)
  have hb : 0 ≤ Real.log N / (64 * (N : ℝ)) := by
    exact div_nonneg (by linarith [hN.2.1]) (by positivity)
  have hw : (N : ℝ) ≤ ((n : ℝ) + 1) ^ (2 * (t : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ n + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])
      (show (1 : ℝ) ≤ 2 * (t : ℝ) by linarith [t.property])
    rw [Real.rpow_one] at h
    exact hnloR.trans h
  rw [paperWoldDirectedKernel, if_pos (show n < j by omega), Complex.ofReal_re]
  calc
    Real.log N ^ 2 / (4096 * (N : ℝ)) =
        (N : ℝ) * (Real.log N / (64 * (N : ℝ))) * (Real.log N / (64 * (N : ℝ))) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul hw hnloD hb (Real.rpow_nonneg (by positivity) _)) hjloD hb
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (hb.trans hnloD))

end
end RHTower
