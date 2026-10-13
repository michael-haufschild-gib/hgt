import GaloisForLFunctions.RHTower.PaperWoldMovingPrefix
import GaloisForLFunctions.RHTower.PaperWoldPrimeNormGrowth

/-! # Uniform logarithmic bounds on native moving observations

Positive rectangles of the original composite matrix detect row damping. The
bounds hold for every admitted exponent and every original input prefix.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

private theorem critical_entry_lower (n j : ℕ) (hnj : n < j) :
    1 / (4 * (j : ℝ) + 8) ≤ (paperWoldCompositeEntry (1 / 2) n j).re := by
  obtain _ | m := j
  · omega
  have h := paperWoldDirectedKernel_composite_lower ⟨1 / 2, le_rfl⟩ m ⟨n, hnj⟩
  rw [show 2 * m + 4 = 2 * (m + 1) + 2 by omega] at h
  change 1 / (4 * (m : ℝ) + 12) ≤ ‖paperWoldCompositeEntry (1 / 2) n (m + 1)‖ at h
  rw [paperWoldCompositeEntry_norm_eq_re] at h
  convert h using 1
  push_cast
  ring

private theorem prefix_single_re (t : {t : ℝ // t ≤ 1 / 2}) (M n j : ℕ) (hj : j ≤ M) :
    (paperWoldCompositePrefixDefect t M (lp.single 2 j (1 : ℂ)) n).re =
      (1 - paperWoldCompositeDampingWeight (paperWoldCompositeDampingTime t) n) *
        (paperWoldCompositeEntry (1 / 2) n j).re := by
  rw [paperWoldCompositePrefixDefect_single, if_pos hj]
  simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_self, zero_mul, sub_zero]

private theorem rectangle_lower (t : {t : ℝ // t ≤ 1 / 2}) (M K : ℕ)
    (hK : 1 ≤ K) (hKM : 3 * K ≤ M + 1) :
    (1 - paperWoldCompositeDampingWeight (paperWoldCompositeDampingTime t) K) / 16 ≤
      ‖paperWoldCompositePrefixDefect t M‖ := by
  let r := paperWoldCompositeDampingTime t
  let d := 1 - paperWoldCompositeDampingWeight r K
  have hd : 0 ≤ d := sub_nonneg.mpr (paperWoldCompositeDampingWeight_le_one r K)
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h := paperWold_finite_rectangle_norm_lower (paperWoldCompositePrefixDefect t M)
    (Finset.Ico K (2 * K)) (Finset.Ico (2 * K) (3 * K)) (K : ℝ)
    (d / (16 * (K : ℝ))) hKp (by positivity)
    (by rw [Nat.card_Ico]; exact_mod_cast (show K ≤ 2 * K - K by omega))
    (by rw [Nat.card_Ico]; exact_mod_cast (show K ≤ 3 * K - 2 * K by omega)) (by
      intro n hn j hj
      obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ico.mp hn
      obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj
      rw [prefix_single_re t M n j (by omega)]
      have hjR : (j : ℝ) + 1 ≤ 3 * K := by exact_mod_cast hjhi
      have he : 1 / (16 * (K : ℝ)) ≤ (paperWoldCompositeEntry (1 / 2) n j).re :=
        (one_div_le_one_div_of_le (by positivity) (by linarith :
          4 * (j : ℝ) + 8 ≤ 16 * K)).trans (critical_entry_lower n j (by omega))
      have hdrow : d ≤ 1 - paperWoldCompositeDampingWeight r n :=
        sub_le_sub_left (paperWoldCompositeDampingWeight_antitone r hnlo) 1
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul hdrow he (by positivity : 0 ≤ 1 / (16 * (K : ℝ)))
          (sub_nonneg.mpr (paperWoldCompositeDampingWeight_le_one r n)))
  have heq : d / (16 * (K : ℝ)) * K = d / 16 := by field_simp
  rwa [heq] at h

private theorem singleton_lower (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) (hM : 1 ≤ M) :
    (1 - paperWoldCompositeDampingWeight (paperWoldCompositeDampingTime t) 0) / 12 ≤
      ‖paperWoldCompositePrefixDefect t M‖ := by
  let r := paperWoldCompositeDampingTime t
  have hd : 0 ≤ 1 - paperWoldCompositeDampingWeight r 0 :=
    sub_nonneg.mpr (paperWoldCompositeDampingWeight_le_one r 0)
  have h := paperWold_finite_rectangle_norm_lower (paperWoldCompositePrefixDefect t M)
    {0} {1} 1 ((1 - paperWoldCompositeDampingWeight r 0) / 12)
    (by norm_num) (by positivity) (by simp) (by simp) (by
      intro n hn j hj
      simp only [Finset.mem_singleton] at hn hj
      subst n; subst j
      rw [prefix_single_re t M 0 1 hM]
      have he := critical_entry_lower 0 1 (by omega)
      norm_num only [Nat.cast_one, mul_one] at he
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left he hd)
  simpa only [mul_one] using h

/-- A native positive rectangle forces detection once the logarithmic clock stays positive. -/
theorem paperWoldCompositePrefixDefect_clock_lower (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    (1 - Real.exp (-(paperWoldCompositeObservationClock t M / 2))) / 16 ≤
      ‖paperWoldCompositePrefixDefect t M‖ := by
  let r := paperWoldCompositeDampingTime t
  by_cases hM0 : M = 0
  · subst M
    simp [paperWoldCompositeObservationClock]
  by_cases hM1 : M = 1
  · subst M
    have hlog : Real.log (2 : ℝ) / 2 ≤ Real.log 3 := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog r.property
    have he : Real.exp (-((r : ℝ) * Real.log 3)) ≤
        Real.exp (-(paperWoldCompositeObservationClock t 1 / 2)) := by
      apply Real.exp_le_exp.mpr
      dsimp [paperWoldCompositeObservationClock]
      norm_num only [Nat.cast_one]
      dsimp [r] at hmul
      linarith
    have hd := paperWoldCompositeDampingWeight_le_one r 0
    rw [paperWoldCompositeDampingWeight_exp] at hd
    norm_num only [Nat.cast_zero, mul_zero, zero_add] at hd
    have h := singleton_lower t 1 (by omega)
    rw [paperWoldCompositeDampingWeight_exp] at h
    norm_num only [Nat.cast_zero, mul_zero, zero_add] at h
    dsimp [r] at he hd
    linarith
  let K := (M + 1) / 3
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hKM : 3 * K ≤ M + 1 := by dsimp [K]; omega
  have hsize : M + 1 < 3 * (K + 1) := Nat.lt_mul_div_succ (M + 1) (by omega)
  have hsizeR : (M : ℝ) + 1 ≤ 3 * ((K : ℝ) + 1) := by exact_mod_cast hsize.le
  have hbase : (M : ℝ) + 1 ≤ (2 * (K : ℝ) + 3) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) K, sq_nonneg (K : ℝ)]
  have hlog := Real.log_le_log (by positivity : 0 < (M : ℝ) + 1) hbase
  rw [Real.log_pow] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog r.property
  have he : Real.exp (-((r : ℝ) * Real.log (2 * (K : ℝ) + 3))) ≤
      Real.exp (-(paperWoldCompositeObservationClock t M / 2)) := by
    apply Real.exp_le_exp.mpr
    dsimp [paperWoldCompositeObservationClock]
    dsimp [r] at hmul
    linarith
  have h := rectangle_lower t M K hK hKM
  rw [paperWoldCompositeDampingWeight_exp] at h
  dsimp [r] at he
  linarith

/-- Strict triangularity turns a logarithmically small window into norm convergence. -/
theorem paperWoldCompositePrefixDefect_clock_upper (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    ‖paperWoldCompositePrefixDefect t M‖ ≤
      5 * (1 - Real.exp (-(3 * paperWoldCompositeObservationClock t M))) := by
  by_cases hM : M = 0
  · subst M
    simp [paperWoldCompositePrefixDefect_zero_prefix, paperWoldCompositeObservationClock]
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpoly : 2 * (M : ℝ) + 3 ≤ ((M : ℝ) + 1) ^ 3 := by
    nlinarith [sq_nonneg (M : ℝ), mul_nonneg (by linarith : 0 ≤ (M : ℝ) - 1)
      (sq_nonneg (M : ℝ))]
  have hlog := Real.log_le_log (by positivity : 0 < 2 * (M : ℝ) + 3) hpoly
  rw [Real.log_pow] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (paperWoldCompositeDampingTime t).property
  dsimp at hmul
  have he : Real.exp (-(3 * paperWoldCompositeObservationClock t M)) ≤
      Real.exp (-((paperWoldCompositeDampingTime t : ℝ) * Real.log (2 * (M : ℝ) + 3))) := by
    apply Real.exp_le_exp.mpr
    simpa only [paperWoldCompositeObservationClock, mul_left_comm] using
      neg_le_neg hmul
  have h := paperWoldCompositePrefixDefect_norm_upper t M
  rw [paperWoldCompositeDampingWeight_exp] at h
  linarith

end
end RHTower
