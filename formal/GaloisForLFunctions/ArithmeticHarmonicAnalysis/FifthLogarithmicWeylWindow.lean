import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FifthLogarithmicCorrelationBound
import GaloisForLFunctions.RHTower.ZetaElevenEighteenthsWeylBlock

/-! # Weyl differencing with the fifth-dual correlation estimate

The small-shift second-derivative range and the large-shift fifth-dual range
have one uniform bound. The actual Weyl inequality then controls every prefix.
-/

noncomputable section
open Complex RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The common bound `Q` for all Weyl shifts `h ≤ H`. -/
def fifthDiffLogQ (T : ℝ) (N H : ℕ) : ℝ :=
  (T * H) ^ (11 / 30 : ℝ) * (N : ℝ) ^ (-(1 / 5) : ℝ) + (T * H) ^ (5 / 8 : ℝ) * (N : ℝ) ^ (-(13 / 16) : ℝ) + T * H / (N : ℝ) ^ 2
    + ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ) + (T * H) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ)
    + (N : ℝ) ^ (5 / 8 : ℝ)

theorem fifthDiffLogQ_nonneg {T : ℝ} (hT : 0 ≤ T) (N H : ℕ) : 0 ≤ fifthDiffLogQ T N H := by
  unfold fifthDiffLogQ; positivity

/-- The second-derivative term fits the transition to the fifth-dual bound. -/
theorem sqrt_ratio_le_of_fourth_le {X n : ℝ} (hX : 0 ≤ X) (hn : 0 < n)
    (h : X ^ 4 ≤ 7 * n ^ 9) : (X / n) ^ (1 / 2 : ℝ) ≤ 2 * n ^ (5 / 8 : ℝ) := by
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (8 : ℕ) ≠ 0)).mp ?_
  have he1 : ((X / n) ^ (1 / 2 : ℝ)) ^ (8 : ℕ) = (X / n) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have he2 : (2 * n ^ (5 / 8 : ℝ)) ^ (8 : ℕ) = 256 * n ^ 5 := by
    rw [mul_pow, ← Real.rpow_natCast (n ^ (5 / 8 : ℝ)), ← Real.rpow_mul hn.le]
    norm_num
  rw [he1, he2, div_pow, div_le_iff₀ (by positivity)]
  nlinarith only [h, pow_nonneg hn.le 9]

/-- A common bound for every correlation in the Weyl window. -/
theorem norm_sum_diffLog_fifth_le {T : ℝ} (hT : 0 < T) {N L h H : ℕ} (hN : 3 ≤ N) (hh : 1 ≤ h)
    (hhH : h ≤ H) (h2h : 2 * h ≤ N) (hL : L ≤ N) :
    ‖∑ n ∈ Finset.range L, Complex.exp (((2 * Real.pi * (T * (Real.log ((N : ℝ) + n + h)
        - Real.log ((N : ℝ) + n))) : ℝ) : ℂ) * I)‖ ≤ 10 ^ 24 * fifthDiffLogQ T N H := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hXY : T * h ≤ T * H := mul_le_mul_of_nonneg_left (by exact_mod_cast hhH) hT.le
  have hTX : T ≤ T * h := by nlinarith
  have hX0 : 0 < T * h := by positivity
  have hsqrt : ((N : ℝ) ^ 3 / (T * h)) ^ (1 / 2 : ℝ) ≤ ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_left (by positivity) hT hTX) (by norm_num)
  have hQ := fifthDiffLogQ_nonneg hT.le N H
  by_cases hB : 7 * (N : ℝ) ^ 9 ≤ (T * h) ^ 4
  · refine (norm_sum_diffLog_fifth_le_B hT (by omega) hh h2h hL hB).trans ?_
    have m1 : (T * h) ^ (11 / 30 : ℝ) ≤ (T * H) ^ (11 / 30 : ℝ) :=
      Real.rpow_le_rpow hX0.le hXY (by norm_num)
    have m2 : (T * h) ^ (5 / 8 : ℝ) ≤ (T * H) ^ (5 / 8 : ℝ) :=
      Real.rpow_le_rpow hX0.le hXY (by norm_num)
    have m3 : T * h / (N : ℝ) ^ 2 ≤ T * H / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hXY (by positivity)
    have m5 : (T * h) ^ (2 / 5 : ℝ) ≤ (T * H) ^ (2 / 5 : ℝ) :=
      Real.rpow_le_rpow hX0.le hXY (by norm_num)
    have hN1 : 0 ≤ (N : ℝ) ^ (-(13 / 16) : ℝ) := by positivity
    have hN2 : 0 ≤ (N : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
    have hN3 : 0 ≤ (N : ℝ) ^ (5 / 8 : ℝ) := by positivity
    have m1' := mul_le_mul_of_nonneg_right m1
      (by positivity : 0 ≤ (N : ℝ) ^ (-(1 / 5) : ℝ))
    have m2' := mul_le_mul_of_nonneg_right m2 hN1
    have m5' := mul_le_mul_of_nonneg_right m5 hN2
    unfold fifthDiffLogQ
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    linarith
  · push Not at hB
    have hXN : T * h ≤ (N : ℝ) ^ 3 := by
      have hn3 : 7 ≤ (N : ℝ) ^ 3 := by
        have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
        have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 3
        norm_num only at hp
        linarith only [hp]
      have h12 : (T * h) ^ 4 ≤ ((N : ℝ) ^ 3) ^ 4 := by
        calc (T * h) ^ 4 ≤ 7 * (N : ℝ) ^ 9 := hB.le
          _ ≤ (N : ℝ) ^ 3 * (N : ℝ) ^ 9 :=
            mul_le_mul_of_nonneg_right hn3 (by positivity)
          _ = _ := by ring
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h12
    refine (norm_sum_diffLog_le_second hT (by omega) hh h2h hL hXN).trans ?_
    have hr := sqrt_ratio_le_of_fourth_le hX0.le hn0 hB.le
    unfold fifthDiffLogQ
    have : 0 ≤ (T * H) ^ (11 / 30 : ℝ) * (N : ℝ) ^ (-(1 / 5) : ℝ) + (T * H) ^ (5 / 8 : ℝ) * (N : ℝ) ^ (-(13 / 16) : ℝ)
        + T * H / (N : ℝ) ^ 2 + (T * H) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
    have hN3 : 0 ≤ (N : ℝ) ^ (5 / 8 : ℝ) := by positivity
    have hs0 : 0 ≤ ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ) := by positivity
    linarith

/-- The fifth-dual correlation estimate controls every logarithmic prefix. -/
theorem norm_prefix_sq_le_fifthWeyl {t : ℝ} (ht : 0 < t) {N L H : ℕ} (hN : 3 ≤ N) (hL : L ≤ N)
    (hH1 : 1 ≤ H) (hHN : 2 * H ≤ N) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2
      ≤ (H : ℝ) ^ 2 + 4 * (N : ℝ) ^ 2 / H
        + 4 * 10 ^ 24 * N * fifthDiffLogQ (t / (2 * Real.pi)) N H := by
  have hT : 0 < t / (2 * Real.pi) := by positivity
  have hQ := fifthDiffLogQ_nonneg hT.le N H
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH1
  set a : ℕ → ℂ := fun j => ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ))) with ha
  have hanorm : ∀ j, ‖a j‖ ≤ 1 := fun j => norm_natCast_cpow_neg_I_mul_le (by omega)
  have hextra : 0 ≤ 4 * (N : ℝ) ^ 2 / H + 4 * 10 ^ 24 * N * fifthDiffLogQ (t / (2 * Real.pi)) N H := by
    positivity
  by_cases hLH : L < H
  · have hP : ‖∑ j ∈ Finset.range L, a j‖ ≤ H := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun j _ => hanorm j).trans ?_
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast hLH.le
    have : ‖∑ j ∈ Finset.range L, a j‖ ^ 2 ≤ (H : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hP 2
    linarith
  push Not at hLH
  have hW := RHTower.Sieve.weyl_vdc a hanorm L H hH1 hLH
  -- each correlation
  have hcorr : ∀ h ∈ Finset.Icc 1 (H - 1),
      ‖RHTower.Sieve.weylCorr a L h‖ ≤ 10 ^ 24 * fifthDiffLogQ (t / (2 * Real.pi)) N H := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    have e : RHTower.Sieve.weylCorr a L h = ∑ n ∈ Finset.range (L - h),
        Complex.exp (((-(2 * Real.pi * (t / (2 * Real.pi) * (Real.log ((N : ℝ) + n + h)
          - Real.log ((N : ℝ) + n))))) : ℝ) * I) := by
      unfold RHTower.Sieve.weylCorr
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [ha]
      rw [RHTower.Sieve.natCast_cpow_neg_I_mul t _ (by omega),
        RHTower.Sieve.natCast_cpow_neg_I_mul t _ (by omega), ← Complex.exp_conj, map_mul,
        Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
      congr 1
      simp only [RHTower.Sieve.logPhase]
      push_cast
      field_simp
      ring
    rw [e, norm_sum_cexp_neg (Finset.range (L - h)) (fun n => 2 * Real.pi * (t / (2 * Real.pi)
      * (Real.log ((N : ℝ) + n + h) - Real.log ((N : ℝ) + n))))]
    exact norm_sum_diffLog_fifth_le hT hN hh.1 (by omega) (by omega) (by omega)
  have hsum : ∑ h ∈ Finset.Icc 1 (H - 1), ‖RHTower.Sieve.weylCorr a L h‖
      ≤ H * (10 ^ 24 * fifthDiffLogQ (t / (2 * Real.pi)) N H) := by
    refine (Finset.sum_le_sum hcorr).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : H + 1 - 1 - 1 ≤ H := by omega
    exact_mod_cast this
  have hLN : (L : ℝ) ≤ N := by exact_mod_cast hL
  have hmain : (H : ℝ) * ‖∑ n ∈ Finset.range L, a n‖ ^ 2
      ≤ 4 * N * (N + H * (10 ^ 24 * fifthDiffLogQ (t / (2 * Real.pi)) N H)) := by
    refine hW.trans ?_
    have h1 : (L : ℝ) + ∑ h ∈ Finset.Icc 1 (H - 1), ‖RHTower.Sieve.weylCorr a L h‖
        ≤ N + H * (10 ^ 24 * fifthDiffLogQ (t / (2 * Real.pi)) N H) := by linarith
    have h2 : 0 ≤ (L : ℝ) + ∑ h ∈ Finset.Icc 1 (H - 1), ‖RHTower.Sieve.weylCorr a L h‖ := by
      positivity
    have := mul_le_mul (mul_le_mul_of_nonneg_left hLN (by norm_num : (0 : ℝ) ≤ 4)) h1 h2
      (by positivity)
    linarith
  have hdiv : ‖∑ n ∈ Finset.range L, a n‖ ^ 2
      ≤ 4 * (N : ℝ) ^ 2 / H + 4 * 10 ^ 24 * N * fifthDiffLogQ (t / (2 * Real.pi)) N H := by
    rw [← mul_le_mul_iff_of_pos_left hH0]
    calc (H : ℝ) * ‖∑ n ∈ Finset.range L, a n‖ ^ 2
        ≤ 4 * N * (N + H * (10 ^ 24 * fifthDiffLogQ (t / (2 * Real.pi)) N H)) := hmain
      _ = H * (4 * (N : ℝ) ^ 2 / H + 4 * 10 ^ 24 * N * fifthDiffLogQ (t / (2 * Real.pi)) N H) := by
        field_simp
  have : (0 : ℝ) ≤ (H : ℝ) ^ 2 := by positivity
  linarith

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_prefix_sq_le_fifthWeyl
