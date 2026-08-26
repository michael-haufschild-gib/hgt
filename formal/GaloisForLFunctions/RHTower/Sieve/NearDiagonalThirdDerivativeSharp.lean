import GaloisForLFunctions.RHTower.Sieve.NearDiagonalThirdDerivative
import GaloisForLFunctions.RHTower.Sieve.ThirdDerivativeTestSharp

namespace RHTower

noncomputable section

/-- Sharp third-derivative estimate for a unit-spaced near-diagonal block. -/
theorem norm_nearDiagonalBlock_third_sharp_le {T r M : ℝ}
    (hT : 0 < T) (hr : 0 < r) (hM : 0 < M) (hrM : r ≤ M)
    {N : ℕ} (hN : 1 ≤ N) (hspan : ((N : ℕ) - 1 : ℕ) ≤ M)
    (hlam1 : nearDiagonalLambda3 T r M ≤ 1) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * nearDiagonalPhase T r (M + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ 16 * 1368 * ((N : ℝ) * nearDiagonalLambda3 T r M ^ (1 / 6 : ℝ)
        + Real.sqrt N * nearDiagonalLambda3 T r M ^ (-(1 / 6 : ℝ))) := by
  have hlam0 : 0 < nearDiagonalLambda3 T r M := nearDiagonalLambda3_pos hT hr hM
  have hmemsub : ∀ x ∈ Set.Icc M (M + (((N : ℕ) - 1 : ℕ) : ℝ)),
      M ≤ x ∧ x ≤ 2 * M := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have htest := RHTower.Sieve.third_derivative_test_sharp
    (nearDiagonalNegDerivativeChain T r) M N hN hlam0 hlam1
    (by norm_num : (1 : ℝ) ≤ 1368)
    (by
      intro i hi x hx
      exact nearDiagonalNegDerivativeChain_hasDerivAt T hr.le
        (lt_of_lt_of_le hM (hmemsub x hx).1) i hi)
    (by
      intro x hx
      simpa only [nearDiagonalNegDerivativeChain] using
        nearDiagonalLambda3_le_D3Abs hT hr hM hrM (hmemsub x hx).1 (hmemsub x hx).2)
    (by
      intro x hx
      simpa only [nearDiagonalNegDerivativeChain] using
        D3Abs_le_nearDiagonalLambda3 hT hr hM hrM (hmemsub x hx).1 (hmemsub x hx).2)
  rw [← RHTower.Sieve.norm_phase_sum_neg (nearDiagonalPhase T r) M N]
  simp only [nearDiagonalNegDerivativeChain] at htest
  convert htest using 1

/-- Sharp third-derivative estimate on a half-open integer interval in one dyadic block. -/
theorem norm_nearDiagonalSum_third_sharp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    (A B : ℕ) (hA : 1 ≤ A) (hspan : B - A - 1 ≤ A) (hrA : r ≤ (A : ℝ))
    (hlam1 : nearDiagonalLambda3 T r A ≤ 1) :
    ‖nearDiagonalSum T r A B‖
      ≤ 16 * 1368 * ((((B - A : ℕ) : ℝ) *
          nearDiagonalLambda3 T r A ^ (1 / 6 : ℝ))
        + Real.sqrt (((B - A : ℕ) : ℝ)) *
          nearDiagonalLambda3 T r A ^ (-(1 / 6 : ℝ))) := by
  by_cases hBA : B ≤ A
  · rw [nearDiagonalSum, Finset.Ico_eq_empty_of_le hBA, Finset.sum_empty, norm_zero]
    rw [Nat.sub_eq_zero_of_le hBA]
    norm_num
  · have hAB : A < B := Nat.lt_of_not_le hBA
    have hN : 1 ≤ B - A := by omega
    have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hspan' : (((B - A : ℕ) - 1 : ℕ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hspan
    have hblock := norm_nearDiagonalBlock_third_sharp_le hT hr hA0 hrA hN hspan' hlam1
    rw [nearDiagonalSum, Finset.sum_Ico_eq_sum_range]
    have hsum :
        (∑ n ∈ Finset.range (B - A),
            Complex.exp (((2 * Real.pi * nearDiagonalPhase T r ((A + n : ℕ) : ℝ) : ℝ) : ℂ)
              * Complex.I)) =
          ∑ n ∈ Finset.range (B - A),
            Complex.exp (((2 * Real.pi * nearDiagonalPhase T r ((A : ℝ) + n) : ℝ) : ℂ)
              * Complex.I) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      congr 3
      push_cast
      rfl
    rw [hsum]
    simpa only [Real.sqrt_eq_rpow] using hblock

end

end RHTower
