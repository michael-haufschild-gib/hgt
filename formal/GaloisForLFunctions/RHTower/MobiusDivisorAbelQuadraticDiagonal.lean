import GaloisForLFunctions.RHTower.DivisorHyperbolaAbelBound
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# Quadratic ceiling for the literal Möbius–divisor Abel diagonal

The symmetric divisor hyperbola is summed in signed time before taking channel
squares. Exact complete/terminal dilation transport gives
`C_d(M)^(2 : ℕ) <= 361 M sqrt(floor((M-1)/d))`, hence
`sum_(d<=M) C_d(M)^(2 : ℕ) <= 722 M^(2 : ℕ)`.

This removes the harmonic loss of the pointwise divisor envelope. The signed
cross-channel contribution is not bounded by this theorem, and no RH conclusion
or diagonal-dominance premise is asserted.
-/

noncomputable section
open Finset HTGeometry
namespace RHTower

/-- Exact identification of the literal undilated source with its signed hyperbola decomposition. -/
theorem mobiusDivisorDilationChannel_one_eq_hyperbola (M : ℕ) :
    mobiusDivisorDilationChannel M 1 =
      divisorHyperbolaSmoothAbel M + 2 * centeredDivisorHyperbolaAbel M := by
  have hpoint (k : ℕ) : primeFreeDivisorDefect k =
      divisorHyperbolaSmoothRemainder k + 2 * centeredDivisorHyperbola k := by
    exact (divisorHyperbolaSmooth_add_centered k).symm
  by_cases hM : M = 0
  · subst M
    simp [mobiusDivisorDilationChannel,divisorHyperbolaSmoothAbel,centeredDivisorHyperbolaAbel]
  · have hM1 : 1 ≤ M := by omega
    have hpred : M-1+1=M := by omega
    unfold mobiusDivisorDilationChannel
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, Nat.div_one]
    rw [← Ico_add_one_right_eq_Icc, hpred,
      sum_Ico_eq_sub _ hM1]
    simp only [sum_range_one, Nat.zero_add, Nat.cast_one, Real.sqrt_one, Nat.cast_zero,
      Real.sqrt_zero, sub_zero, one_mul]
    have hzero : primeFreeDivisorDefect 0 = 0 := by simp [primeFreeDivisorDefect]
    rw [hzero,sub_zero]
    unfold divisorHyperbolaSmoothAbel centeredDivisorHyperbolaAbel
    rw [mul_sum (s := range M) (a := (2:ℝ)), ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    rw [hpoint]
    simp only [halfOrderAbelStep,Nat.zero_add]
    ring

/-- Signed temporal cancellation yields a three-quarter-power envelope for the actual divisor
channel, without any hypothesis about Möbius cancellation. -/
theorem abs_mobiusDivisorDilationChannel_one_le (M : ℕ) :
    |mobiusDivisorDilationChannel M 1| ≤
      7 * Real.sqrt M * Real.sqrt (Real.sqrt M) := by
  rw [mobiusDivisorDilationChannel_one_eq_hyperbola]
  exact abs_divisorHyperbolaCompleteAbel_le_threeQuarter M

/-- Complete quotient blocks plus the literal clipped last block reconstruct each dilation. -/
theorem mobiusDivisorDilationChannel_eq_full_terminal {M d : ℕ}
    (hd : 1 ≤ d) (hdM : d ≤ M-1) :
    mobiusDivisorDilationChannel M d =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (Real.sqrt d * mobiusDivisorDilationChannel ((M-1)/d) 1 +
          (Real.sqrt M - Real.sqrt (((M-1)/d)*d : ℕ)) *
            primeFreeDivisorDefect ((M-1)/d)) := by
  let Q := (M-1)/d
  have hdpos : 0 < d := by omega
  have hQ : 1 ≤ Q := (Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hdM)
  have hQd : Q*d ≤ M-1 := Nat.div_mul_le_self (M-1) d
  have htop : M ≤ (Q+1)*d := by
    have h := (Nat.div_lt_iff_lt_mul hdpos).mp (show (M-1)/d < Q+1 by dsimp [Q]; omega)
    omega
  have hsum :
      (∑ q ∈ Icc 1 Q, divisorDilationClippedAbelWeight M d q * primeFreeDivisorDefect q) =
      (∑ q ∈ Icc 1 (Q-1), divisorDilationClippedAbelWeight M d q * primeFreeDivisorDefect q) +
        divisorDilationClippedAbelWeight M d Q * primeFreeDivisorDefect Q := by
    have h := sum_Icc_succ_top (f := fun q =>
      divisorDilationClippedAbelWeight M d q * primeFreeDivisorDefect q)
      (show 1 ≤ Q-1+1 by omega)
    simpa only [Nat.sub_add_cancel hQ] using h
  have hfull :
      (∑ q ∈ Icc 1 (Q-1), divisorDilationClippedAbelWeight M d q * primeFreeDivisorDefect q) =
        Real.sqrt d * mobiusDivisorDilationChannel Q 1 := by
    simp only [mobiusDivisorDilationChannel, ArithmeticFunction.moebius_apply_one,
      Int.cast_one, one_mul, Nat.div_one, mul_sum]
    apply sum_congr rfl
    intro q hq
    have hq1 := (mem_Icc.mp hq).1
    have hqQ : q+1 ≤ Q := by have := (mem_Icc.mp hq).2; omega
    have hfull : (q+1)*d ≤ M :=
      (Nat.mul_le_mul_right d hqQ).trans (hQd.trans (Nat.sub_le M 1))
    rw [divisorDilationClippedAbelWeight_eq_full hd hq1 hfull]
    ring
  have hlast : divisorDilationClippedAbelWeight M d Q =
      Real.sqrt M - Real.sqrt (Q*d : ℕ) := by
    rw [divisorDilationClippedAbelWeight_eq_endpointDiff hd hQ hQd,
      min_eq_left htop, min_eq_right (hQd.trans (Nat.sub_le M 1))]
  rw [mobiusDivisorDilationChannel_eq_quotientBlocks hd]
  change _ * (∑ q ∈ Icc 1 Q, _) = _
  rw [hsum,hfull,hlast]

/-- The clipped final block has a square-root dilation budget, including an exactly full last block. -/
private theorem abs_divisorDilation_terminal_le {M d Q : ℕ}
    (hd : 1 ≤ d) (hQ : 1 ≤ Q) (hlo : Q*d ≤ M) (hhi : M ≤ (Q+1)*d) :
    |(Real.sqrt M - Real.sqrt (Q*d : ℕ)) * primeFreeDivisorDefect Q| ≤
      12 * Real.sqrt d := by
  have hnonneg : 0 ≤ Real.sqrt M - Real.sqrt (Q*d : ℕ) := by
    apply sub_nonneg.mpr
    exact Real.sqrt_le_sqrt (by exact_mod_cast hlo)
  have hgap : Real.sqrt M - Real.sqrt (Q*d : ℕ) ≤
      Real.sqrt d * (Real.sqrt (Q+1 : ℕ) - Real.sqrt Q) := by
    have h := Real.sqrt_le_sqrt (by exact_mod_cast hhi : (M:ℝ) ≤ ((Q+1)*d : ℕ))
    push_cast at h ⊢
    rw [Real.sqrt_mul (by positivity)] at h
    rw [Real.sqrt_mul (by positivity)]
    nlinarith only [h]
  have hstep : 0 ≤ Real.sqrt (Q+1 : ℕ) - Real.sqrt Q := by
    apply sub_nonneg.mpr
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show Q ≤ Q+1 by omega))
  have hhalf : (Real.sqrt (Q+1 : ℕ) - Real.sqrt Q) * Real.sqrt Q ≤ 1/2 := by
    have h0 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) Q)
    have h1 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (Q+1))
    have h2 := sq_nonneg (Real.sqrt (Q+1 : ℕ) - Real.sqrt Q)
    push_cast at h0 h1 h2 ⊢
    nlinarith only [h0,h1,h2]
  rw [abs_mul,abs_of_nonneg hnonneg]
  calc
    _ ≤ (Real.sqrt d * (Real.sqrt (Q+1 : ℕ) - Real.sqrt Q)) * (24 * Real.sqrt Q) :=
      mul_le_mul hgap (abs_primeFreeDivisorDefect_le hQ) (abs_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) hstep)
    _ = (24 * Real.sqrt d) *
        ((Real.sqrt (Q+1 : ℕ) - Real.sqrt Q) * Real.sqrt Q) := by ring
    _ ≤ (24 * Real.sqrt d) * (1/2) :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = _ := by ring

/-- Every literal dilation square is controlled by the square root of its quotient depth. -/
theorem mobiusDivisorDilationChannel_sq_le_quotient {M d : ℕ} (hd : 1 ≤ d) :
    mobiusDivisorDilationChannel M d ^ (2 : ℕ) ≤
      361 * (M : ℝ) * Real.sqrt ((M-1)/d : ℕ) := by
  by_cases hdM : d ≤ M-1
  · let Q := (M-1)/d
    have hdpos : 0 < d := by omega
    have hQ : 1 ≤ Q := (Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hdM)
    have hQd : Q*d ≤ M := (Nat.div_mul_le_self (M-1) d).trans (Nat.sub_le M 1)
    have htop : M ≤ (Q+1)*d := by
      have h := (Nat.div_lt_iff_lt_mul hdpos).mp (show (M-1)/d < Q+1 by dsimp [Q]; omega)
      omega
    have hterminal := abs_divisorDilation_terminal_le hd hQ hQd htop
    have hmain := abs_mobiusDivisorDilationChannel_one_le Q
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hraw : |mobiusDivisorDilationChannel M d| ≤
        Real.sqrt d * (7 * Real.sqrt Q * Real.sqrt (Real.sqrt Q)) + 12 * Real.sqrt d := by
      rw [mobiusDivisorDilationChannel_eq_full_terminal hd hdM,abs_mul]
      change |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        |Real.sqrt d * mobiusDivisorDilationChannel Q 1 +
          (Real.sqrt M-Real.sqrt (Q*d : ℕ))*primeFreeDivisorDefect Q| ≤ _
      calc
        _ ≤ 1 * |Real.sqrt d * mobiusDivisorDilationChannel Q 1 +
            (Real.sqrt M-Real.sqrt (Q*d : ℕ))*primeFreeDivisorDefect Q| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ ≤ _ := by
          rw [one_mul]
          have h := (abs_add_le (Real.sqrt d * mobiusDivisorDilationChannel Q 1)
            ((Real.sqrt M-Real.sqrt (Q*d : ℕ))*primeFreeDivisorDefect Q))
          rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] at h
          exact h.trans (add_le_add
            (mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg _)) hterminal)
    have hsQ : 1 ≤ Real.sqrt Q := by
      simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ Q by exact_mod_cast hQ)
    have hrQ : 1 ≤ Real.sqrt (Real.sqrt Q) := by simpa using Real.sqrt_le_sqrt hsQ
    have hsmall : 12 * Real.sqrt d ≤
        12 * Real.sqrt d * Real.sqrt Q * Real.sqrt (Real.sqrt Q) := by
      calc
        12 * Real.sqrt d = 12 * Real.sqrt d * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    have hbound : |mobiusDivisorDilationChannel M d| ≤
        19 * Real.sqrt d * Real.sqrt Q * Real.sqrt (Real.sqrt Q) := by
      nlinarith only [hraw,hsmall]
    have hsq : mobiusDivisorDilationChannel M d ^ (2 : ℕ) ≤
        361 * (d:ℝ) * Q * Real.sqrt Q := by
      calc
        _ = |mobiusDivisorDilationChannel M d| ^ (2 : ℕ) := (sq_abs _).symm
        _ ≤ (19 * Real.sqrt d * Real.sqrt Q * Real.sqrt (Real.sqrt Q))^(2 : ℕ) := by gcongr
        _ = _ := by
          simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d),
            Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) Q),Real.sq_sqrt (Real.sqrt_nonneg (Q:ℝ))]
          ring
    have hscale : (d:ℝ) * Q ≤ M := by exact_mod_cast (by simpa [Nat.mul_comm] using hQd)
    change _ ≤ 361 * (M:ℝ) * Real.sqrt Q
    exact hsq.trans (by nlinarith [mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg (Q:ℝ))])
  · have hempty : Icc d (M-1) = ∅ := Icc_eq_empty_of_lt (by omega)
    simp only [mobiusDivisorDilationChannel,hempty,sum_empty,mul_zero,zero_pow (by omega : (2:ℕ) ≠ 0)]
    positivity

/-- The complete literal arithmetic diagonal has a quadratic ceiling with no harmonic loss.
Signed time cancellation is taken inside each channel before the channel squares are summed. -/
theorem sum_mobiusDivisorDilationChannel_sq_le_quadratic (M : ℕ) :
    (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d ^ (2 : ℕ)) ≤ 722 * (M:ℝ)^(2 : ℕ) := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 M) :
      mobiusDivisorDilationChannel M d ^ (2 : ℕ) ≤
        (361 * (M:ℝ) * Real.sqrt M) * (1 / Real.sqrt d) := by
    have hd1 := (mem_Icc.mp hd).1
    have hdroot : 0 < Real.sqrt d := by positivity
    have hroot : Real.sqrt ((M-1)/d : ℕ) ≤ Real.sqrt M / Real.sqrt d := by
      apply (le_div_iff₀ hdroot).mpr
      rw [← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      exact_mod_cast (Nat.div_mul_le_self (M-1) d).trans (Nat.sub_le M 1)
    have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 361*(M:ℝ) by positivity)
    exact (mobiusDivisorDilationChannel_sq_le_quotient hd1).trans (by
      convert h using 1; ring)
  calc
    _ ≤ ∑ d ∈ Icc 1 M, (361*(M:ℝ)*Real.sqrt M)*(1/Real.sqrt d) := sum_le_sum hpoint
    _ = (361*(M:ℝ)*Real.sqrt M) * ∑ d ∈ Icc 1 M, (1:ℝ)/Real.sqrt d := by rw [mul_sum]
    _ ≤ (361*(M:ℝ)*Real.sqrt M) * (2*Real.sqrt M) :=
      mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le M) (by positivity)
    _ = _ := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M)]

end RHTower
