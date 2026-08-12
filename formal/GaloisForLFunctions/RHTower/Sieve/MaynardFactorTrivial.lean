import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicPointwise
import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicCoefficientBound
import GaloisForLFunctions.RHTower.Sieve.LSeriesTrivialSize

/-!
# Sharp trivial bounds for individual Heath--Brown dyadic factors

Every unit-bounded dyadic block based at `N=2^q` has at most `N` terms, all supported in
`[N,2N)`.  On `Re s = sigma >= 0` its exact trivial bound is therefore `N^(1-sigma)`, with no
constant.  This applies to Möbius and zeta atoms.  The unique logarithm atom costs only
`log(2N)`.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

theorem complexCoeff_arithmeticDyadicBlock_support_Ico
    (F : ArithmeticFunction ℝ) (q n : ℕ)
    (hn : complexCoeff (arithmeticDyadicBlock F q) n ≠ 0) :
    n ∈ Finset.Ico (2 ^ q) (2 ^ (q + 1)) := by
  have hnreal : arithmeticDyadicBlock F q n ≠ 0 := by
    intro hzero
    exact hn (by rw [complexCoeff_apply, hzero, Complex.ofReal_zero])
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    exact hnreal (by simp [arithmeticDyadicBlock])
  have hlog : Nat.log 2 n = q := by
    by_contra hne
    exact hnreal (by simp [arithmeticDyadicBlock, hne])
  exact Finset.mem_Ico.mpr
    ((Nat.log_eq_iff (Or.inr ⟨by norm_num, hn0⟩)).mp hlog)

theorem norm_complexCoeff_arithmeticDyadicBlock_le_one
    {F : ArithmeticFunction ℝ} (hF : ∀ n, ‖F n‖ ≤ 1)
    (q n : ℕ) :
    ‖complexCoeff (arithmeticDyadicBlock F q) n‖ ≤ 1 := by
  simpa [complexCoeff_apply] using norm_arithmeticDyadicBlock_le_one hF q n

theorem norm_LSeries_arithmeticDyadicBlock_le_rpow
    {F : ArithmeticFunction ℝ} (hF : ∀ n, ‖F n‖ ≤ 1)
    (q : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) (y : ℝ) :
    ‖LSeries (complexCoeff (arithmeticDyadicBlock F q))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      (((2 ^ q : ℕ) : ℝ)) ^ (1 - sigma) := by
  let N : ℕ := 2 ^ q
  let M : ℕ := 2 ^ (q + 1)
  have hN : 0 < N := by simp [N]
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs0 : 0 ∉ Finset.Ico N M := by simp [N]
  have hsupp : ∀ n : ℕ,
      complexCoeff (arithmeticDyadicBlock F q) n ≠ 0 → n ∈ Finset.Ico N M := by
    intro n hn
    simpa [N, M] using complexCoeff_arithmeticDyadicBlock_support_Ico F q n hn
  have hterm : ∀ n ∈ Finset.Ico N M,
      ‖complexCoeff (arithmeticDyadicBlock F q) n‖ *
          (n : ℝ) ^ (-sigma) ≤ (N : ℝ) ^ (-sigma) := by
    intro n hn
    have hnN : N ≤ n := (Finset.mem_Ico.mp hn).1
    have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    have hpow : (n : ℝ) ^ (-sigma) ≤ (N : ℝ) ^ (-sigma) :=
      Real.rpow_le_rpow_of_nonpos hNreal hnreal (by linarith)
    calc
      ‖complexCoeff (arithmeticDyadicBlock F q) n‖ * (n : ℝ) ^ (-sigma)
          ≤ 1 * (N : ℝ) ^ (-sigma) := by
            exact mul_le_mul
              (norm_complexCoeff_arithmeticDyadicBlock_le_one hF q n) hpow
              (Real.rpow_nonneg (by positivity) _) (by norm_num)
      _ = (N : ℝ) ^ (-sigma) := one_mul _
  calc
    ‖LSeries (complexCoeff (arithmeticDyadicBlock F q))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ ∑ n ∈ Finset.Ico N M,
            ‖complexCoeff (arithmeticDyadicBlock F q) n‖ *
              (n : ℝ) ^ (-sigma) :=
      norm_LSeries_le_sum_of_support hs0 hsupp sigma y
    _ ≤ ∑ _n ∈ Finset.Ico N M, (N : ℝ) ^ (-sigma) :=
      Finset.sum_le_sum hterm
    _ = (N : ℝ) * (N : ℝ) ^ (-sigma) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Ico N M).card = N := by
        simp [N, M, pow_succ]
        omega
      rw [hcard]
    _ = (N : ℝ) ^ (1 - sigma) := by
      calc
        (N : ℝ) * (N : ℝ) ^ (-sigma) =
            (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-sigma) := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ ((1 : ℝ) + (-sigma)) :=
          (Real.rpow_add hNreal _ _).symm
        _ = (N : ℝ) ^ (1 - sigma) := by ring_nf
    _ = (((2 ^ q : ℕ) : ℝ)) ^ (1 - sigma) := by rfl

theorem norm_LSeries_moebiusDyadicBlock_le_rpow
    (L q : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) (y : ℝ) :
    ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      (((2 ^ q : ℕ) : ℝ)) ^ (1 - sigma) :=
  norm_LSeries_arithmeticDyadicBlock_le_rpow
    (norm_truncatedMoebius_le_one L) q hsigma y

theorem norm_LSeries_zetaDyadicBlock_le_rpow
    (X q : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) (y : ℝ) :
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      (((2 ^ q : ℕ) : ℝ)) ^ (1 - sigma) :=
  norm_LSeries_arithmeticDyadicBlock_le_rpow
    (norm_coeffTrunc_zeta_le_one X) q hsigma y

theorem norm_LSeries_logDyadicBlock_le_rpow_mul_log
    (X q : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) (y : ℝ) :
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      (((2 ^ q : ℕ) : ℝ)) ^ (1 - sigma) *
        Real.log (((2 ^ (q + 1) : ℕ) : ℝ)) := by
  let N : ℕ := 2 ^ q
  let M : ℕ := 2 ^ (q + 1)
  have hN : 0 < N := by simp [N]
  have hN1 : 1 ≤ N := hN
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hM2 : 2 ≤ M := by
    dsimp [M]
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ (q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlogM : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hM2.trans' (by norm_num : 1 ≤ 2)))
  have hs0 : 0 ∉ Finset.Ico N M := by simp [N]
  have hsupp : ∀ n : ℕ,
      complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n ≠ 0 →
          n ∈ Finset.Ico N M := by
    intro n hn
    simpa [N, M] using complexCoeff_arithmeticDyadicBlock_support_Ico
      (coeffTrunc ArithmeticFunction.log X) q n hn
  have hterm : ∀ n ∈ Finset.Ico N M,
      ‖complexCoeff
          (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n‖ *
          (n : ℝ) ^ (-sigma) ≤
        Real.log (M : ℝ) * (N : ℝ) ^ (-sigma) := by
    intro n hn
    have hnI := Finset.mem_Ico.mp hn
    have hn1 : 1 ≤ n := hN1.trans hnI.1
    have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnI.1
    have hpow : (n : ℝ) ^ (-sigma) ≤ (N : ℝ) ^ (-sigma) :=
      Real.rpow_le_rpow_of_nonpos hNreal hnreal (by linarith)
    have hcoeff : ‖complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n‖ ≤
        Real.log (n : ℝ) := by
      simpa [complexCoeff_apply] using
        norm_arithmeticDyadicLogBlock_le_log X q hn1
    have hlog : Real.log (n : ℝ) ≤ Real.log (M : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hn1))
      exact_mod_cast hnI.2.le
    exact mul_le_mul (hcoeff.trans hlog) hpow
      (Real.rpow_nonneg (by positivity) _) hlogM
  have hcard : (Finset.Ico N M).card = N := by
    simp [N, M, pow_succ]
    omega
  calc
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ ∑ n ∈ Finset.Ico N M,
            ‖complexCoeff
              (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n‖ *
              (n : ℝ) ^ (-sigma) :=
      norm_LSeries_le_sum_of_support hs0 hsupp sigma y
    _ ≤ ∑ _n ∈ Finset.Ico N M,
          Real.log (M : ℝ) * (N : ℝ) ^ (-sigma) :=
      Finset.sum_le_sum hterm
    _ = ((N : ℝ) * (N : ℝ) ^ (-sigma)) * Real.log (M : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      ring
    _ = (N : ℝ) ^ (1 - sigma) * Real.log (M : ℝ) := by
      congr 1
      calc
        (N : ℝ) * (N : ℝ) ^ (-sigma) =
            (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-sigma) := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ ((1 : ℝ) + (-sigma)) :=
          (Real.rpow_add hNreal _ _).symm
        _ = (N : ℝ) ^ (1 - sigma) := by ring_nf
    _ = (((2 ^ q : ℕ) : ℝ)) ^ (1 - sigma) *
          Real.log (((2 ^ (q + 1) : ℕ) : ℝ)) := by rfl

end RHTower.Sieve
