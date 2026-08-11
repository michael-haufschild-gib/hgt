import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicBoxes
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSigma

/-!
# Pointwise derivative-test bounds for Heath--Brown dyadic factors

The dyadic coefficient blocks in the finite Heath--Brown packet are not merely abstract finite
L-series.  A zeta block is exactly the half-open Dirichlet block

`[2^q, min (X+1) (2^(q+1)))`,

and a logarithm block is the same polynomial with coefficient `log n`.  This file proves those
identities and transfers the corpus's derivative-test saving to both factors.  The logarithmic
coefficient is inserted by an increasing-weight Abel inequality, costing only `2 log M` and
preserving the power saving.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped zeta

/-- Exclusive upper endpoint of the `q`-th block after sharp truncation at `X`. -/
def heathBrownDyadicFactorTop (X q : ℕ) : ℕ :=
  min (X + 1) (2 ^ (q + 1))

theorem pow_le_heathBrownDyadicFactorTop
    {X q : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X) :
    2 ^ q ≤ heathBrownDyadicFactorTop X q := by
  rw [heathBrownDyadicFactorTop, Nat.le_min]
  constructor
  · have hpow : 2 ^ q ≤ 2 ^ Nat.log 2 X :=
      Nat.pow_le_pow_right (by norm_num) hq
    exact hpow.trans (Nat.le_succ_of_le (Nat.pow_log_le_self 2 (by omega)))
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ q)

theorem heathBrownDyadicFactorTop_le_two_mul_add_one (X q : ℕ) :
    heathBrownDyadicFactorTop X q ≤ 2 * 2 ^ q + 1 := by
  calc
    heathBrownDyadicFactorTop X q ≤ 2 ^ (q + 1) := min_le_right _ _
    _ = 2 * 2 ^ q := by rw [pow_succ]; ring
    _ ≤ 2 * 2 ^ q + 1 := Nat.le_succ _

theorem complexCoeff_zetaDyadicBlock_support_Ico
    (X q n : ℕ)
    (hn : complexCoeff
      (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q) n ≠ 0) :
    n ∈ Finset.Ico (2 ^ q) (heathBrownDyadicFactorTop X q) := by
  have hnreal :
      arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q n ≠ 0 := by
    intro hzero
    exact hn (by rw [complexCoeff_apply, hzero, Complex.ofReal_zero])
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    exact hnreal (by simp [arithmeticDyadicBlock])
  have hlog : Nat.log 2 n = q := by
    by_contra hne
    exact hnreal (by simp [arithmeticDyadicBlock, hne])
  have hnX : n ≤ X := by
    by_contra hnot
    have hzero := coeffTrunc_apply_of_lt (zeta : ArithmeticFunction ℝ)
      (Nat.lt_of_not_ge hnot)
    rw [arithmeticDyadicBlock_apply, if_pos hlog, hzero] at hnreal
    exact hnreal rfl
  have hedges := (Nat.log_eq_iff (Or.inr ⟨by norm_num, hn0⟩)).mp hlog
  exact Finset.mem_Ico.mpr
    ⟨hedges.1, lt_min (Nat.lt_succ_iff.mpr hnX) hedges.2⟩

theorem complexCoeff_logDyadicBlock_support_Ico
    (X q n : ℕ)
    (hn : complexCoeff
      (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q) n ≠ 0) :
    n ∈ Finset.Ico (2 ^ q) (heathBrownDyadicFactorTop X q) := by
  have hnreal : arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q n ≠ 0 := by
    intro hzero
    exact hn (by rw [complexCoeff_apply, hzero, Complex.ofReal_zero])
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    exact hnreal (by simp [arithmeticDyadicBlock])
  have hlog : Nat.log 2 n = q := by
    by_contra hne
    exact hnreal (by simp [arithmeticDyadicBlock, hne])
  have hnX : n ≤ X := by
    by_contra hnot
    have hzero := coeffTrunc_apply_of_lt ArithmeticFunction.log
      (Nat.lt_of_not_ge hnot)
    rw [arithmeticDyadicBlock_apply, if_pos hlog, hzero] at hnreal
    exact hnreal rfl
  have hedges := (Nat.log_eq_iff (Or.inr ⟨by norm_num, hn0⟩)).mp hlog
  exact Finset.mem_Ico.mpr
    ⟨hedges.1, lt_min (Nat.lt_succ_iff.mpr hnX) hedges.2⟩

/-- Exact finite sum represented by a sharply truncated zeta dyadic block. -/
theorem LSeries_zetaDyadicBlock_eq_sum_Ico
    (X q : ℕ) (σ t : ℝ) :
    LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
        ((σ : ℂ) + (t : ℂ) * Complex.I) =
      ∑ n ∈ Finset.Ico (2 ^ q) (heathBrownDyadicFactorTop X q),
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ)) := by
  rw [← sum_mul_cpow_neg_eq_LSeries
    (s := Finset.Ico (2 ^ q) (heathBrownDyadicFactorTop X q))
    (by simp [Finset.mem_Ico])
    (complexCoeff_zetaDyadicBlock_support_Ico X q)]
  apply Finset.sum_congr rfl
  intro n hn
  have hnmem := Finset.mem_Ico.mp hn
  have hn0 : n ≠ 0 := by
    have : 1 ≤ 2 ^ q := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero q (by norm_num))
    omega
  have hnX : n ≤ X := by
    have hlt : n < X + 1 := hnmem.2.trans_le (min_le_left _ _)
    omega
  have hlog : Nat.log 2 n = q :=
    (Nat.log_eq_iff (Or.inr ⟨by norm_num, hn0⟩)).mpr
      ⟨hnmem.1, hnmem.2.trans_le (min_le_right _ _)⟩
  simp only [complexCoeff_apply, arithmeticDyadicBlock_apply, hlog, if_pos,
    coeffTrunc_apply_of_le (zeta : ArithmeticFunction ℝ) hnX]
  rw [show (zeta : ArithmeticFunction ℝ) n = 1 by simp [hn0]]
  simp only [Complex.ofReal_one, one_mul]
  congr 1
  ring

/-- Exact finite sum represented by a sharply truncated logarithm dyadic block. -/
theorem LSeries_logDyadicBlock_eq_sum_Ico
    (X q : ℕ) (σ t : ℝ) :
    LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((σ : ℂ) + (t : ℂ) * Complex.I) =
      ∑ n ∈ Finset.Ico (2 ^ q) (heathBrownDyadicFactorTop X q),
        (Real.log (n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ)) := by
  rw [← sum_mul_cpow_neg_eq_LSeries
    (s := Finset.Ico (2 ^ q) (heathBrownDyadicFactorTop X q))
    (by simp [Finset.mem_Ico])
    (complexCoeff_logDyadicBlock_support_Ico X q)]
  apply Finset.sum_congr rfl
  intro n hn
  have hnmem := Finset.mem_Ico.mp hn
  have hn0 : n ≠ 0 := by
    have : 1 ≤ 2 ^ q := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero q (by norm_num))
    omega
  have hnX : n ≤ X := by
    have hlt : n < X + 1 := hnmem.2.trans_le (min_le_left _ _)
    omega
  have hlog : Nat.log 2 n = q :=
    (Nat.log_eq_iff (Or.inr ⟨by norm_num, hn0⟩)).mpr
      ⟨hnmem.1, hnmem.2.trans_le (min_le_right _ _)⟩
  simp only [complexCoeff_apply, arithmeticDyadicBlock_apply, hlog, if_pos,
    coeffTrunc_apply_of_le ArithmeticFunction.log hnX, ArithmeticFunction.log_apply]
  congr 2
  ring

/-- Abel inequality for an increasing nonnegative weight.  Uniform prefix control costs at most
twice the terminal weight. -/
theorem abel_block_bound_increasing
    (a : ℕ → ℂ) (w : ℕ → ℝ) (N M : ℕ) (hNM : N ≤ M)
    (hwN : 0 ≤ w N) (hwM : 0 ≤ w M)
    (hmono : ∀ m, N ≤ m → m < M → w m ≤ w (m + 1))
    (P : ℝ) (hP : ∀ m, N ≤ m → m ≤ M → ‖∑ n ∈ Finset.Ico N m, a n‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico N M, ((w n : ℝ) : ℂ) * a n‖ ≤ 2 * P * w M := by
  rw [sum_weight_mul_eq_abel a w N M hNM]
  have hP0 : 0 ≤ P := le_trans (norm_nonneg _) (hP N le_rfl hNM)
  have hterm : ∀ m ∈ Finset.Ico N M,
      ‖((w m - w (m + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico N (m + 1), a n)‖
        ≤ (w (m + 1) - w m) * P := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hdw : w m - w (m + 1) ≤ 0 := sub_nonpos.mpr (hmono m hm.1 hm.2)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hdw]
    simpa only [neg_sub] using
      (mul_le_mul_of_nonneg_left (hP (m + 1) (by omega) (by omega))
        (sub_nonneg.mpr (hmono m hm.1 hm.2)))
  have htel : ∑ m ∈ Finset.Ico N M, (w (m + 1) - w m) = w M - w N := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h := Finset.sum_range_sub' (fun i => -w (N + i)) (M - N)
    rw [show N + 0 = N by omega, show N + (M - N) = M by omega] at h
    simpa only [Nat.add_assoc, neg_sub_neg] using h
  calc
    ‖(∑ m ∈ Finset.Ico N M,
          ((w m - w (m + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico N (m + 1), a n))
        + ((w M : ℝ) : ℂ) * ∑ n ∈ Finset.Ico N M, a n‖
      ≤ ‖∑ m ∈ Finset.Ico N M,
          ((w m - w (m + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico N (m + 1), a n)‖
        + ‖((w M : ℝ) : ℂ) * ∑ n ∈ Finset.Ico N M, a n‖ := norm_add_le _ _
    _ ≤ (∑ m ∈ Finset.Ico N M, (w (m + 1) - w m) * P) + w M * P := by
      have h1 := le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
      have h2 : ‖((w M : ℝ) : ℂ) * ∑ n ∈ Finset.Ico N M, a n‖ ≤ w M * P := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwM]
        exact mul_le_mul_of_nonneg_left (hP M hNM le_rfl) hwM
      linarith
    _ = (w M - w N) * P + w M * P := by rw [← Finset.sum_mul, htel]
    _ ≤ 2 * P * w M := by nlinarith

/-- Increasing logarithmic weight costs only `2 log M`. -/
theorem dirichlet_block_log_sigma_bound
    {σ : ℝ} (t : ℝ) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (P : ℝ)
    (hP : ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico N m,
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico N M, (Real.log (n : ℝ) : ℂ) *
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2 * P * Real.log (M : ℝ) := by
  apply abel_block_bound_increasing
    (fun n => (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ)))
    (fun n => Real.log (n : ℝ)) N M hNM
  · exact Real.log_nonneg (by exact_mod_cast hN)
  · exact Real.log_nonneg (by exact_mod_cast hN.trans hNM)
  · intro m hm _
    apply Real.log_le_log
    · have : 1 ≤ m := hN.trans hm
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
    · exact_mod_cast Nat.le_succ m
  · exact hP

/-- Derivative-test power saving with one logarithmic coefficient. -/
theorem dirichlet_block_log_sigma_saving_of_small_factorial
    {σ : ℝ} (hσ : 0 ≤ σ) {t : ℝ} (ht : 0 < t)
    {N M k₀ : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N + 1)
    (hk₀ : 2 ≤ k₀) (hfac : Nat.factorial (k₀ - 1) ≤ N)
    (hlow : 8 * Real.pi * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * (N : ℝ) ^ (k₀ - 1) *
      (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, (Real.log (n : ℝ) : ℂ) *
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 5120 * (N : ℝ) ^ (1 - σ) *
        (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) * Real.log (M : ℝ) := by
  have hprefix : ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico N m,
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
        ≤ 2560 * (N : ℝ) ^ (1 - σ) *
          (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
    intro m hNm hmM
    exact dirichlet_block_sigma_saving_of_small_factorial hσ ht hN hNm
      (hmM.trans hM) hk₀ hfac hlow hhigh
  have h := dirichlet_block_log_sigma_bound t N M hN hNM _ hprefix
  convert h using 1 <;> ring

/-- Pointwise derivative-test saving for a dyadic zeta factor in the Heath--Brown packet. -/
theorem norm_LSeries_zetaDyadicBlock_le
    {X q k₀ : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X)
    {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ 2 ^ q)
    (hlow : 8 * Real.pi * ((2 ^ q : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * ((2 ^ q : ℕ) : ℝ) ^ (k₀ - 1) *
      ((2 ^ q : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2560 * ((2 ^ q : ℕ) : ℝ) ^ (1 - σ) *
        ((2 ^ q : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
  rw [LSeries_zetaDyadicBlock_eq_sum_Ico]
  exact dirichlet_block_sigma_saving_of_small_factorial hσ ht
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero q (by norm_num)))
    (pow_le_heathBrownDyadicFactorTop hX hq)
    (heathBrownDyadicFactorTop_le_two_mul_add_one X q) hk₀ hfac hlow hhigh

/-- Pointwise derivative-test saving for the logarithm factor in the Heath--Brown packet. -/
theorem norm_LSeries_logDyadicBlock_le
    {X q k₀ : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X)
    {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ 2 ^ q)
    (hlow : 8 * Real.pi * ((2 ^ q : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * ((2 ^ q : ℕ) : ℝ) ^ (k₀ - 1) *
      ((2 ^ q : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 5120 * ((2 ^ q : ℕ) : ℝ) ^ (1 - σ) *
        ((2 ^ q : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) *
          Real.log (heathBrownDyadicFactorTop X q : ℝ) := by
  rw [LSeries_logDyadicBlock_eq_sum_Ico]
  exact dirichlet_block_log_sigma_saving_of_small_factorial hσ ht
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero q (by norm_num)))
    (pow_le_heathBrownDyadicFactorTop hX hq)
    (heathBrownDyadicFactorTop_le_two_mul_add_one X q) hk₀ hfac hlow hhigh

end RHTower.Sieve
