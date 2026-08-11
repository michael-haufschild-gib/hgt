import GaloisForLFunctions.RHTower.Sieve.MaynardEligibleGreedySelection
import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicCoefficientBound
import GaloisForLFunctions.RHTower.Sieve.LSeriesTrivialSize

/-!
# Trivial size of low-total Heath--Brown boxes

One signed box is supported between its exact multiplicative edges `D` and `M=2^(2j)D`.
Keeping the lower-edge real-axis weight gives size `M^(1+epsilon) D^(-sigma) log M`, uniformly in
height.  This is the elementary bound needed to remove low-total boxes before Huxley selection.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

theorem one_le_heathBrownDyadicCoreLower
    (j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) :
    1 ≤ heathBrownDyadicCoreLower j a b q := by
  have ha : 0 < ∏ i, 2 ^ a i := by positivity
  have hb : 0 < ∏ i, 2 ^ b i := by positivity
  dsimp [heathBrownDyadicCoreLower]
  exact Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero ha.ne' hb.ne') (pow_ne_zero q (by norm_num)))

theorem one_le_heathBrownDyadicCoreUpper
    (j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) :
    1 ≤ heathBrownDyadicCoreUpper j a b q := by
  have ha : 0 < ∏ i, 2 ^ (a i + 1) := by positivity
  have hb : 0 < ∏ i, 2 ^ (b i + 1) := by positivity
  dsimp [heathBrownDyadicCoreUpper]
  exact Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero ha.ne' hb.ne') (pow_ne_zero (q + 1) (by norm_num)))

/-- Exact signed-box support lies in the closed interval between its multiplicative edges. -/
theorem complexCoeff_heathBrownDyadicTermBox_support_Icc_edges
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q n : ℕ)
    (hn : complexCoeff (heathBrownDyadicTermBox L X k m a b q) n ≠ 0) :
    n ∈ Finset.Icc (heathBrownDyadicCoreLower (k - m) a b q)
      (heathBrownDyadicCoreUpper (k - m) a b q) := by
  have hnreal : heathBrownDyadicTermBox L X k m a b q n ≠ 0 := by
    intro hzero
    apply hn
    simp [complexCoeff_apply, hzero]
  have hupper := upperSupported_heathBrownDyadicTermBox L X k m a b q n hnreal
  have hlower : heathBrownDyadicCoreLower (k - m) a b q ≤ n := by
    by_contra hnot
    have hlt : n < heathBrownDyadicCoreLower (k - m) a b q := Nat.lt_of_not_ge hnot
    exact hnreal (vanishesBelow_heathBrownDyadicTermBox L X k m a b q n hlt)
  exact Finset.mem_Icc.mpr ⟨hlower, (Finset.mem_Icc.mp hupper).2⟩

/-- **Uniform vertical-line bound for one signed dyadic box.** -/
theorem exists_norm_heathBrownDyadicTermProduct_le_edges
    {eps : ℝ} (heps : 0 < eps) (k m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L X : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
        (q : ℕ) {sigma y : ℝ}, 0 ≤ sigma →
        ‖heathBrownDyadicTermProduct L X k m a b q
          ((sigma : ℂ) + (y : ℝ) * I)‖ ≤
          (heathBrownDyadicCoreUpper (k - m) a b q : ℝ) *
            ((k.choose m : ℝ) * C *
              (heathBrownDyadicCoreUpper (k - m) a b q : ℝ) ^ eps *
              Real.log (heathBrownDyadicCoreUpper (k - m) a b q : ℝ) *
              (heathBrownDyadicCoreLower (k - m) a b q : ℝ) ^ (-sigma)) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_norm_complexCoeff_heathBrownDyadicTermBox_le_prefix_rpow_mul_log heps k m
  refine ⟨C, hC, ?_⟩
  intro L X a b q sigma y hsigma
  let D := heathBrownDyadicCoreLower (k - m) a b q
  let M := heathBrownDyadicCoreUpper (k - m) a b q
  let F := heathBrownDyadicTermBox L X k m a b q
  let A : ℝ := (k.choose m : ℝ) * C * (M : ℝ) ^ eps * Real.log (M : ℝ) *
    (D : ℝ) ^ (-sigma)
  have hD : 1 ≤ D := one_le_heathBrownDyadicCoreLower (k - m) a b q
  have hM : 1 ≤ M := one_le_heathBrownDyadicCoreUpper (k - m) a b q
  have hDM : D ≤ M := by
    dsimp [D, M, heathBrownDyadicCoreLower, heathBrownDyadicCoreUpper]
    gcongr <;> simp
  have hs0 : 0 ∉ Finset.Icc D M := by
    simp [Finset.mem_Icc]
    omega
  have hsupp : ∀ n : ℕ, complexCoeff F n ≠ 0 → n ∈ Finset.Icc D M := by
    intro n hn
    exact complexCoeff_heathBrownDyadicTermBox_support_Icc_edges L X k m a b q n hn
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    positivity
  have hterm : ∀ n ∈ Finset.Icc D M,
      ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) ≤ A := by
    intro n hn
    have hnI := Finset.mem_Icc.mp hn
    have hn1 : 1 ≤ n := hD.trans hnI.1
    have hc := hcoeff L X a b q M n hn1 hnI.2
    have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hD
    have hncast : (D : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnI.1
    have hw : (n : ℝ) ^ (-sigma) ≤ (D : ℝ) ^ (-sigma) :=
      Real.rpow_le_rpow_of_nonpos hDR hncast (by linarith)
    dsimp [F, A]
    exact mul_le_mul hc hw (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hC))
        (Real.rpow_nonneg (by positivity) _))
        (Real.log_nonneg (by exact_mod_cast hM)))
  have hcard : ((Finset.Icc D M).card : ℝ) ≤ (M : ℝ) := by
    norm_cast
    simp
    omega
  rw [← LSeries_heathBrownDyadicTermBox L X k m a b q]
  calc
    ‖LSeries (complexCoeff F) ((sigma : ℂ) + (y : ℝ) * I)‖
        ≤ ∑ n ∈ Finset.Icc D M, ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) :=
      norm_LSeries_le_sum_of_support hs0 hsupp sigma y
    _ ≤ ∑ _n ∈ Finset.Icc D M, A := Finset.sum_le_sum hterm
    _ = ((Finset.Icc D M).card : ℝ) * A := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * A := mul_le_mul_of_nonneg_right hcard hA0
    _ = (heathBrownDyadicCoreUpper (k - m) a b q : ℝ) *
          ((k.choose m : ℝ) * C *
            (heathBrownDyadicCoreUpper (k - m) a b q : ℝ) ^ eps *
            Real.log (heathBrownDyadicCoreUpper (k - m) a b q : ℝ) *
            (heathBrownDyadicCoreLower (k - m) a b q : ℝ) ^ (-sigma)) := rfl

end RHTower.Sieve
