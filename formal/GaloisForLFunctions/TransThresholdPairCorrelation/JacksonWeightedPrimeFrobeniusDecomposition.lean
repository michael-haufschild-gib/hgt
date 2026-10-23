import GaloisForLFunctions.RHTower.ZetaWeightedFrobeniusClose

/-!
# Global Jackson-Weighted Prime–Prime Frobenius Decomposition and Close-Pair Reduction

In `ZetaWeightedFrobeniusClose` and `ZetaWeightedFrobeniusFar`, each individual pair `(n, m)` in the
Jackson-weighted prime–prime Frobenius expansion is analyzed on the grid `τ_k = T + k h`, `h = 2π/L`.
This module assembles the global prime–prime Frobenius theorem across an arbitrary finite index set `s`:

1. **Compact frequency support of `jacksonPairKernel` (`jacksonPairKernel_eq_zero_of_le_abs`):**
   Because the product of a shifted Jackson window with itself is band-limited to `(-4b, 4b)`
   (`integral_jacksonProduct_mul_cexp_eq_zero`), the continuous close-pair kernel
   `K_r(θ) = jacksonPairKernel b s₀ s₁ L r θ` vanishes identically whenever `4b ≤ |θ|`.
   Consequently, the continuous kernel sum over all pairs `(n, m) ∈ s × s` reduces identically to
   the close pairs `|y_n − y_m| < 4b` (`sum_jacksonCloseApprox_eq_close`).
2. **Automatic alias separation on `[2b, L/2 − 2b]` (`alias_sep_diff_of_mem_Icc`,
   `alias_sep_sum_of_mem_Icc`):**
   For frequencies `y, y' ∈ [2b, L/2 − 2b]`, `y − y'` is at distance `≥ 4b` from every non-zero
   grid alias `jL` (`j ≠ 0`) and `y + y'` is at distance `≥ 4b` from every grid alias `jL` (`j ∈ ℤ`).
3. **Global prime–prime Frobenius reduction with factored outer-mass error
   (`abs_weighted_frobenius_pp_sub_closeKernel_le`):**
   The full Jackson-weighted prime–prime Frobenius sum
   `∑_{k,l ∈ [0,d)} W_k W_l (∑_{n ∈ s} c_n Re(e^{i y_n τ_l} A_n(k − l)))²`
   differs from the close-pair continuous kernel sum by at most the factored outer Jackson mass
   `jacksonOuterErr b L M * ∑_{|r| < d} (∑_{n ∈ s} |c_n| ‖A_n(r)‖)²`.
-/

open Complex MeasureTheory Real Set Finset RHTower RHTower.FejerWeight
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

variable {b s₀ s₁ : ℝ}

/-! ## Compact support of `jacksonPairKernel` and close-pair reduction -/

/-- **The continuous close-pair kernel `jacksonPairKernel b s₀ s₁ L r θ` vanishes for `4b ≤ |θ|`.** -/
theorem jacksonPairKernel_eq_zero_of_le_abs (hb : 0 < b) (h01 : s₀ ≤ s₁) (L : ℝ) (r : ℤ)
    {θ : ℝ} (hθ : 4 * b ≤ |θ|) :
    jacksonPairKernel b s₀ s₁ L r θ = 0 := by
  unfold jacksonPairKernel
  have hη : 4 * b ≤ |-θ| := by rwa [abs_neg]
  have hz := integral_jacksonProduct_mul_cexp_eq_zero hb h01 (r * (2 * π / L)) hη
  have hcongr : (∫ s, ((jacksonWindow b s₀ s₁ (s + r * (2 * π / L))
        * jacksonWindow b s₀ s₁ s : ℝ) : ℂ) * cexp (I * θ * s))
      = ∫ s, ((jacksonWindow b s₀ s₁ (s + r * (2 * π / L))
        * jacksonWindow b s₀ s₁ s : ℝ) : ℂ) * cexp (-(I * ((-θ : ℝ) : ℂ) * s)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    congr 2
    push_cast
    ring
  rw [hcongr, hz, mul_zero]

/-- The continuous kernel approximation for a prime pair `(y, A)` and `(y', A')`:
`½ Re ∑_{|r|<d} A(r) conj(A'(r)) K_r(y − y')`. -/
def jacksonCloseApprox (b s₀ s₁ L : ℝ) (d : ℕ) (y : ℝ) (A : ℤ → ℂ) (y' : ℝ) (A' : ℤ → ℂ) : ℝ :=
  (∑ r ∈ Finset.Ioo (-(d : ℤ)) d,
    A r * starRingEnd ℂ (A' r) * jacksonPairKernel b s₀ s₁ L r (y - y')).re / 2

/-- The outer Jackson mass error factor `2 E₀`. -/
def jacksonOuterErr (b L M : ℝ) : ℝ :=
  2 * ((jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2)))

/-- When `4b ≤ |y − y'|`, `jacksonCloseApprox` vanishes identically. -/
theorem jacksonCloseApprox_eq_zero_of_le_abs (hb : 0 < b) (h01 : s₀ ≤ s₁) (L : ℝ) (d : ℕ)
    {y y' : ℝ} (hθ : 4 * b ≤ |y - y'|) (A A' : ℤ → ℂ) :
    jacksonCloseApprox b s₀ s₁ L d y A y' A' = 0 := by
  unfold jacksonCloseApprox
  have hz : ∀ r ∈ Finset.Ioo (-(d : ℤ)) d,
      A r * starRingEnd ℂ (A' r) * jacksonPairKernel b s₀ s₁ L r (y - y') = 0 := by
    intro r _
    rw [jacksonPairKernel_eq_zero_of_le_abs hb h01 L r hθ, mul_zero]
  rw [Finset.sum_eq_zero hz, Complex.zero_re, zero_div]

/-- **Exact support reduction to close pairs `|y_n − y_m| < 4b`:**
the double sum of `jacksonCloseApprox` over all `(n, m) ∈ s × s` equals the sum restricted to
close pairs `|y_n − y_m| < 4b`. -/
theorem sum_jacksonCloseApprox_eq_close {ι : Type*} (hb : 0 < b) (h01 : s₀ ≤ s₁) (L : ℝ) (d : ℕ)
    (s : Finset ι) (c : ι → ℝ) (y : ι → ℝ) (A : ι → ℤ → ℂ) :
    (∑ n ∈ s, ∑ m ∈ s, c n * c m * jacksonCloseApprox b s₀ s₁ L d (y n) (A n) (y m) (A m))
      = ∑ n ∈ s, ∑ m ∈ s,
          if |y n - y m| < 4 * b then
            c n * c m * jacksonCloseApprox b s₀ s₁ L d (y n) (A n) (y m) (A m)
          else 0 := by
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  by_cases h : |y n - y m| < 4 * b
  · rw [if_pos h]
  · rw [if_neg h, jacksonCloseApprox_eq_zero_of_le_abs hb h01 L d (not_lt.mp h), mul_zero]

/-! ## Automatic alias separation on the frequency band `[2b, L/2 − 2b]` -/

/-- For `y, y' ∈ [2b, L − 2b]`, the difference `y − y'` is separated by at least `4b` from every
non-zero grid alias `jL` (`j ≠ 0`). -/
theorem alias_sep_diff_of_mem_Icc {b L y y' : ℝ} (hb : 0 < b)
    (hy : y ∈ Icc (2 * b) (L - 2 * b)) (hy' : y' ∈ Icc (2 * b) (L - 2 * b))
    {j : ℤ} (hj : j ≠ 0) :
    4 * b ≤ |j * L - (y - y')| := by
  have hL : 0 < L := by linarith [hy.1, hy.2]
  have hdiff : |y - y'| ≤ L - 4 * b :=
    abs_le.mpr ⟨by linarith [hy.1, hy'.2], by linarith [hy.2, hy'.1]⟩
  have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hj
  have hjL : L ≤ |j * L| := by
    rw [abs_mul, abs_of_pos hL]
    exact le_mul_of_one_le_left hL.le hj1
  have htri : |j * L| - |y - y'| ≤ |j * L - (y - y')| := abs_sub_abs_le_abs_sub _ _
  linarith

/-- For `y, y' ∈ [2b, L/2 − 2b]`, the sum `y + y'` is separated by at least `4b` from every
grid alias `jL` (`j ∈ ℤ`). -/
theorem alias_sep_sum_of_mem_Icc {b L y y' : ℝ} (hb : 0 < b)
    (hy : y ∈ Icc (2 * b) (L / 2 - 2 * b)) (hy' : y' ∈ Icc (2 * b) (L / 2 - 2 * b))
    (j : ℤ) :
    4 * b ≤ |j * L - (y + y')| := by
  have hL : 0 < L := by linarith [hy.1, hy.2]
  have hsum_lo : 4 * b ≤ y + y' := by linarith [hy.1, hy'.1]
  have hsum_hi : y + y' ≤ L - 4 * b := by linarith [hy.2, hy'.2]
  rcases le_or_gt j 0 with hj | hj
  · have hj0 : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    have hjL : (j : ℝ) * L ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hj0 hL.le
    have hneg : j * L - (y + y') ≤ -(4 * b) := by linarith
    have habs : -(j * L - (y + y')) ≤ |j * L - (y + y')| := neg_le_abs _
    linarith
  · have hj1 : 1 ≤ j := hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hjL : L ≤ (j : ℝ) * L := le_mul_of_one_le_left hL.le hjR
    have hpos : 4 * b ≤ j * L - (y + y') := by linarith
    exact hpos.trans (le_abs_self _)

/-! ## Global Jackson-weighted prime–prime Frobenius theorem -/

/-- Exact factorization of the double sum of products of norms into a sum of squares. -/
theorem sum_sum_mul_sum_norm_eq {ι : Type*} (s : Finset ι) (R : Finset ℤ) (c : ι → ℝ)
    (A : ι → ℤ → ℂ) (E : ℝ) :
    (∑ n ∈ s, ∑ m ∈ s, |c n| * |c m| * ((∑ r ∈ R, ‖A n r‖ * ‖A m r‖) * E))
      = E * ∑ r ∈ R, (∑ n ∈ s, |c n| * ‖A n r‖) ^ 2 := by
  have h1 : ∀ n m : ι,
      |c n| * |c m| * ((∑ r ∈ R, ‖A n r‖ * ‖A m r‖) * E)
        = ∑ r ∈ R, E * ((|c n| * ‖A n r‖) * (|c m| * ‖A m r‖)) := by
    intro n m
    rw [← mul_assoc, mul_comm _ E, mul_assoc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext m
    rw [Finset.sum_comm]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]

/-- **Global Jackson-weighted prime–prime Frobenius decomposition:**
For any finite index set `s`, real coefficients `c_n`, frequencies `y_n` avoiding the non-zero
difference aliases and all sum aliases, and shift profiles `A_n(r)`, the full Jackson-weighted
prime–prime Frobenius sum equals the close-pair continuous kernel sum up to the factored outer
Jackson mass `jacksonOuterErr b L M * ∑_{|r|<d} (∑_{n∈s} |c_n| ‖A_n(r)‖)²`. -/
theorem abs_weighted_frobenius_pp_sub_closeKernel_le {ι : Type*}
    (hb : 0 < b) (h01 : s₀ ≤ s₁) {L T M : ℝ} (hL : 0 < L) (hM : 0 < M) (d : ℕ)
    (hs₀ : T + M ≤ s₀) (hs₁ : s₁ + M ≤ T + d * (2 * π / L))
    (s : Finset ι) (c : ι → ℝ) (y : ι → ℝ) (A : ι → ℤ → ℂ)
    (hminus : ∀ n ∈ s, ∀ m ∈ s, ∀ j : ℤ, j ≠ 0 → 4 * b ≤ |j * L - (y n - y m)|)
    (hplus : ∀ n ∈ s, ∀ m ∈ s, ∀ j : ℤ, 4 * b ≤ |j * L - (y n + y m)|) :
    |∑ k ∈ Finset.Ico (0 : ℤ) d, ∑ l ∈ Finset.Ico (0 : ℤ) d,
        jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) * jacksonWindow b s₀ s₁ (T + l * (2 * π / L))
          * (∑ n ∈ s, c n * (cexp (I * y n * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A n (k - l)).re) ^ 2
      - ∑ n ∈ s, ∑ m ∈ s,
          if |y n - y m| < 4 * b then
            c n * c m * jacksonCloseApprox b s₀ s₁ L d (y n) (A n) (y m) (A m)
          else 0|
      ≤ jacksonOuterErr b L M
          * ∑ r ∈ Finset.Ioo (-(d : ℤ)) d, (∑ n ∈ s, |c n| * ‖A n r‖) ^ 2 := by
  rw [← sum_jacksonCloseApprox_eq_close hb h01 L d s c y A]
  have hexp := weighted_sq_sum_mul_re_eq (Finset.Ico (0 : ℤ) d) s
    (fun k : ℤ => jacksonWindow b s₀ s₁ (T + k * (2 * π / L))) c
    (fun n k l => cexp (I * y n * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A n (k - l))
  rw [hexp, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun n hn => ?_).trans
    (le_of_eq (sum_sum_mul_sum_norm_eq s (Finset.Ioo (-(d : ℤ)) d) c A (jacksonOuterErr b L M)))
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [ ← mul_sub, abs_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact abs_weighted_close_pair_sub_le hb h01 hL hM d hs₀ hs₁
    (hminus n hn m hm) (hplus n hn m hm) (A n) (A m)

end GaloisForLFunctions.TransThresholdPairCorrelation
