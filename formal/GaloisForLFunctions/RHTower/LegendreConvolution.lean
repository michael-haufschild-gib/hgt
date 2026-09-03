import GaloisForLFunctions.RHTower.LegendreGeneratingFunction
import GaloisForLFunctions.RHTower.SemilocalBoostDiagonalClosedForm

/-!
# The central-binomial convolution form of the Legendre polynomials

`(1 − 2 cos φ · w + w²)^{−1/2} = (1 − w e^{iφ})^{−1/2} (1 − w e^{−iφ})^{−1/2}` and each factor is the
central-binomial series `Σ C_j u^j`, so the Cauchy product and coefficient uniqueness give

`P_N(cos φ) = Σ_{k=0}^{N} C_k C_{N−k} cos((N − 2k) φ)`,   `C_k = binom(2k,k)/4^k`.

This exact trigonometric form is the input of the Laplace–Heine asymptotics.
-/

open Finset Complex
open scoped BigOperators

namespace RHTower

namespace LegendreBoost

open ScaledHypergeometric RouteJProfile PowerSeriesUniqueness MeixnerPollaczek

theorem cb_zero : cb 0 = 1 := by simp [cb]

theorem cb_le_one (j : ℕ) : cb j ≤ 1 := by
  induction j with
  | zero => rw [cb_zero]
  | succ j ih =>
      rw [cb_succ]
      have h := cb_pos j
      calc cb j * (2 * (j : ℝ) + 1) / (2 * ((j : ℝ) + 1)) ≤ cb j * 1 := by
            rw [mul_div_assoc]
            apply mul_le_mul_of_nonneg_left _ h.le
            rw [div_le_one (by positivity)]
            linarith
        _ ≤ 1 := by linarith

/-- `((−½) choose j) (−1)^j = C_j` in `ℂ`. -/
theorem ringChoose_neg_half_mul_neg_one_pow_eq_cb (j : ℕ) :
    Ring.choose (-(1 / 2 : ℂ)) j * (-1) ^ j = (cb j : ℂ) := by
  rw [ringChoose_neg_half_mul_neg_one_pow]
  unfold cb
  rw [centralBinom_div_four_pow_eq_normalization_sq]
  push_cast
  ring

/-- The central-binomial series `Σ C_j u^j = (1 − u)^{−1/2}`. -/
theorem hasSum_cb_mul_pow {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum (fun j : ℕ => (cb j : ℂ) * u ^ j) ((1 - u) ^ (-(1 / 2 : ℂ))) := by
  have h := hasSum_one_sub_cpow_neg (1 / 2 : ℂ) hu
  refine h.congr_fun fun j => ?_
  rw [← ringChoose_neg_half_mul_neg_one_pow_eq_cb, neg_pow]
  ring

theorem summable_norm_cb_mul_pow {u : ℂ} (hu : ‖u‖ < 1) :
    Summable (fun j : ℕ => ‖(cb j : ℂ) * u ^ j‖) := by
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_geometric_of_lt_one (norm_nonneg u) hu)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cb_pos j)]
  exact mul_le_of_le_one_left (by positivity) (cb_le_one j)

theorem re_one_sub_mul_exp_pos {w : ℂ} (hw : ‖w‖ < 1 / 4) (t : ℝ) :
    0 < (1 - w * cexp ((t : ℂ) * I)).re := by
  have h : |(w * cexp ((t : ℂ) * I)).re| ≤ 1 / 4 := by
    calc |(w * cexp ((t : ℂ) * I)).re| ≤ ‖w * cexp ((t : ℂ) * I)‖ := abs_re_le_norm _
      _ = ‖w‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      _ ≤ 1 / 4 := hw.le
  simp only [sub_re, one_re]
  linarith [(abs_le.mp h).2]

/-- The factorization of the generating function at `x = cos φ`. -/
theorem legendreGen_cos_eq (φ : ℝ) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    legendreGen (Real.cos φ) w =
      (1 - w * cexp ((φ : ℂ) * I)) ^ (-(1 / 2 : ℂ)) * (1 - w * cexp (((-φ : ℝ) : ℂ) * I)) ^ (-(1 / 2 : ℂ)) := by
  unfold legendreGen
  have h2 : 2 * (Real.cos φ : ℂ) = cexp ((φ : ℂ) * I) + cexp (((-φ : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_cos, Complex.two_cos]
    push_cast
    ring_nf
  have h1 : cexp ((φ : ℂ) * I) * cexp (((-φ : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
    exact Complex.exp_zero
  have hprod : (1 - 2 * (Real.cos φ : ℂ) * w + w ^ 2) =
      (1 - w * cexp ((φ : ℂ) * I)) * (1 - w * cexp (((-φ : ℝ) : ℂ) * I)) := by
    linear_combination (-w) * h2 + (-(w ^ 2)) * h1
  rw [hprod, mul_cpow_of_re_pos (re_one_sub_mul_exp_pos hw φ) (re_one_sub_mul_exp_pos hw (-φ))]

/-- The convolution coefficient `Σ_{i+j=N} C_i C_j e^{i(i−j)φ}`. -/
noncomputable def legendreConvCoeff (φ : ℝ) (N : ℕ) : ℂ :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal N,
    (cb ij.1 : ℂ) * (cb ij.2 : ℂ) * cexp ((((ij.1 : ℝ) - (ij.2 : ℝ)) * φ : ℝ) * I)

theorem hasSum_legendreConvCoeff (φ : ℝ) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    HasSum (fun N : ℕ => legendreConvCoeff φ N * w ^ N) (legendreGen (Real.cos φ) w) := by
  have hu1 : ‖w * cexp ((φ : ℂ) * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; linarith
  have hu2 : ‖w * cexp (((-φ : ℝ) : ℂ) * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; linarith
  have hf := summable_norm_cb_mul_pow hu1
  have hg := summable_norm_cb_mul_pow hu2
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  rw [(hasSum_cb_mul_pow hu1).tsum_eq, (hasSum_cb_mul_pow hu2).tsum_eq] at hprod
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum
  rw [← hprod, ← legendreGen_cos_eq φ hw] at hsum
  refine hsum.congr_fun fun N => ?_
  unfold legendreConvCoeff
  rw [sum_mul]
  apply sum_congr rfl
  intro ij hij
  have hij' : ij.1 + ij.2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← hij', pow_add]
  have : cexp ((((ij.1 : ℝ) - (ij.2 : ℝ)) * φ : ℝ) * I) =
      cexp ((ij.1 : ℂ) * ((φ : ℂ) * I)) * cexp ((ij.2 : ℂ) * (((-φ : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [this]
  ring

/-- **`P_N(cos φ)` is the convolution coefficient.** -/
theorem legendre_cos_eq_conv (φ : ℝ) (N : ℕ) :
    (legendre N (Real.cos φ) : ℂ) = legendreConvCoeff φ N :=
  congrFun (eq_of_hasSum_mul_pow_eq (by norm_num : (0 : ℝ) < 1 / 4)
    (fun w hw => hasSum_legendreGen (abs_le.mpr ⟨by linarith [Real.neg_one_le_cos φ],
      Real.cos_le_one φ⟩) hw)
    (fun w hw => hasSum_legendreConvCoeff φ hw)) N

/-- **Real convolution form:** `P_N(cos φ) = Σ_{k ≤ N} C_k C_{N−k} cos((k − (N − k)) φ)`. -/
theorem legendre_cos_eq_sum (φ : ℝ) (N : ℕ) :
    legendre N (Real.cos φ) =
      ∑ k ∈ range (N + 1), cb k * cb (N - k) * Real.cos (((k : ℝ) - ((N - k : ℕ) : ℝ)) * φ) := by
  have h := congrArg Complex.re (legendre_cos_eq_conv φ N)
  rw [Complex.ofReal_re] at h
  rw [h]
  unfold legendreConvCoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Complex.re_sum]
  apply sum_congr rfl
  intro k _
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

end LegendreBoost

end RHTower
