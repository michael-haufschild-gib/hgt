import GaloisForLFunctions.BiarithmeticGeometry.GeometricFutureTail
import Mathlib.Analysis.Complex.Basic

/-!
# Exact division by an expanding one-prime factor

A causal geometric response at ratio greater than one has finite square
energy exactly when the coefficient series vanishes at the reciprocal ratio.
On that evaluation kernel, the response is the negative geometric future
tail, with an explicit absolute-sum bound.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The finite complex causal response at a real geometric ratio. -/
def geometricCausalResponse (q : ℝ) (g : ℕ → ℂ) (M : ℕ) : ℂ :=
  ∑ r ∈ range (M + 1), (q : ℂ) ^ (M - r) * g r

theorem geometricCausalResponse_zero (q : ℝ) (g : ℕ → ℂ) :
    geometricCausalResponse q g 0 = g 0 := by simp [geometricCausalResponse]

theorem geometricCausalResponse_succ (q : ℝ) (g : ℕ → ℂ) (M : ℕ) :
    geometricCausalResponse q g (M + 1) =
      (q : ℂ) * geometricCausalResponse q g M + g (M + 1) := by
  rw [geometricCausalResponse, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  rw [geometricCausalResponse, mul_sum]
  apply sum_congr rfl
  intro r hr
  rw [show M + 1 - r = (M - r) + 1 by have := mem_range.mp hr; omega, pow_succ]
  ring

/-- Factoring the causal response gives its exact finite pole sum. -/
theorem geometricCausalResponse_eq_partialPoleSum (q : ℝ) (hq : q ≠ 0)
    (g : ℕ → ℂ) (M : ℕ) :
    geometricCausalResponse q g M = (q : ℂ) ^ M *
      ∑ r ∈ range (M + 1), g r / (q : ℂ) ^ r := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  rw [geometricCausalResponse, mul_sum]
  apply sum_congr rfl
  intro r hr
  have hrM : r ≤ M := by have := mem_range.mp hr; omega
  have hp : (q : ℂ) ^ M = (q : ℂ) ^ (M - r) * (q : ℂ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrM]
  rw [hp]
  field_simp [hqC]

/-- The pole-sum weight is precisely the squared norm of the causal response. -/
theorem norm_sq_geometricCausalResponse (q : ℝ) (hq : q ≠ 0)
    (g : ℕ → ℂ) (M : ℕ) :
    ‖geometricCausalResponse q g M‖ ^ 2 =
      (q ^ 2) ^ M * ‖∑ r ∈ range (M + 1), g r / (q : ℂ) ^ r‖ ^ 2 := by
  rw [geometricCausalResponse_eq_partialPoleSum q hq, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, mul_pow,
    ← pow_mul, Nat.mul_comm M 2, pow_mul, sq_abs]

private theorem summable_norm_geometricEvaluation {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖) :
    Summable (fun r : ℕ => ‖(b : ℂ) ^ r * g r‖) := by
  apply hg.of_nonneg_of_le (fun r => norm_nonneg _)
  intro r
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hb0 hb1)

/-- The reciprocal evaluation is the initial coefficient plus its future tail. -/
theorem geometricEvaluation_eq_initial_add_tail {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖) :
    (∑' r : ℕ, (b : ℂ) ^ r * g r) = g 0 + geometricFutureTail b g 0 := by
  rw [((summable_norm_geometricEvaluation hb0 hb1.le hg).of_norm).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, geometricFutureTail, Nat.zero_add]

/-- Vanishing evaluation identifies the causal response with the negative future tail. -/
theorem geometricCausalResponse_eq_neg_futureTail {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖)
    (he : (∑' r : ℕ, (b : ℂ) ^ r * g r) = 0) (M : ℕ) :
    geometricCausalResponse b⁻¹ g M = -geometricFutureTail b g M := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  induction M with
  | zero =>
    rw [geometricCausalResponse_zero]
    rw [geometricEvaluation_eq_initial_add_tail hb0.le hb1 hg] at he
    exact eq_neg_of_add_eq_zero_left he
  | succ M ih =>
    rw [geometricCausalResponse_succ, ih, Complex.ofReal_inv]
    rw [geometricFutureTail_recurrence hb0.le hb1 hg M]
    field_simp [hbC]
    ring

/-- Absolute summability implies square summability, with no boundedness premise. -/
theorem summable_norm_sq_of_summable_norm {u : ℕ → ℂ}
    (hu : Summable fun n => ‖u n‖) : Summable (fun n => ‖u n‖ ^ 2) := by
  have hb (n : ℕ) : ‖u n‖ ≤ ∑' m, ‖u m‖ := by
    simpa only [sum_singleton] using
      sum_le_hasSum ({n} : Finset ℕ) (fun m _ => norm_nonneg (u m)) hu.hasSum
  apply (hu.mul_right (∑' m, ‖u m‖)).of_nonneg_of_le (fun n => sq_nonneg _)
  intro n
  rw [pow_two]
  exact mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _)

private theorem geometricEvaluation_partialSum {b : ℝ} (hb : b ≠ 0)
    (g : ℕ → ℂ) (M : ℕ) :
    (∑ r ∈ range (M + 1), (b : ℂ) ^ r * g r) =
      (b : ℂ) ^ M * geometricCausalResponse b⁻¹ g M := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  induction M with
  | zero => simp [geometricCausalResponse_zero]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, geometricCausalResponse_succ, pow_succ, Complex.ofReal_inv]
    field_simp [hbC]

/-- Square energy forces vanishing of the interior reciprocal evaluation. -/
theorem geometricEvaluation_zero_of_summable_response {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖)
    (hS : Summable fun M => ‖geometricCausalResponse b⁻¹ g M‖ ^ 2) :
    (∑' r : ℕ, (b : ℂ) ^ r * g r) = 0 := by
  have hn : Tendsto (fun M => ‖geometricCausalResponse b⁻¹ g M‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hS.tendsto_atTop_zero.sqrt
  have hS0 : Tendsto (geometricCausalResponse b⁻¹ g) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using hn
  have hp : Tendsto (fun M : ℕ => (b : ℂ) ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0])
  have hzero : Tendsto (fun M : ℕ => ∑ r ∈ range (M + 1), (b : ℂ) ^ r * g r)
      atTop (𝓝 0) := by
    simpa only [geometricEvaluation_partialSum hb0.ne', mul_zero] using hp.mul hS0
  have hsum : Tendsto (fun M : ℕ => ∑ r ∈ range (M + 1), (b : ℂ) ^ r * g r)
      atTop (𝓝 (∑' r : ℕ, (b : ℂ) ^ r * g r)) :=
    (summable_norm_geometricEvaluation hb0.le hb1.le hg).of_norm.hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hsum hzero

/-- The strict expanding response domain is precisely one continuous evaluation kernel. -/
theorem summable_sq_geometricCausalResponse_iff {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖) :
    Summable (fun M => ‖geometricCausalResponse b⁻¹ g M‖ ^ 2) ↔
      (∑' r : ℕ, (b : ℂ) ^ r * g r) = 0 := by
  constructor
  · exact geometricEvaluation_zero_of_summable_response hb0 hb1 hg
  · intro he
    simp only [geometricCausalResponse_eq_neg_futureTail hb0 hb1 hg he, norm_neg]
    exact summable_norm_sq_of_summable_norm (summable_norm_geometricFutureTail hb0.le hb1 hg)

/-- On the evaluation kernel, the causal response has the explicit absolute-sum bound. -/
theorem tsum_norm_geometricCausalResponse_le {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖)
    (he : (∑' r : ℕ, (b : ℂ) ^ r * g r) = 0) :
    (∑' M, ‖geometricCausalResponse b⁻¹ g M‖) ≤ (b / (1 - b)) * ∑' r, ‖g r‖ := by
  simp only [geometricCausalResponse_eq_neg_futureTail hb0 hb1 hg he, norm_neg]
  exact tsum_norm_geometricFutureTail_le hb0.le hb1 hg

end GaloisForLFunctions.BiarithmeticGeometry

