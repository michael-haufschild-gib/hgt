import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffSaddle
import GaloisForLFunctions.RHTower.GammaDampedVerticalBound
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summation of the Hausdorff saddle tails

Finite fiber estimates suffice for absolutely convergent zero sums. A
linear shell count is absorbed by half of a geometric exponential.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

open scoped BigOperators

def gaussianSumConstant : ℝ := 64 * (1 - Real.exp (-(1 / 64 : ℝ)))⁻¹

theorem gaussianSumConstant_pos : 0 < gaussianSumConstant := by
  have h : Real.exp (-(1 / 64 : ℝ)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  unfold gaussianSumConstant
  positivity

/-- The linear count factor consumes only half the exponential decay. -/
theorem linear_mul_exp_le (n : ℕ) :
    ((n : ℝ) + 1) * Real.exp (-(n : ℝ) / 32) ≤ 64 * Real.exp (-(n : ℝ) / 64) := by
  have h := Real.add_one_le_exp ((n : ℝ) / 64)
  have hlinear : (n : ℝ) + 1 ≤ 64 * Real.exp ((n : ℝ) / 64) := by linarith only [h]
  have hmul := mul_le_mul_of_nonneg_right hlinear (Real.exp_pos (-(n : ℝ) / 32)).le
  have heq : Real.exp ((n : ℝ) / 64) * Real.exp (-(n : ℝ) / 32) =
      Real.exp (-(n : ℝ) / 64) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith only [hmul, heq]

/-- A shell count bounded by `B(n+1)` sums uniformly against the Gaussian majorant. -/
theorem sum_le_gaussianSumConstant {α : Type*} (F : Finset α) (index : α → ℕ)
    (f : α → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcard : ∀ n : ℕ, ((F.filter (fun q => index q = n)).card : ℝ) ≤ B * ((n : ℝ) + 1))
    (hterm : ∀ q ∈ F, f q ≤ A * Real.exp (-(index q : ℝ) / 32)) :
    ∑ q ∈ F, f q ≤ A * B * gaussianSumConstant := by
  classical
  have hq : ‖Real.exp (-(1 / 64 : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hsum := summable_geometric_of_norm_lt_one hq
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩ : ∀ q ∈ F, index q ∈ F.image index) f
  rw [← hgroup]
  calc
    _ ≤ ∑ n ∈ F.image index, (64 * A * B) * Real.exp (-(1 / 64 : ℝ)) ^ n := by
      apply Finset.sum_le_sum
      intro n _
      have hf : ∑ q ∈ F.filter (fun q => index q = n), f q ≤
          ((F.filter (fun q => index q = n)).card : ℝ) * (A * Real.exp (-(n : ℝ) / 32)) := by
        calc
          _ ≤ ∑ _q ∈ F.filter (fun q => index q = n), A * Real.exp (-(n : ℝ) / 32) := by
            apply Finset.sum_le_sum
            intro q hq
            obtain ⟨hqF, hqn⟩ := Finset.mem_filter.mp hq
            simpa only [hqn] using hterm q hqF
          _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
      have hc := mul_le_mul_of_nonneg_right (hcard n)
        (show 0 ≤ A * Real.exp (-(n : ℝ) / 32) by positivity)
      have hg := mul_le_mul_of_nonneg_left (linear_mul_exp_le n) (mul_nonneg hA hB)
      have heq : Real.exp (-(1 / 64 : ℝ)) ^ n = Real.exp (-(n : ℝ) / 64) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [heq]
      nlinarith only [hf, hc, hg]
    _ ≤ ∑' n : ℕ, (64 * A * B) * Real.exp (-(1 / 64 : ℝ)) ^ n :=
      Summable.sum_le_tsum _ (fun _ _ => by positivity) (hsum.mul_left (64 * A * B))
    _ = A * B * gaussianSumConstant := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq]
      unfold gaussianSumConstant
      ring

/-- Extract a uniform `4⁻p` factor from every power tail starting at four. -/
theorem inv_pow_le_four_inv_pow {p n : ℕ} (hp : 4 ≤ p) (hn : 4 ≤ n) :
    (n : ℝ)⁻¹ ^ p ≤ 256 * (4 : ℝ)⁻¹ ^ p * (n : ℝ)⁻¹ ^ 4 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hbase : (n : ℝ)⁻¹ ≤ (4 : ℝ)⁻¹ :=
    (inv_le_inv₀ hn0 (by norm_num)).mpr hnR
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hn0.le) hbase (p - 4)
  have hsplit : p = 4 + (p - 4) := by omega
  have h4 : (4 : ℝ)⁻¹ ^ (p - 4) = 256 * (4 : ℝ)⁻¹ ^ p := by
    have h := congrArg (fun j : ℕ => (4 : ℝ)⁻¹ ^ j) hsplit
    rw [pow_add] at h
    norm_num at h
    linarith only [h]
  calc
    _ = (n : ℝ)⁻¹ ^ 4 * (n : ℝ)⁻¹ ^ (p - 4) := by conv_lhs => rw [hsplit, pow_add]
    _ ≤ (n : ℝ)⁻¹ ^ 4 * (4 : ℝ)⁻¹ ^ (p - 4) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [h4]; ring

/-- A quadratic shell count sums uniformly against a power of order at least four. -/
theorem sum_le_power_tail {α : Type*} (F : Finset α) (index : α → ℕ)
    (f : α → ℝ) {A B : ℝ} {p : ℕ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 4 ≤ p)
    (hindex : ∀ q ∈ F, 4 ≤ index q)
    (hcard : ∀ n : ℕ, 4 ≤ n →
      ((F.filter (fun q => index q = n)).card : ℝ) ≤ B * ((n : ℝ) + 1) ^ 2)
    (hterm : ∀ q ∈ F, f q ≤ A * (index q : ℝ)⁻¹ ^ p) :
    ∑ q ∈ F, f q ≤ 2048 * A * B * (4 : ℝ)⁻¹ ^ p := by
  classical
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩ : ∀ q ∈ F, index q ∈ F.image index) f
  rw [← hgroup]
  have hfinite : ∑ n ∈ F.image index, ((n : ℝ) ^ 2)⁻¹ ≤ 2 := by
    exact (Summable.sum_le_tsum _ (fun _ _ => by positivity)
      _root_.RHTower.summable_inv_natCast_sq).trans _root_.RHTower.tsum_inv_natCast_sq_le
  calc
    _ ≤ ∑ n ∈ F.image index, (1024 * A * B * (4 : ℝ)⁻¹ ^ p) * ((n : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hnmem
      obtain ⟨q, hq, hqn⟩ := Finset.mem_image.mp hnmem
      have hn : 4 ≤ n := hqn ▸ hindex q hq
      have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith only [hnR]
      have hf : ∑ q ∈ F.filter (fun q => index q = n), f q ≤
          ((F.filter (fun q => index q = n)).card : ℝ) * (A * (n : ℝ)⁻¹ ^ p) := by
        calc
          _ ≤ ∑ _q ∈ F.filter (fun q => index q = n), A * (n : ℝ)⁻¹ ^ p := by
            apply Finset.sum_le_sum
            intro q hq
            obtain ⟨hqF, hqn⟩ := Finset.mem_filter.mp hq
            simpa only [hqn] using hterm q hqF
          _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
      have hc := mul_le_mul_of_nonneg_right (hcard n hn)
        (show 0 ≤ A * (n : ℝ)⁻¹ ^ p by positivity)
      have hpbound := mul_le_mul_of_nonneg_left (inv_pow_le_four_inv_pow hp hn)
        (show 0 ≤ A * B * ((n : ℝ) + 1) ^ 2 by positivity)
      have hquad : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith only [hnR]
      have hquad' := mul_le_mul_of_nonneg_right hquad
        (show 0 ≤ 256 * A * B * (4 : ℝ)⁻¹ ^ p * (n : ℝ)⁻¹ ^ 4 by positivity)
      have heq : (n : ℝ) ^ 2 * (n : ℝ)⁻¹ ^ 4 = ((n : ℝ) ^ 2)⁻¹ := by
        field_simp [hn0.ne']
      rw [show (4 * (n : ℝ) ^ 2) * (256 * A * B * (4 : ℝ)⁻¹ ^ p * (n : ℝ)⁻¹ ^ 4) =
        (1024 * A * B * (4 : ℝ)⁻¹ ^ p) * ((n : ℝ) ^ 2 * (n : ℝ)⁻¹ ^ 4) by ring,
        heq] at hquad'
      nlinarith only [hf, hc, hpbound, hquad']
    _ = (1024 * A * B * (4 : ℝ)⁻¹ ^ p) * ∑ n ∈ F.image index, ((n : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (1024 * A * B * (4 : ℝ)⁻¹ ^ p) * 2 :=
      mul_le_mul_of_nonneg_left hfinite (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
