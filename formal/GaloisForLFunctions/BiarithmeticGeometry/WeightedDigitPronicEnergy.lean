import GaloisForLFunctions.BiarithmeticGeometry.DigitPronicBlocks
import GaloisForLFunctions.BiarithmeticGeometry.FiniteGeometricConvolution
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exact energy domain of arbitrary signed digit rows

Complete digit blocks partition the positive integers. Their variance lower bound and
the finite geometric convolution estimate compare pronic energy with a weighted square sum.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Normalize a digit coefficient by its square-root block scale. -/
def fiveNormalizedDigitWeight (x : ℕ → ℝ) (l : ℕ) : ℝ := x l / Real.sqrt 5 ^ l

theorem sq_fiveNormalizedDigitWeight (x : ℕ → ℝ) (l : ℕ) :
    fiveNormalizedDigitWeight x l ^ 2 = x l ^ 2 / (5 : ℝ) ^ l := by
  rw [fiveNormalizedDigitWeight, div_pow, ← pow_mul, Nat.mul_comm l 2, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

private theorem sqrt_five_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

private theorem inv_sqrt_five_bounds : 0 ≤ (Real.sqrt 5)⁻¹ ∧ (Real.sqrt 5)⁻¹ < 1 := by
  refine ⟨inv_nonneg.mpr sqrt_five_pos.le, ?_⟩
  rw [inv_eq_one_div]
  apply (div_lt_one sqrt_five_pos).mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith only [hs, sqrt_five_pos]

private theorem fiveDigit_geometricConvolution_eq (x : ℕ → ℝ) (M : ℕ) :
    finiteGeometricConvolution (Real.sqrt 5)⁻¹ (fun l => |fiveNormalizedDigitWeight x l|) M =
      (∑ i : Fin (M + 1), |x i|) / Real.sqrt 5 ^ M := by
  rw [finiteGeometricConvolution,
    Fin.sum_univ_eq_sum_range (fun l : ℕ => |x l|) (M + 1), div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro l hl
  have hlM : l ≤ M := by have := mem_range.mp hl; omega
  rw [fiveNormalizedDigitWeight, abs_div, abs_of_pos (pow_pos sqrt_five_pos l), inv_pow]
  calc
    _ = |x l| / (Real.sqrt 5 ^ (M - l) * Real.sqrt 5 ^ l) := by
      rw [div_mul_eq_div_div]
      ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hlM, div_eq_mul_inv]

private theorem fiveDigitPronicBlock_le_convolution (x : ℕ → ℝ) (M : ℕ) :
    fiveDigitPronicBlock x M ≤ (64 / 5 : ℝ) *
      finiteGeometricConvolution (Real.sqrt 5)⁻¹
        (fun l => |fiveNormalizedDigitWeight x l|) M ^ 2 := by
  rw [fiveDigit_geometricConvolution_eq, div_pow, ← pow_mul, Nat.mul_comm M 2,
    pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  simpa only [mul_div_assoc] using fiveDigitPronicBlock_upper x M

/-- Pronic energy below an ordinary integer cutoff. -/
def fiveDigitPronicEnergyTo (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ico 1 N, fiveWeightedDigitRow x n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- Complete base-five blocks partition the entire observed prefix. -/
theorem fiveDigitPronicEnergyTo_complete (x : ℕ → ℝ) (R : ℕ) :
    fiveDigitPronicEnergyTo x (5 ^ (R + 1)) =
      ∑ M ∈ range (R + 1), fiveDigitPronicBlock x M := by
  induction R with
  | zero => simp [fiveDigitPronicEnergyTo, fiveDigitPronicBlock]
  | succ R ih =>
    rw [sum_range_succ, ← ih]
    unfold fiveDigitPronicEnergyTo fiveDigitPronicBlock
    symm
    apply sum_Ico_consecutive
    · have hp : 0 < 5 ^ (R + 1) := pow_pos (by omega) _
      omega
    · rw [pow_succ]
      omega

/-- Uniform two-sided finite energy comparison for every signed digit coefficient sequence. -/
theorem fiveDigitPronicEnergyTo_complete_bounds (x : ℕ → ℝ) (R : ℕ) :
    (1 / 5 : ℝ) * (∑ l ∈ range (R + 1), x l ^ 2 / (5 : ℝ) ^ l) ≤
        fiveDigitPronicEnergyTo x (5 ^ (R + 1)) ∧
      (1 - (Real.sqrt 5)⁻¹) ^ 2 * fiveDigitPronicEnergyTo x (5 ^ (R + 1)) ≤
        (64 / 5 : ℝ) * ∑ l ∈ range (R + 1), x l ^ 2 / (5 : ℝ) ^ l := by
  rw [fiveDigitPronicEnergyTo_complete]
  constructor
  · rw [mul_sum]
    apply sum_le_sum
    intro M _
    calc
      _ = x M ^ 2 / (5 : ℝ) ^ (M + 1) := by
        rw [pow_succ (5 : ℝ) M, div_mul_eq_div_div]
        ring
      _ ≤ _ := fiveDigitPronicBlock_lower x M
  · have hblocks : (∑ M ∈ range (R + 1), fiveDigitPronicBlock x M) ≤
        (64 / 5 : ℝ) * ∑ M ∈ range (R + 1),
          finiteGeometricConvolution (Real.sqrt 5)⁻¹
            (fun l => |fiveNormalizedDigitWeight x l|) M ^ 2 := by
      rw [mul_sum]
      exact sum_le_sum fun M _ => fiveDigitPronicBlock_le_convolution x M
    have hyoung := sum_sq_finiteGeometricConvolution_le (Real.sqrt 5)⁻¹
      inv_sqrt_five_bounds.1 inv_sqrt_five_bounds.2
      (fun l => |fiveNormalizedDigitWeight x l|) R
    simp only [sq_abs, sq_fiveNormalizedDigitWeight] at hyoung
    calc
      _ ≤ (1 - (Real.sqrt 5)⁻¹) ^ 2 * ((64 / 5 : ℝ) *
          ∑ M ∈ range (R + 1), finiteGeometricConvolution (Real.sqrt 5)⁻¹
            (fun l => |fiveNormalizedDigitWeight x l|) M ^ 2) :=
        mul_le_mul_of_nonneg_left hblocks (sq_nonneg _)
      _ = (64 / 5 : ℝ) * ((1 - (Real.sqrt 5)⁻¹) ^ 2 *
          ∑ M ∈ range (R + 1), finiteGeometricConvolution (Real.sqrt 5)⁻¹
            (fun l => |fiveNormalizedDigitWeight x l|) M ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hyoung (by norm_num)

/-- Bounded pronic energy is exactly weighted square summability of the signed digit coefficients. -/
theorem bounded_fiveDigitPronicEnergy_iff (x : ℕ → ℝ) :
    (∃ B : ℝ, ∀ N : ℕ, fiveDigitPronicEnergyTo x N ≤ B) ↔
      Summable (fun l : ℕ => x l ^ 2 / (5 : ℝ) ^ l) := by
  constructor
  · rintro ⟨B, hB⟩
    refine summable_of_sum_range_le (fun l => by positivity) (c := 5 * B) fun R => ?_
    have hlo := (fiveDigitPronicEnergyTo_complete_bounds x R).1
    have hb := hB (5 ^ (R + 1))
    have hs : (∑ l ∈ range R, x l ^ 2 / (5 : ℝ) ^ l) ≤
        ∑ l ∈ range (R + 1), x l ^ 2 / (5 : ℝ) ^ l := by
      rw [sum_range_succ]
      exact le_add_of_nonneg_right (by positivity)
    nlinarith only [hlo, hb, hs]
  · intro hx
    have hc : 0 < (1 - (Real.sqrt 5)⁻¹) ^ 2 :=
      sq_pos_of_pos (sub_pos.mpr inv_sqrt_five_bounds.2)
    refine ⟨((64 / 5 : ℝ) * ∑' l : ℕ, x l ^ 2 / (5 : ℝ) ^ l) /
      (1 - (Real.sqrt 5)⁻¹) ^ 2, fun N => ?_⟩
    let R := Nat.log 5 N
    have hN : N ≤ 5 ^ (R + 1) :=
      (Nat.lt_pow_succ_log_self (by omega : 1 < 5) N).le
    have hcut : fiveDigitPronicEnergyTo x N ≤ fiveDigitPronicEnergyTo x (5 ^ (R + 1)) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Ico.mpr ⟨(mem_Ico.mp hn).1, lt_of_lt_of_le (mem_Ico.mp hn).2 hN⟩
      · intro n _ _
        positivity
    have hs : (∑ l ∈ range (R + 1), x l ^ 2 / (5 : ℝ) ^ l) ≤
        ∑' l : ℕ, x l ^ 2 / (5 : ℝ) ^ l :=
      sum_le_hasSum _ (fun l _ => by positivity) hx.hasSum
    apply (le_div_iff₀ hc).mpr
    calc
      _ = (1 - (Real.sqrt 5)⁻¹) ^ 2 * fiveDigitPronicEnergyTo x N := mul_comm _ _
      _ ≤ (1 - (Real.sqrt 5)⁻¹) ^ 2 * fiveDigitPronicEnergyTo x (5 ^ (R + 1)) :=
        mul_le_mul_of_nonneg_left hcut hc.le
      _ ≤ (64 / 5 : ℝ) * ∑ l ∈ range (R + 1), x l ^ 2 / (5 : ℝ) ^ l :=
        (fiveDigitPronicEnergyTo_complete_bounds x R).2
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)

end GaloisForLFunctions.BiarithmeticGeometry
