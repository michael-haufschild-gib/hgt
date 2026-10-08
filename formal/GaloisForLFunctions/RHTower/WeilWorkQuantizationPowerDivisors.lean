import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Exact divisor quotient of valuation-dependent coefficients

The quotient by the arithmetic zeta function is supported on numerator powers,
with coefficients given by consecutive differences. No primality is required.
-/

open Finset
noncomputable section
namespace RHTower.WeilSpectral

def quantizationPowerSeries (u : ℕ) (d : ℕ → ℂ) : ArithmeticFunction ℂ := by
  classical
  exact toArithmeticFunction fun n => if ∃ j : ℕ, n = u ^ j then d (padicValNat u n) else 0

theorem quantizationPowerSeries_apply_pow {u : ℕ} (hu : 2 ≤ u) (d : ℕ → ℂ) (j : ℕ) :
    quantizationPowerSeries u d (u ^ j) = d j := by
  simp only [quantizationPowerSeries, toArithmeticFunction, ArithmeticFunction.coe_mk]
  rw [if_neg (pow_ne_zero _ (by omega)), if_pos ⟨j, rfl⟩, padicValNat_base_pow (by omega)]

theorem quantizationPowerSeries_eq_zero {u n : ℕ} (d : ℕ → ℂ)
    (hn : ¬ ∃ j : ℕ, n = u ^ j) : quantizationPowerSeries u d n = 0 := by
  simp [quantizationPowerSeries, toArithmeticFunction, hn]

theorem quantizationPowerSeries_divisor_sum {u n : ℕ} (hu : 2 ≤ u) (hn : 1 ≤ n)
    (d : ℕ → ℂ) :
    (ArithmeticFunction.zeta * quantizationPowerSeries u d) n =
      ∑ j ∈ range (padicValNat u n + 1), d j := by
  classical
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  let S := (range (padicValNat u n + 1)).image (fun j => u ^ j)
  have hS : S ⊆ n.divisors := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    apply Nat.mem_divisors.mpr
    exact ⟨(Nat.pow_dvd_iff_le_padicValNat (by omega) (by omega)).mpr (by simpa using hj), by omega⟩
  have hout : ∀ x ∈ n.divisors, x ∉ S → quantizationPowerSeries u d x = 0 := by
    intro x hx hxs
    apply quantizationPowerSeries_eq_zero
    rintro ⟨j, rfl⟩
    apply hxs
    apply mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    have hj := (Nat.pow_dvd_iff_le_padicValNat (by omega) (by omega)).mp
      (Nat.mem_divisors.mp hx).1
    simpa using hj
  rw [← sum_subset hS hout]
  dsimp [S]
  rw [sum_image (fun i _ j _ hij => Nat.pow_right_injective hu hij)]
  exact sum_congr rfl fun j _ => quantizationPowerSeries_apply_pow hu d j

theorem quantization_sum_differences (A : ℕ → ℂ) (j : ℕ) :
    (∑ k ∈ range (j+1), (if k = 0 then A 0 else A k - A (k-1))) = A j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih]
    simp

theorem quantization_exists_power_quotient {u : ℕ} (hu : 2 ≤ u) {a : ℕ → ℂ}
    (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (ha : ∀ n : ℕ, 1 ≤ n → a n = a (u ^ padicValNat u n)) :
    ∃ b : ArithmeticFunction ℂ, b 1 = 1 ∧
      (∀ n : ℕ, (¬ ∃ j : ℕ, n = u ^ j) → b n = 0) ∧
      ∀ n : ℕ, (ArithmeticFunction.zeta * b) n = a n := by
  let d : ℕ → ℂ := fun j => if j=0 then a 1 else a (u^j) - a (u^(j-1))
  refine ⟨quantizationPowerSeries u d, ?_, fun n hn => quantizationPowerSeries_eq_zero d hn, ?_⟩
  · have h := quantizationPowerSeries_apply_pow hu d 0
    simpa [d, ha1] using h
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · rw [quantizationPowerSeries_divisor_sum hu hn, ha n hn]
      have h := quantization_sum_differences (fun j => a (u^j)) (padicValNat u n)
      simpa only [pow_zero] using h

end RHTower.WeilSpectral
