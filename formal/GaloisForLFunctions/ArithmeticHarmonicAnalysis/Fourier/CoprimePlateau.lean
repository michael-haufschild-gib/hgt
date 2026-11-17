import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Fourier.DivisibilityHarmonics
import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation

/-!
# The first plateau of coprime sine harmonics

Below the first rational breakpoint, Möbius cancellation removes the linear
part of the sawtooth. The remaining height is half pi times the reduced-residue
density. Thus every modulus greater than one has a square-wave-like first plateau.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open BezoutValuationIncidence

noncomputable section

/-- On the first open cell, every divisor sees the same linear branch. -/
theorem sawtooth_divisor_first_cell {q : ℕ} (hq : 0 < q) {x : ℝ}
    (hx : 0 < x) (hxq : x < (q : ℝ)⁻¹) {d : ℕ} (hd : d ∈ q.divisors) :
    sawtooth ((d : ℝ) * x) = (d : ℝ) * x - 1 / 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hdq : (d : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)
  have hdxx : (d : ℝ) * x < 1 := by
    calc (d : ℝ) * x ≤ (q : ℝ) * x := mul_le_mul_of_nonneg_right hdq hx.le
      _ < (q : ℝ) * (q : ℝ)⁻¹ := mul_lt_mul_of_pos_left hxq hq0
      _ = 1 := mul_inv_cancel₀ hq0.ne'
  have hdx : 0 < (d : ℝ) * x := mul_pos hd0 hx
  rw [sawtooth, Int.fract_eq_self.mpr ⟨hdx.le, hdxx⟩, if_neg hdx.ne']

/-- Möbius cancellation makes the first Fourier cell exactly constant. -/
theorem coprime_sawtooth_plateau {q : ℕ} (hq : 1 < q) {x : ℝ}
    (hx : 0 < x) (hxq : x < (q : ℝ)⁻¹) :
    -Real.pi * (∑ d ∈ q.divisors, (μ d : ℝ) / d * sawtooth ((d : ℝ) * x)) =
      Real.pi / 2 * ((q.totient : ℝ) / q) := by
  have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq
  have hterm : ∀ d ∈ q.divisors,
      (μ d : ℝ) / d * sawtooth ((d : ℝ) * x) =
        (μ d : ℝ) * x - (μ d : ℝ) / d / 2 := by
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    rw [sawtooth_divisor_first_cell hq0 hx hxq hd]
    field_simp
  rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_mul,
    HTGeometry.sum_divisors_moebius_real, if_neg hq.ne', zero_mul, zero_sub,
    ← sum_div, _root_.RHTower.Sieve.sum_moebius_div_divisors_eq_totient_div hq0]
  ring

/-- The complete profile is a step function with half-jump values at resonances. -/
theorem coprime_sawtooth_floor_formula {q : ℕ} (hq : 1 < q) (x : ℝ) :
    -Real.pi * (∑ d ∈ q.divisors, (μ d : ℝ) / d * sawtooth ((d : ℝ) * x)) =
      Real.pi * ((∑ d ∈ q.divisors, (μ d : ℝ) / d * ⌊(d : ℝ) * x⌋) +
        ((q.totient : ℝ) / q) / 2 -
        (∑ d ∈ q.divisors.filter (fun d : ℕ => Int.fract ((d : ℝ) * x) = 0),
          (μ d : ℝ) / d) / 2) := by
  have hsaw (y : ℝ) : sawtooth y = y - ⌊y⌋ - 1 / 2 +
      (if Int.fract y = 0 then 1 / 2 else 0) := by
    have hf := Int.floor_add_fract y
    rw [sawtooth]
    split_ifs with h <;> linarith
  have hterm : ∀ d ∈ q.divisors,
      (μ d : ℝ) / d * sawtooth ((d : ℝ) * x) =
        (μ d : ℝ) * x - (μ d : ℝ) / d * ⌊(d : ℝ) * x⌋ - (μ d : ℝ) / d / 2 +
          (if Int.fract ((d : ℝ) * x) = 0 then (μ d : ℝ) / d else 0) / 2 := by
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    rw [hsaw]
    split_ifs <;> field_simp <;> ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    ← sum_mul, HTGeometry.sum_divisors_moebius_real, if_neg hq.ne', zero_mul,
    ← sum_div, _root_.RHTower.Sieve.sum_moebius_div_divisors_eq_totient_div (by omega),
    ← sum_div, ← sum_filter]
  ring

/-- The coprime Fourier series has the exact totient-density plateau. -/
theorem tendsto_coprimeHarmonicSine_plateau (q : ℕ) {x : ℝ}
    (hx : 0 < x) (hxq : x < ((q + 2 : ℕ) : ℝ)⁻¹) :
    Tendsto (fun N => coprimeHarmonicSine (q + 2) N x) atTop
      (𝓝 (Real.pi / 2 * (((q + 2).totient : ℝ) / (q + 2 : ℕ)))) := by
  have h := tendsto_coprimeHarmonicSine (q + 1) x
  rw [show q + 1 + 1 = q + 2 by omega,
    coprime_sawtooth_plateau (by omega : 1 < q + 2) hx hxq] at h
  exact h

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.coprime_sawtooth_floor_formula
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.tendsto_coprimeHarmonicSine_plateau
