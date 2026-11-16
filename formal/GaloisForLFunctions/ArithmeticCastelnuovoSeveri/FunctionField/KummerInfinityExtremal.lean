import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityConductor
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResidueExtremal

/-!
# A small-divisor test for the last infinity gap

The sharp conductor criterion reduces to divisibility of the covering
degree by the least nonnegative branch exponent. Zero reduced exponent
is exactly the rational case.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "N" => p ^ (s + 1) + 1
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) R
local notation "g" => Module.finrank K (globalRegularDifferentials K L)

/-- The extremal infinity-gap condition is a small-divisor test on the reduced branch exponent, including genus zero. -/
theorem squareKummerInfinity_last_gap_divisor_criterion :
    (g = 0 ∨ ¬ ∃ x : L, IsIntegral K[X] x ∧
      squareKummerInfinityValuation p s c d r x = WithZero.exp ((2 * g - 1 : ℕ) : ℤ)) ↔
        R % N = 0 ∨ R % N ∣ N := by
  rw [squareKummerInfinity_last_gap_criterion,
    last_mul_residue_max_iff_dvd N R (Nat.succ_pos _)]

/-- A nonzero reduced exponent dividing the covering degree characterizes positive genus with the last possible infinity gap. -/
theorem squareKummerInfinity_positive_genus_last_gap_iff :
    (g ≠ 0 ∧ ¬ ∃ x : L, IsIntegral K[X] x ∧
      squareKummerInfinityValuation p s c d r x = WithZero.exp ((2 * g - 1 : ℕ) : ℤ)) ↔
        R % N ∣ N := by
  have hzero : g = 0 ↔ R % N = 0 := by
    rw [squareKummer_regularDifferential_finrank_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨hpos, hgap⟩
    have h := (squareKummerInfinity_last_gap_divisor_criterion p s c d r).mp (Or.inr hgap)
    exact h.resolve_left (fun hz => hpos (hzero.mpr hz))
  · intro hd
    have hres : R % N ≠ 0 := by
      intro hz
      obtain ⟨t, ht⟩ := hd
      rw [hz, zero_mul] at ht
      omega
    have hpos : g ≠ 0 := fun hz => hres (hzero.mp hz)
    refine ⟨hpos, ?_⟩
    exact ((squareKummerInfinity_last_gap_divisor_criterion p s c d r).mpr (Or.inr hd)).resolve_left hpos

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
