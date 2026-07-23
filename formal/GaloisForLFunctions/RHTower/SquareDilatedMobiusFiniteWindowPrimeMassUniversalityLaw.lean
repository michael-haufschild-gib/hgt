import GaloisForLFunctions.RHTower.PowerSupportedPrimeMassFiniteWindowUniversalityLaw
import GaloisForLFunctions.RHTower.SqrtCarrierWindowBridge

/-!
# Square-dilated Möbius finite-window prime-mass universality

The square-dilated Möbius carrier has coefficient magnitude one at every prime square.  Weighting
its cutoff by `n⁻¹/⁴` turns each such coefficient into exactly `p⁻¹/²`.  The general
power-supported transference law therefore gives one concrete prime-mass packet whose independent
Steinhaus second moment and every deterministic symmetric finite window are controlled
simultaneously.
-/

open Complex MeasureTheory intervalIntegral Finset
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- Quarter-weighted square-dilated Möbius coefficient. -/
def sqrtQuarterWindowCoeff (n : ℕ) : ℝ :=
  sqrtMoebiusCoeff n * (n : ℝ) ^ (-(1 / 4 : ℝ))

/-- **Square-dilated Möbius finite-window prime-mass universality law.**  At every cutoff, the
quarter-weighted square-dilated Möbius packet has exact independent Steinhaus diagonal, that
diagonal dominates the complete prime reciprocal mass through the square-root cutoff, and every
positive symmetric deterministic window retains the same mass after subtracting only its explicit
sinc collision energy. -/
theorem sqrtQuarterWindow_primeMass_randomExact_deterministicWindowLowerBound
    (y : ℕ) (T : ℝ) (hT : 0 < T) :
    (∫ ω,
        ‖∑ n ∈ Finset.Icc 1 y,
          (sqrtQuarterWindowCoeff n : ℂ) * X n ω‖ ^ 2 ∂steinhausMeasure =
      ∑ n ∈ Finset.Icc 1 y, sqrtQuarterWindowCoeff n ^ 2) ∧
      (∑ p ∈ Nat.primesBelow (Nat.sqrt y + 1), (p : ℝ)⁻¹) ≤
        ∫ ω,
          ‖∑ n ∈ Finset.Icc 1 y,
            (sqrtQuarterWindowCoeff n : ℂ) * X n ω‖ ^ 2 ∂steinhausMeasure ∧
      (∑ p ∈ Nat.primesBelow (Nat.sqrt y + 1), (p : ℝ)⁻¹) -
          dpolySincOffDiagonalEnergy
            sqrtQuarterWindowCoeff (Finset.Icc 1 y) T ≤
        (∫ t in (-T)..T,
          ‖dpoly sqrtQuarterWindowCoeff (Finset.Icc 1 y) t‖ ^ 2) / (2 * T) := by
  have hmem : ∀ p ∈ Nat.primesBelow (Nat.sqrt y + 1), p ^ 2 ∈ Finset.Icc 1 y := by
    intro p hp
    obtain ⟨hplt, hprime⟩ := Nat.mem_primesBelow.mp hp
    have hple : p ≤ Nat.sqrt y := by omega
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_pow _ _ hprime.pos, by
        rw [pow_two]
        exact Nat.le_sqrt.mp hple⟩
  have hval : ∀ p ∈ Nat.primesBelow (Nat.sqrt y + 1),
      1 * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        |sqrtQuarterWindowCoeff (p ^ 2)| := by
    intro p hp
    obtain ⟨-, hprime⟩ := Nat.mem_primesBelow.mp hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hcoeff : |sqrtMoebiusCoeff (p ^ 2)| = 1 := by
      rw [sqrtMoebiusCoeff, sqrtPart_apply_sq,
        ArithmeticFunction.moebius_apply_prime hprime]
      norm_num
    have hpow :
        ((p ^ 2 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) =
          ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [natCast_sq_rpow]
      congr 1
      ring
    rw [sqrtQuarterWindowCoeff, one_mul, abs_mul, hcoeff, one_mul, hpow,
      abs_of_pos (Real.rpow_pos_of_pos hp0 _)]
  have hS : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n :=
    fun n hn => (Finset.mem_Icc.mp hn).1
  simpa using
    (powerSupportedPrimeMass_randomExact_deterministicWindowLowerBound
      (S := Finset.Icc 1 y)
      (P := Nat.primesBelow (Nat.sqrt y + 1))
      (b := sqrtQuarterWindowCoeff) (δ := 1) (m := 2)
      (by omega) zero_le_one hmem hval hS T hT)

end

end RHTower
