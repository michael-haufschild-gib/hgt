/-
# Bondarenko--Heap Lemma 10: finite Möbius zero-detection coefficients

Chen--Gupta--Li Section 12 starts zero detection with
`M_X(s, χ) = ∑_{n ≤ X} μ(n)χ(n)n⁻ˢ` and the coefficients
`c_n = ∑_{d | n, d ≤ X} μ(d)`.  This module gives a premise-free finite
version with cutoff `X + 1`, so the source identities `c₁ = 1` and
`cₙ = 0` for every represented `1 < n ≤ X + 1` are closed Lean theorems.
-/
import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaTenConductorAggregation
import GaloisForLFunctions.RHTower.Mollifier

open ArithmeticFunction

noncomputable section

namespace RHTower

/-- Truncated Möbius divisor coefficient in the zero-detection identity.
The natural cutoff is represented as `X + 1`, ensuring the source's initial
coefficient is present without a positivity premise. -/
def zeroDetectionMobiusCoefficient (X n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ X + 1), (moebius d : ℤ)

/-- The initial zero-detection coefficient is exactly one. -/
theorem zeroDetectionMobiusCoefficient_one (X : ℕ) :
    zeroDetectionMobiusCoefficient X 1 = 1 := by
  unfold zeroDetectionMobiusCoefficient
  have hfilter : (1 : ℕ).divisors.filter (fun d => d ≤ X + 1) = (1 : ℕ).divisors := by
    rw [Finset.filter_eq_self]
    intro d hd
    have hd1 : d = 1 := Nat.dvd_one.mp (Nat.mem_divisors.mp hd).1
    rw [hd1]
    omega
  rw [hfilter, sum_moebius_divisors]
  simp

/-- Every source coefficient strictly after the first and through the literal
cutoff vanishes.  `n : Fin X` encodes the complete finite interval without a
caller-supplied inequality. -/
theorem zeroDetectionMobiusCoefficient_vanishes_below_cutoff
    (X : ℕ) (n : Fin X) :
    zeroDetectionMobiusCoefficient X (n.1 + 2) = 0 := by
  have hmpos : 0 < n.1 + 2 := by omega
  have hmle : n.1 + 2 ≤ X + 1 := by omega
  unfold zeroDetectionMobiusCoefficient
  have hfilter : (n.1 + 2).divisors.filter (fun d => d ≤ X + 1) =
      (n.1 + 2).divisors := by
    rw [Finset.filter_eq_self]
    intro d hd
    exact (Nat.le_of_dvd hmpos (Nat.mem_divisors.mp hd).1).trans hmle
  rw [hfilter, sum_moebius_divisors]
  simp

end RHTower
