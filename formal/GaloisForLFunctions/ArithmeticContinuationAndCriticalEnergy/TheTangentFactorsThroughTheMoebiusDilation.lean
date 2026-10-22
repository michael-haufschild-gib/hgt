import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationCalculusOnIntegerPrefixes

/-!
# The tangent factors through the Möbius dilation

`Λ = μ * log`, and the damping twist is a ring homomorphism, so the damped prime row factors:
`Λ_ε = μ_ε * (log)_ε`.  By the dilation calculus the prime dilation therefore factors as a Möbius
dilation after a logarithmic one,

`D^{Λ_ε} = D^{μ_ε} ∘ D^{(log)_ε}`  (`prefixDilation_dampedPrime_factor`),

and the logarithmic dilation of the source is already explicit — a Möbius-free expression in the von
Mangoldt weights, the integer parts and the two densities.  Hence the centred damping tangent is the
**Möbius dilation of an explicit row**, up to the explicit correction:

`E_ε = D^{μ_ε}(Ψ_ε − m₀(ε) Σ_j Λ(j) j^{-ε} Φ_ε(⌊·/j⌋)) + (m₀(ε) Ψ_ε − · m(ε))`
(`dampedChebyshevError_eq_moebiusDilation`).

So the whole Möbius content of the tangent sits in one dilation, and the signed work becomes a
bilinear expression in the Möbius row: the source on one side, a Möbius dilation of a Möbius-free
row on the other.  That is the shape the single-modulus bilinear mechanism of
`BezoutValuationIncidence` is built for.
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The damped Möbius dilation weight `μ(j) j^{-ε}`. -/
def dampedMoebiusWeight (ε : ℝ) (j : ℕ) : ℝ := (moebius j : ℝ) * (j : ℝ) ^ (-ε)

/-- The damped logarithm weight `(log j) j^{-ε}`. -/
def dampedLogWeight (ε : ℝ) (j : ℕ) : ℝ := Real.log j * (j : ℝ) ^ (-ε)

/-- The damped prime row is the convolution of the damped Möbius row with the damped logarithm. -/
theorem sum_divisors_dampedMoebius_mul_dampedLog (ε : ℝ) (m : ℕ) :
    (∑ j ∈ m.divisors, dampedMoebiusWeight ε j * dampedLogWeight ε (m / j)) =
      dampedPrimeWeight ε m := by
  have hmul : dampedTwist ε (↑moebius : ArithmeticFunction ℝ) *
      dampedTwist ε (ArithmeticFunction.log : ArithmeticFunction ℝ) =
      dampedTwist ε (Λ : ArithmeticFunction ℝ) := by
    rw [← dampedTwist_mul, ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
  have hval : (dampedTwist ε (↑moebius : ArithmeticFunction ℝ) *
      dampedTwist ε (ArithmeticFunction.log : ArithmeticFunction ℝ)) m =
      dampedTwist ε (Λ : ArithmeticFunction ℝ) m := by rw [hmul]
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun a b => dampedTwist ε (↑moebius : ArithmeticFunction ℝ) a *
        dampedTwist ε (ArithmeticFunction.log : ArithmeticFunction ℝ) b)] at hval
  simp only [dampedTwist_apply, ArithmeticFunction.log_apply,
    ArithmeticFunction.intCoe_apply] at hval
  simp only [dampedMoebiusWeight, dampedLogWeight, dampedPrimeWeight]
  rw [← hval]

/-- **The prime dilation factors.** -/
theorem prefixDilation_dampedPrime_factor (ε : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    prefixDilation (dampedPrimeWeight ε) v n =
      prefixDilation (dampedMoebiusWeight ε) (prefixDilation (dampedLogWeight ε) v) n := by
  rw [prefixDilation_comp]
  rw [prefixDilation, prefixDilation]
  exact Finset.sum_congr rfl fun m _ => by
    rw [sum_divisors_dampedMoebius_mul_dampedLog]

/-- **The tangent is the Möbius dilation of an explicit row.**  Every Möbius factor of the damping
tangent sits in a single dilation; the row it acts on carries only von Mangoldt weights, integer
parts and the two densities. -/
theorem dampedChebyshevError_eq_moebiusDilation (ε : ℝ) (n : ℕ) :
    dampedChebyshevError ε n =
      prefixDilation (dampedMoebiusWeight ε)
          (fun m => dampedPrimeFloorSum ε m -
            (pmPowerDampedDivisorDensity ε).re *
              ∑ j ∈ Icc 1 m, dampedPrimeWeight ε j * dampedUnitFloorSum ε (m / j)) n +
        ((pmPowerDampedDivisorDensity ε).re * dampedPrimeFloorSum ε n -
          dampedReadout ε * n) := by
  have hdil : (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j *
      pmPowerDampedCenteredDivisorPrefix ε (n / j)) =
      prefixDilation (dampedPrimeWeight ε) (pmPowerDampedCenteredDivisorPrefix ε) n := rfl
  rw [dampedChebyshevError_eq_dilation ε n, hdil,
    prefixDilation_dampedPrime_factor ε (pmPowerDampedCenteredDivisorPrefix ε) n]
  congr 2
  funext m
  have hlog : prefixDilation (dampedLogWeight ε) (pmPowerDampedCenteredDivisorPrefix ε) m =
      prefixDilation (fun j => Real.log j * (j : ℝ) ^ (-ε))
        (pmPowerDampedCenteredDivisorPrefix ε) m := by
    rw [prefixDilation, prefixDilation]
    exact Finset.sum_congr rfl fun j _ => by rw [dampedLogWeight]
  rw [hlog, prefixDilation_dampedLog_centeredPrefix]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
