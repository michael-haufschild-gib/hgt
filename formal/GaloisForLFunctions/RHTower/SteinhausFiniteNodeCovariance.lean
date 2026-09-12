import GaloisForLFunctions.RHTower.SmoothAFEZetaRightReflectedPrimalEnergyEvent

/-!
# Finite-node covariance of largest-prime Steinhaus channels

For finitely many coefficient systems, every complex linear combination of their
largest-prime channels is the largest-prime channel of the corresponding linear
combination of coefficients.  Complex Steinhaus Parseval therefore identifies:

* the covariance Rayleigh form over the independent large-prime phases, at each
  frozen small-prime configuration; and
* the expectation of that Rayleigh form over the small-prime phases

with explicit sums of squared arithmetic coefficient combinations.  The final
specialization uses the literal reflected-primal approximate-functional-equation
coefficients.  Thus joint nondegeneracy is reduced to one concrete arithmetic
Gram lower bound, rather than inferred from scalar channel energy.
-/

noncomputable section

namespace RHTower

open Complex Finset Nat MeasureTheory
open SteinhausModel

/-- Complex linear combination of a finite family of arithmetic coefficient systems. -/
def steinhausFiniteNodeCoefficientCombination {J : ℕ}
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (n : ℕ) : ℂ :=
  ∑ j : Fin J, u j * a j n

/-- Complex linear combination of the corresponding largest-prime channels. -/
def steinhausFiniteNodeChannelCombination {J : ℕ}
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ)
    (X p : ℕ) (omega : Omega) : ℂ :=
  ∑ j : Fin J, u j * steinhausLargePrimeChannel (a j) X p omega

/-- Linear combination commutes exactly with largest-prime channel formation. -/
theorem steinhausFiniteNodeChannelCombination_eq_channel {J : ℕ}
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ)
    (X p : ℕ) (omega : Omega) :
    steinhausFiniteNodeChannelCombination a u X p omega =
      steinhausLargePrimeChannel
        (steinhausFiniteNodeCoefficientCombination a u) X p omega := by
  classical
  unfold steinhausFiniteNodeChannelCombination steinhausLargePrimeChannel
    steinhausFiniteNodeCoefficientCombination
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact expected energy of one finite-node channel combination. -/
theorem integral_normSq_steinhausFiniteNodeChannelCombination {J : ℕ}
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (X p : ℕ) :
    (∫ omega,
        ‖steinhausFiniteNodeChannelCombination a u X p omega‖ ^ 2
          ∂steinhausMeasure) =
      ∑ m ∈ Finset.Icc 1 (X / p),
        ‖steinhausFiniteNodeCoefficientCombination a u (p * m)‖ ^ 2 := by
  simpa only [steinhausFiniteNodeChannelCombination_eq_channel] using
    integral_normSq_steinhausLargePrimeChannel
      (steinhausFiniteNodeCoefficientCombination a u) X p

/-- Arithmetic Gram energy controlling one complex Rayleigh direction across a prime family. -/
def steinhausFiniteNodeArithmeticGramEnergy {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (X : ℕ) : ℝ :=
  ∑ p ∈ P, ∑ m ∈ Finset.Icc 1 (X / p),
    ‖steinhausFiniteNodeCoefficientCombination a u (p * m)‖ ^ 2

/-- The mean small-prime Rayleigh energy is the explicit arithmetic Gram energy. -/
theorem sum_integral_normSq_steinhausFiniteNodeChannelCombination {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (X : ℕ) :
    (∑ p ∈ P, ∫ omega,
        ‖steinhausFiniteNodeChannelCombination a u X p omega‖ ^ 2
          ∂steinhausMeasure) =
      steinhausFiniteNodeArithmeticGramEnergy P a u X := by
  unfold steinhausFiniteNodeArithmeticGramEnergy
  exact Finset.sum_congr rfl fun p hp =>
    integral_normSq_steinhausFiniteNodeChannelCombination a u X p

/-- A frozen family of channel coefficients sampled by independent prime phases. -/
def steinhausFiniteNodeLargePrimePacket {J : ℕ}
    (P : Finset ℕ) (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ)
    (M : ℕ) (omegaSmall omegaLarge : Omega) : ℂ :=
  ∑ p ∈ P,
    steinhausFiniteNodeChannelCombination a u M p omegaSmall * X p omegaLarge

/-- **Exact conditional covariance Rayleigh form.**  After freezing the channel
coefficients, integration over independent large-prime phases gives their squared
Gram energy. -/
theorem integral_normSq_steinhausFiniteNodeLargePrimePacket {J : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p ≠ 0)
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ)
    (M : ℕ) (omegaSmall : Omega) :
    (∫ omegaLarge,
        ‖steinhausFiniteNodeLargePrimePacket P a u M omegaSmall omegaLarge‖ ^ 2
          ∂steinhausMeasure) =
      ∑ p ∈ P,
        ‖steinhausFiniteNodeChannelCombination a u M p omegaSmall‖ ^ 2 := by
  unfold steinhausFiniteNodeLargePrimePacket
  exact integral_normSq_dpoly_complex
    (fun p => steinhausFiniteNodeChannelCombination a u M p omegaSmall) P hP

/-- Literal reflected-primal AFE coefficient family at finitely many right-line nodes. -/
def smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient {J : ℕ}
    (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ) (j : Fin J) (n : ℕ) : ℂ :=
  smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau j) r N n

/-- The mean finite-node covariance form for the literal reflected-primal AFE channels
is exactly the displayed arithmetic Gram sum. -/
theorem sum_integral_normSq_reflectedPrimalFiniteNodeChannelCombination {J : ℕ}
    (P : Finset ℕ) (d tau : Fin J → ℝ) (r : ℝ)
    (N : ℕ) (u : Fin J → ℂ) :
    (∑ p ∈ P, ∫ omega,
        ‖steinhausFiniteNodeChannelCombination
          (smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient d tau r N)
          u N p omega‖ ^ 2 ∂steinhausMeasure) =
      steinhausFiniteNodeArithmeticGramEnergy P
        (smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient d tau r N) u N :=
  sum_integral_normSq_steinhausFiniteNodeChannelCombination P
    (smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient d tau r N) u N

end RHTower

end
