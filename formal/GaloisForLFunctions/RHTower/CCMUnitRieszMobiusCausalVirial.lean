import GaloisForLFunctions.RHTower.CCMCriticalMellinRieszMobiusRenewal
import GaloisForLFunctions.RHTower.CCMUnitRieszMarkovDensity

/-!
# Finite critical Möbius causal virial

This module records the exact finite algebra behind the causal-complement virial used by the
unit-Riesz Markov factorization.  It is known-derived corpus infrastructure, not new scientific
knowledge and not an RH proof.

For a finite critical Möbius boundary, subtracting `T` times the causal complement from its
primitive cancels the entire boundary mass and leaves only the logarithmic Möbius moment plus the
explicit polar term.  No estimate or zero information is used.
-/

open Nat ArithmeticFunction Finset
open scoped BigOperators Moebius

namespace RHTower

noncomputable section

/-- Finite critical weighted-Möbius boundary mass. -/
def finiteCriticalMobiusBoundary (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 K,
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) / n

/-- Finite logarithmic moment of the critical weighted-Möbius boundary. -/
def finiteCriticalMobiusLogMoment (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 K,
    (((ArithmeticFunction.moebius n : ℤ) : ℝ) / n) * Real.log n

/-- Finite critical causal complement `exp(-T)-m_K`. -/
def finiteCriticalMobiusCausalComplement (T : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-T) - finiteCriticalMobiusBoundary K

/-- Exact primitive of the finite step-boundary model, written without analytic integration. -/
def finiteCriticalMobiusCausalPrimitive (T : ℝ) (K : ℕ) : ℝ :=
  1 - Real.exp (-T) -
    ∑ n ∈ Finset.Icc 1 K,
      (((ArithmeticFunction.moebius n : ℤ) : ℝ) / n) * (T - Real.log n)

/-- Causal virial `primitive - T * complement`. -/
def finiteCriticalMobiusCausalVirial (T : ℝ) (K : ℕ) : ℝ :=
  finiteCriticalMobiusCausalPrimitive T K -
    T * finiteCriticalMobiusCausalComplement T K

/-- **Finite causal-virial collapse.**  Boundary mass cancels exactly, leaving the logarithmic
Möbius moment and explicit polar correction. -/
theorem finiteCriticalMobiusCausalVirial_eq_logMoment
    (T : ℝ) (K : ℕ) :
    finiteCriticalMobiusCausalVirial T K =
      1 - (1 + T) * Real.exp (-T) + finiteCriticalMobiusLogMoment K := by
  rw [finiteCriticalMobiusCausalVirial, finiteCriticalMobiusCausalPrimitive,
    finiteCriticalMobiusCausalComplement, finiteCriticalMobiusBoundary,
    finiteCriticalMobiusLogMoment]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Sign convention matching the paper's `Q(X)=-sum mu(n)log(n)/n`. -/
def finiteCriticalMobiusLogDefect (K : ℕ) : ℝ :=
  -finiteCriticalMobiusLogMoment K

/-- Equivalent source-facing form of the finite causal virial. -/
theorem finiteCriticalMobiusCausalVirial_eq_one_sub_logDefect
    (T : ℝ) (K : ℕ) :
    finiteCriticalMobiusCausalVirial T K =
      1 - (1 + T) * Real.exp (-T) - finiteCriticalMobiusLogDefect K := by
  rw [finiteCriticalMobiusCausalVirial_eq_logMoment, finiteCriticalMobiusLogDefect]
  ring

end

end RHTower
