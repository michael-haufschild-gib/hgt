import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Critical dilation absolute-contraction obstruction

The exact Möbius--Laplace Lambert law has critical dilation weight `k^(-1/2)`.  Its restriction to
prime indices is already nonsummable.  More sharply, no correction can have summable critical
prime mass simultaneously with the coefficient obtained by adding the uncorrected prime tail.

This closes absolute-value Neumann-series attacks on the critical renewal equation.  Any viable
dilation argument must retain conditional signed cancellation of the distinguished Möbius
solution.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- Prime power mass is nonsummable throughout the closed exponent range `[-1, +infinity)`.
This is the obstruction range relevant to critical dilation weights. -/
theorem not_summable_primeRpow_of_negOne_le {r : ℝ} (hr : -1 ≤ r) :
    ¬ Summable (fun p : Nat.Primes => (p : ℝ) ^ r) := by
  rw [Nat.Primes.summable_rpow]
  exact not_lt_of_ge hr

/-- **Sharp absolute-correction obstruction.**  At every prime-power exponent `r >= -1`, a
correction and the coefficient obtained by adding the constant prime tail cannot both have
summable weighted norm. -/
theorem no_simultaneous_summable_primeRpowCorrection
    (b : Nat.Primes → ℂ) {r : ℝ} (hr : -1 ≤ r) :
    ¬ (Summable (fun p : Nat.Primes => ‖b p‖ * (p : ℝ) ^ r) ∧
       Summable (fun p : Nat.Primes => ‖1 + b p‖ * (p : ℝ) ^ r)) := by
  rintro ⟨hb, hcorrected⟩
  apply not_summable_primeRpow_of_negOne_le hr
  have hmajor := hb.add hcorrected
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hmajor
  have htriangle : (1 : ℝ) ≤ ‖b p‖ + ‖1 + b p‖ := by
    have h := norm_sub_le (1 + b p) (b p)
    simpa [add_comm] using h
  have hweight : 0 ≤ (p : ℝ) ^ r := by positivity
  calc
    (p : ℝ) ^ r = 1 * (p : ℝ) ^ r := by ring
    _ ≤ (‖b p‖ + ‖1 + b p‖) * (p : ℝ) ^ r :=
      mul_le_mul_of_nonneg_right htriangle hweight
    _ = ‖b p‖ * (p : ℝ) ^ r + ‖1 + b p‖ * (p : ℝ) ^ r := by ring

/-- The critical prime dilation mass `sum_p p^(-1/2)` is not summable. -/
theorem not_summable_primeCriticalDilationWeight :
    ¬ Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 / 2 : ℝ))) :=
  not_summable_primeRpow_of_negOne_le (by norm_num)

/-- No absolutely controlled infinite correction can turn the critical constant prime tail into
an absolutely summable contraction tail. -/
theorem no_simultaneous_summable_primeCriticalDilationCorrection
    (b : Nat.Primes → ℂ) :
    ¬ (Summable (fun p : Nat.Primes =>
          ‖b p‖ * (p : ℝ) ^ (-(1 / 2 : ℝ))) ∧
       Summable (fun p : Nat.Primes =>
          ‖1 + b p‖ * (p : ℝ) ^ (-(1 / 2 : ℝ)))) :=
  no_simultaneous_summable_primeRpowCorrection b (by norm_num)

/-- Finite prime corrections are a fortiori impossible: an eventually zero correction leaves the
coefficient equal to one on a cofinite set of primes. -/
theorem not_summable_primeCriticalDilationCorrection_of_eventually_zero
    (b : Nat.Primes → ℂ) (hb : b =ᶠ[cofinite] 0) :
    ¬ Summable (fun p : Nat.Primes =>
      ‖1 + b p‖ * (p : ℝ) ^ (-(1 / 2 : ℝ))) := by
  intro hcorrected
  apply not_summable_primeCriticalDilationWeight
  apply hcorrected.congr_cofinite
  filter_upwards [hb] with p hp
  simp [hp]

/-- Canonical embedding of a prime index into the positive dilation semigroup. -/
def primeAsPositiveDilation (p : Nat.Primes) : ℕ+ :=
  ⟨p, p.property.pos⟩

/-- The concrete critical renewal weights are nonsummable even after restriction to prime
dilations.  Absolute convergence of the actual renewal series therefore comes from transform-value
cancellation and cannot be bounded by the weights alone. -/
theorem not_summable_prime_mobiusLaplaceCriticalRenewalWeight :
    ¬ Summable (fun p : Nat.Primes =>
      mobiusLaplaceCriticalRenewalWeight (primeAsPositiveDilation p)) := by
  simpa [mobiusLaplaceCriticalRenewalWeight_eq_rpow] using
    not_summable_primeCriticalDilationWeight

end

end RHTower
