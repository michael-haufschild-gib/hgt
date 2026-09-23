import GaloisForLFunctions.RHTower.PrimeBarycentricCoefficientDivergence
import GaloisForLFunctions.RHTower.PrimeHarmonicLogLower

/-!
# Prime-log sampling weight obstructions

This file proves two unconditional arithmetic divergence statements used to test proposed
prime-log sampling maps.

* The shifted-sinc profile
  `∑_{3 < p ≤ x} 1 / (1 + (log p)^(2 : ℕ))`
  tends to infinity.
* The critical explicit-formula profile
  `∑_{p ≤ X} (log p)^(2 : ℕ) / (p (1 + (log p)^(2 : ℕ)))`
  dominates a positive constant times the prime-harmonic sum, hence has an explicit
  `log log` lower bound.

The file deliberately makes no conditional Paley--Wiener or Hilbert-space declaration.  Turning
these profiles into a theorem about a concrete sampling operator additionally requires a proved
analytic carrier and a proved evaluation map; neither is introduced here as an interface.
-/

namespace RHTower

open Filter Finset Set Topology
open scoped BigOperators Topology

noncomputable section

/-- A positive comparison constant valid for every prime-log square. -/
def primeCriticalPWProfileConstant : ℝ :=
  Real.log 2 ^ (2 : ℕ) / (1 + Real.log 2 ^ (2 : ℕ))

theorem primeCriticalPWProfileConstant_pos : 0 < primeCriticalPWProfileConstant := by
  exact div_pos (sq_pos_of_pos (Real.log_pos (by norm_num))) (by positivity)

/-- The finite shifted-sinc profile over prime logarithms in `(log 3, log x]`. -/
def primeShiftedSincProfileSum (x : ℝ) : ℝ :=
  ∑ p ∈ windowPrimes 3 x, 1 / (1 + Real.log p ^ (2 : ℕ))

/-- The shifted-sinc profile dominates a fixed positive multiple of the reciprocal-log-square
prime tail. -/
theorem criticalConstant_mul_primeReciprocalLogSqTailSum_le_primeShiftedSincProfileSum
    {x : ℝ} (hx : 3 ≤ x) :
    primeCriticalPWProfileConstant * primeReciprocalLogSqTailSum 3 x ≤
      primeShiftedSincProfileSum x := by
  rw [primeReciprocalLogSqTailSum, primeShiftedSincProfileSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hprime, hp3, hpx⟩ :=
    (mem_windowPrimes (by norm_num : (0 : ℝ) ≤ 3) (by linarith)).mp hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hlogle : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) hp2
  have hsqle : Real.log 2 ^ (2 : ℕ) ≤ Real.log p ^ (2 : ℕ) := by nlinarith
  dsimp [primeCriticalPWProfileConstant]
  field_simp
  nlinarith

/-- **Unconditional shifted-sinc prime-profile divergence.** -/
theorem tendsto_primeShiftedSincProfileSum_atTop :
    Tendsto primeShiftedSincProfileSum atTop atTop := by
  have hscaled := tendsto_const_nhds.pos_mul_atTop primeCriticalPWProfileConstant_pos
    (tendsto_primeReciprocalLogSqTailSum_atTop 3 (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
  exact criticalConstant_mul_primeReciprocalLogSqTailSum_le_primeShiftedSincProfileSum hx

/-- The critical explicit-formula profile over primes below `X + 1`. -/
def primeCriticalPWProfileSum (X : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (X + 1),
    Real.log p ^ (2 : ℕ) / ((p : ℝ) * (1 + Real.log p ^ (2 : ℕ)))

/-- The critical profile dominates a fixed positive multiple of the prime-harmonic sum. -/
theorem primeCriticalPWProfileConstant_mul_primeHarmonic_le (X : ℕ) :
    primeCriticalPWProfileConstant *
        (∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹) ≤
      primeCriticalPWProfileSum X := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hlogle : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) hp2
  have hsqle : Real.log 2 ^ (2 : ℕ) ≤ Real.log p ^ (2 : ℕ) := by nlinarith
  dsimp [primeCriticalPWProfileConstant, primeCriticalPWProfileSum]
  field_simp
  nlinarith

/-- **Explicit critical-profile lower bound.** The profile is at least a positive constant times
`log log (X+1) - 1`. -/
theorem criticalProfile_logLog_lower (X : ℕ) (hX : 1 ≤ X) :
    primeCriticalPWProfileConstant *
        (Real.log (Real.log ((X : ℝ) + 1)) - 1) ≤
      primeCriticalPWProfileSum X := by
  calc
    primeCriticalPWProfileConstant *
        (Real.log (Real.log ((X : ℝ) + 1)) - 1) ≤
        primeCriticalPWProfileConstant *
          (∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left (log_log_sub_one_le_sum_primesBelow_inv X hX)
        primeCriticalPWProfileConstant_pos.le
    _ ≤ primeCriticalPWProfileSum X := primeCriticalPWProfileConstant_mul_primeHarmonic_le X

/-- **Unconditional critical-profile divergence.** -/
theorem tendsto_primeCriticalPWProfileSum_atTop :
    Tendsto primeCriticalPWProfileSum atTop atTop := by
  have hshift : Tendsto (fun X : ℕ => (X : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun X : ℕ => Real.log (Real.log ((X : ℝ) + 1)))
      atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hshift)
  have hsub : Tendsto (fun X : ℕ => Real.log (Real.log ((X : ℝ) + 1)) - 1)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1) hloglog
  have hscaled := tendsto_const_nhds.pos_mul_atTop primeCriticalPWProfileConstant_pos hsub
  refine tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
  exact criticalProfile_logLog_lower X hX

end
end RHTower
