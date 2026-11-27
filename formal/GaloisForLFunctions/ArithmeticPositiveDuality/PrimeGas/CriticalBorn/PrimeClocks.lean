import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Law
import GaloisForLFunctions.HTGeometry.PrimePoissonSuperselectionScreen
import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw

/-! # Harmonic elementary sampling on the full torus of prime energies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology

/-- One prime clock interrogates every elementary energy simultaneously. -/
def primeClocks := packetLaw (fun p => countableClockPhasePoint
  (fun q : Nat.Primes => Real.log (q:ℕ)) (-Real.log p))

theorem primeClocks_moment (m : Nat.Primes →₀ ℤ) (N : ℕ) :
    (∫ z, infiniteTorusFourier m z ∂(primeClocks N : Measure (Nat.Primes → UnitAddCircle))) =
      coefficient (infiniteTorusCharacterDetuning m (fun q : Nat.Primes => Real.log (q:ℕ))) (-1) N := by
  rw [primeClocks,packet_integral,coefficient]
  simp only [infiniteTorusFourier_countableClockPhasePoint,phase,Circle.coe_exp,neg_neg,zpow_one,
    neg_mul,mul_comm (Real.log _) (infiniteTorusCharacterDetuning m _)]

/-- All prime energy clocks acquire independent uniform phases in the
weak limit of a single harmonically sampled elementary excitation. -/
theorem primeClocks_Haar : Tendsto primeClocks atTop
    (𝓝 (⟨torusHaar Nat.Primes,inferInstance⟩ : ProbabilityMeasure (Nat.Primes → UnitAddCircle))) := by
  apply probabilityMeasure_tendsto_of_infiniteTorusFourier_integral_tendsto
  intro m
  change Tendsto (fun N => ∫ z, infiniteTorusFourier m z ∂(primeClocks N : Measure _))
    atTop (𝓝 (∫ z, infiniteTorusFourier m z ∂torusHaar Nat.Primes))
  have haar : (∫ z, infiniteTorusFourier m z ∂torusHaar Nat.Primes) =
      if m=0 then 1 else 0 := by
    change (∫ z, torusCharacter m z ∂torusHaar Nat.Primes) = _
    exact integral_torusCharacter m
  rw [haar]
  simp only [primeClocks_moment]
  have resonant := infiniteTorusCharacterDetuning_logPrime_eq_zero_iff m
  by_cases h : m=0
  · simp only [if_pos h,resonant.mpr h,zero_height_coefficient]
    exact tendsto_const_nhds
  · rw [if_neg h]
    exact nonzero_mode _ (fun he => h (resonant.mp he)) _ (by norm_num)

#print axioms primeClocks_moment
#print axioms primeClocks_Haar

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
