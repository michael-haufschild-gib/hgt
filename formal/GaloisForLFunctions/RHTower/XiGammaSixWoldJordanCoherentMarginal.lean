import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanParametricVacuity

/-!
# Prime-weighted readout of complete coherent Frobenius packets

Retaining a left-prime marginal preserves the prime-labelled energy reporter,
but total coherent cancellation does not imply cancellation under that reporter.
The exact readout is a finite covariance. Its annihilator over all coherent
profiles consists precisely of constant prime weights. For reciprocal weights
`A / p`, universal coherent annihilation is equivalent to `A = 0`.

These are unconditional finite-source identities and classifications. They do
not assert annihilation for an arithmetic source-selected family, or prove RH.
-/

open Complex Filter Function Set Topology
open scoped BigOperators
namespace RHTower.HedenmalmThetaSource
noncomputable section

/-- Exact weighted readout, with both marginal sums retained. -/
theorem primeLabelledEnergyReporter_coherent_covariance
    (c : Nat.Primes → ℝ) (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    primeLabelledEnergyReporter c (deningerBigWittCrossPairFiniteRightLegPacket a s) =
      (s.card : ℂ) * (∑ p ∈ s, (c p : ℂ) * (starRingEnd ℂ) (a p)) -
        (∑ p ∈ s, (c p : ℂ)) * (∑ p ∈ s, (starRingEnd ℂ) (a p)) := by
  classical
  have hsum : primeLabelledEnergyReporter c
      (deningerBigWittCrossPairFiniteRightLegPacket a s) =
      ∑ p ∈ s, ∑ q ∈ s, (c p : ℂ) * (starRingEnd ℂ) (a p - a q) := by
    rw [deningerBigWittCrossPairFiniteRightLegPacket, map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases h : p ≠ q
    · simp [h, deningerBigWittCrossPairRightLeg, mul_sub]
    · simp [not_ne_iff.mp h]
  rw [hsum]
  simp_rw [map_sub, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mul_sum]
  · simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]

/-- Complete coherent packets annihilate exactly the constant prime weights. -/
theorem primeLabelledEnergyReporter_coherent_null_iff (c : Nat.Primes → ℝ) :
    (∀ (a : Nat.Primes → ℂ) (s : Finset Nat.Primes),
      primeLabelledEnergyReporter c (deningerBigWittCrossPairFiniteRightLegPacket a s) = 0) ↔
      ∃ z : ℝ, ∀ p : Nat.Primes, c p = z := by
  classical
  constructor
  · intro hnull
    let p₀ := nthPrimeSubtype 0
    refine ⟨c p₀, ?_⟩
    intro p
    by_cases hp : p = p₀
    · rw [hp]
    have h := hnull (fun r => if r = p then 1 else 0) {p, p₀}
    rw [primeLabelledEnergyReporter_coherent_covariance] at h
    simp [hp] at h
    have hc : (c p : ℂ) = (c p₀ : ℂ) := by linear_combination h
    exact_mod_cast hc
  · rintro ⟨z, hz⟩ a s
    rw [primeLabelledEnergyReporter_coherent_covariance]
    simp_rw [hz]
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    ring

/-- Reciprocal prime weights annihilate every coherent profile exactly at zero coefficient. -/
theorem primeReciprocalEnergyReporter_coherent_null_iff (A : ℝ) :
    (∀ (a : Nat.Primes → ℂ) (s : Finset Nat.Primes),
      primeLabelledEnergyReporter (fun p => A / (p : ℕ))
        (deningerBigWittCrossPairFiniteRightLegPacket a s) = 0) ↔ A = 0 := by
  rw [primeLabelledEnergyReporter_coherent_null_iff]
  constructor
  · rintro ⟨z, hz⟩
    apply (abstractPrimeReciprocalSourceDescends_iff A).1
    exact (primeLabelledActualSourceDescends_iff (fun p => A / (p : ℕ))).2
      ⟨z, fun n => hz (nthPrimeSubtype n)⟩
  · intro hA
    subst A
    exact ⟨0, fun p => by simp⟩

end
end RHTower.HedenmalmThetaSource
