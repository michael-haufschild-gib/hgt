import GaloisForLFunctions.RHTower.PrimeSeamDampingAperture

/-!
# Prime-valuation Kakutani radial purity

The Hellinger numerator for the source-derived prime-valuation geometric laws is the squared
distance between the amplitudes `p⁻¹ᐟ²` and `p⁻¹ᐟ²⁺ᶜ`.  This module identifies that numerator
exactly with a reparameterized member of the already formalized damped prime-clock reflection
hierarchy.  Its prime sum is finite precisely at zero radial twist.

This is the scalar analytic input to the product-measure sector mechanism.  It does not prove that
the Xi conormal has a source-normal realization in that sector; that remains the load-bearing
source theorem.
-/

namespace RHTower

noncomputable section

/-- Squared local Hellinger numerator between the critical prime-valuation law and its coherent
radial twist by `c`. -/
def primeValuationHellingerGap (c : ℝ) (p : Nat.Primes) : ℝ :=
  ((p : ℝ) ^ (-(1 / 2 : ℝ)) -
    (p : ℝ) ^ (-(1 / 2 - c))) ^ 2

/-- The prime-valuation Hellinger numerator is exactly a power-damped prime-clock reflection
energy.  Thus the new product-sector interpretation reuses, rather than duplicates, the scalar
reflection aperture already present in the corpus. -/
theorem primeValuationHellingerGap_eq_weightedReflection
    (c : ℝ) (p : Nat.Primes) :
    primeValuationHellingerGap c p =
      weightedPrimeClockReflectionLogMomentEnergy
        0 (-c) ((1 + c) / 2) p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hscale :
      (p : ℝ) ^ c = ((p : ℝ) ^ (c / 2)) ^ 2 := by
    rw [pow_two, ← Real.rpow_add hp0]
    congr 1
    ring
  have hleft :
      (p : ℝ) ^ (c / 2) * (p : ℝ) ^ (-((1 + c) / 2)) =
        (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  have hright :
      (p : ℝ) ^ (c / 2) *
          (p : ℝ) ^ (-(1 - (1 + c) / 2)) =
        (p : ℝ) ^ (-(1 / 2 - c)) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  rw [primeValuationHellingerGap,
    weightedPrimeClockReflectionLogMomentEnergy,
    primeClockReflectionEnergy]
  simp only [pow_zero, one_mul, neg_neg]
  rw [hscale, ← mul_pow]
  rw [mul_sub, hleft, hright]

/-- **Prime-valuation radial-purity theorem.**  The all-prime Hellinger numerator is summable
exactly for the critical radial sector. -/
theorem summable_primeValuationHellingerGap_iff (c : ℝ) :
    Summable (primeValuationHellingerGap c) ↔ c = 0 := by
  rw [show primeValuationHellingerGap c =
      weightedPrimeClockReflectionLogMomentEnergy
        0 (-c) ((1 + c) / 2) by
      funext p
      exact primeValuationHellingerGap_eq_weightedReflection c p]
  rw [summable_weightedPrimeClockReflectionLogMomentEnergy_iff]
  constructor
  · rintro (hcenter | haperture)
    · linarith
    · have habs : -c ≤ |c| := neg_le_abs c
      have harg : |2 * ((1 + c) / 2) - 1| = |c| := by
        congr 1
        ring
      rw [harg] at haperture
      linarith
  · intro hc
    left
    linarith

end

end RHTower
