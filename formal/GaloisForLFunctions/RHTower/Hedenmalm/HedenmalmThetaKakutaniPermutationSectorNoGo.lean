import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKakutaniBalancedIndexNoGo

/-!
# Weak-Hilbert ideal barrier for theta Kakutani sectors

The universal critical channel has amplitude `p⁻¹ᐟ²`, hence lies outside `ℓ²` over the primes.
Every nonneutral twisted channel has amplitude `p⁻¹ᐟ²⁻|t|`, hence lies in `ℓ²`.  Subtracting any
`ℓ²` correction from the universal channel cannot produce an `ℓ²` gap.  In particular, no
permutation of prime coordinates can make a nonneutral twisted sector equivalent to the critical
sector.

Thus Route P's harmonic escape is an ideal-class obstruction, not an artifact of coordinate
matching.  Any successful source construction must cancel the universal non-`ℓ²` principal symbol
before Hilbert completion; finite-dimensional or square-summable corrections cannot do so.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Squared amplitude gap after arbitrary relabeling of the prime coordinates. -/
def thetaPrimePermutationAmplitudeGapSq
    (t : ℝ) (e : Nat.Primes ≃ Nat.Primes) (p : Nat.Primes) : ℝ :=
  (routeNGammaSewnUniversalCriticalChannelAmplitude p -
    routeNGammaSewnTwistedCriticalChannelAmplitude t (e p)) ^ 2

/-- The universal critical amplitude is outside `ℓ²` over the primes. -/
theorem not_summable_routeNGammaSewnUniversalCriticalChannelAmplitude_sq :
    ¬ Summable (fun p : Nat.Primes =>
      routeNGammaSewnUniversalCriticalChannelAmplitude p ^ 2) := by
  rw [show (fun p : Nat.Primes =>
      routeNGammaSewnUniversalCriticalChannelAmplitude p ^ 2) =
        fun p : Nat.Primes => (p : ℝ) ^ (-1 : ℝ) by
    funext p
    rw [routeNGammaSewnUniversalCriticalChannelAmplitude_sq,
      routeNGammaSewnUniversalCriticalChannelMass]]
  rw [Nat.Primes.summable_rpow]
  norm_num

/-- Every nonneutral twisted critical amplitude belongs to `ℓ²`. -/
theorem summable_routeNGammaSewnTwistedCriticalChannelAmplitude_sq_of_ne
    (t : ℝ) (ht : t ≠ 0) :
    Summable (fun p : Nat.Primes =>
      routeNGammaSewnTwistedCriticalChannelAmplitude t p ^ 2) := by
  rw [show (fun p : Nat.Primes =>
      routeNGammaSewnTwistedCriticalChannelAmplitude t p ^ 2) =
        fun p : Nat.Primes => (p : ℝ) ^ (-1 - 2 * |t|) by
    funext p
    rw [routeNGammaSewnTwistedCriticalChannelAmplitude_sq,
      routeNGammaSewnTwistedCriticalChannelMass]]
  exact Nat.Primes.summable_rpow.mpr (by
    have htpos : 0 < |t| := abs_pos.mpr ht
    linarith)

/-- An `ℓ²` correction cannot absorb the universal weak-`ℓ²` prime amplitude. -/
theorem not_summable_sq_sub_universal_of_summable_sq
    (v : Nat.Primes → ℝ)
    (hv : Summable (fun p : Nat.Primes => v p ^ 2)) :
    ¬ Summable (fun p : Nat.Primes =>
      (routeNGammaSewnUniversalCriticalChannelAmplitude p - v p) ^ 2) := by
  intro hgap
  apply not_summable_routeNGammaSewnUniversalCriticalChannelAmplitude_sq
  refine Summable.of_nonneg_of_le
    (f := fun p : Nat.Primes =>
      2 * (routeNGammaSewnUniversalCriticalChannelAmplitude p - v p) ^ 2 +
        2 * v p ^ 2)
    (fun p => sq_nonneg (routeNGammaSewnUniversalCriticalChannelAmplitude p))
    (fun p => by
      nlinarith [sq_nonneg
        (routeNGammaSewnUniversalCriticalChannelAmplitude p - 2 * v p)])
    ((hgap.mul_left 2).add (hv.mul_left 2))

/-- Relabeling primes preserves square summability of a nonneutral twisted amplitude. -/
theorem summable_permuted_routeNGammaSewnTwistedCriticalChannelAmplitude_sq_of_ne
    (t : ℝ) (ht : t ≠ 0) (e : Nat.Primes ≃ Nat.Primes) :
    Summable (fun p : Nat.Primes =>
      routeNGammaSewnTwistedCriticalChannelAmplitude t (e p) ^ 2) := by
  exact (e.summable_iff.mpr
    (summable_routeNGammaSewnTwistedCriticalChannelAmplitude_sq_of_ne t ht)).congr
      (fun _ => rfl)

/-- No prime permutation can turn a nonneutral twisted sector into a square-summable perturbation
of the critical sector. -/
theorem not_summable_thetaPrimePermutationAmplitudeGapSq_of_ne
    (t : ℝ) (ht : t ≠ 0) (e : Nat.Primes ≃ Nat.Primes) :
    ¬ Summable (thetaPrimePermutationAmplitudeGapSq t e) := by
  exact not_summable_sq_sub_universal_of_summable_sq
    (fun p => routeNGammaSewnTwistedCriticalChannelAmplitude t (e p))
    (summable_permuted_routeNGammaSewnTwistedCriticalChannelAmplitude_sq_of_ne t ht e)

/-- A prime-coordinate matching with square-summable amplitude gap exists exactly at neutral
grade. -/
theorem exists_primePermutation_summable_amplitudeGap_iff (t : ℝ) :
    (∃ e : Nat.Primes ≃ Nat.Primes,
      Summable (thetaPrimePermutationAmplitudeGapSq t e)) ↔ t = 0 := by
  constructor
  · rintro ⟨e, hgap⟩
    by_contra ht
    exact not_summable_thetaPrimePermutationAmplitudeGapSq_of_ne t ht e hgap
  · rintro rfl
    refine ⟨Equiv.refl Nat.Primes, ?_⟩
    rw [show thetaPrimePermutationAmplitudeGapSq 0 (Equiv.refl Nat.Primes) =
        (fun _ : Nat.Primes => 0) by
      funext p
      simp [thetaPrimePermutationAmplitudeGapSq,
        routeNGammaSewnUniversalCriticalChannelAmplitude,
        routeNGammaSewnTwistedCriticalChannelAmplitude]]
    exact summable_zero

/-- On an oriented Xi fibre, prime-sector equivalence after arbitrary relabeling is exactly
vanishing of the theta Green boundary current. -/
theorem exists_primePermutation_summable_amplitudeGap_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    (∃ e : Nat.Primes ≃ Nat.Primes,
      Summable (thetaPrimePermutationAmplitudeGapSq
        (primeDepthBVWoldXiCenteredRate q.1) e)) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [exists_primePermutation_summable_amplitudeGap_iff]
  rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  constructor
  · intro hrate
    rw [hrate, mul_zero]
  · intro hflux
    have hunit : -(thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
      neg_ne_zero.mpr
        (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
    exact (mul_eq_zero.mp hflux).resolve_left hunit

/-- **Permutation-robust Route P criterion.** A squared theta node is positive real exactly when
its critical and twisted prime sectors admit an `ℓ²` matching, even after arbitrary relabeling of
all primes. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_exists_primePermutation_summable_amplitudeGap
    (q : XiZeroCopy) :
    (∃ r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ 2 = (r : ℂ)) ↔
      ∃ e : Nat.Primes ≃ Nat.Primes,
        Summable (thetaPrimePermutationAmplitudeGapSq
          (primeDepthBVWoldXiCenteredRate q.1) e) := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero,
    exists_primePermutation_summable_amplitudeGap_iff_boundaryFlux_zero]

end

end RHTower.HedenmalmThetaSource
