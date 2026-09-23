import GaloisForLFunctions.RHTower.HedenmalmThetaPrincipalCountertermPolarityNoGo

/-!
# Principal-class trichotomy for Route P

Modulo summable prime families, the Route P Hellinger gap has only two classes: zero at neutral
grade and the universal harmonic class `[1/p]` at every nonneutral grade.  Adding a fixed scalar
multiple `c/p`, plus any summable remainder, therefore has a complete trichotomy:

* `c = 0` admits exactly neutral grade;
* `c = -1` admits exactly nonneutral grade;
* every other `c` admits no grade.

Thus no fixed principal renormalization improves the Route P selector.  The unrenormalized
positive gap already has the unique correct principal class.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Route P gap with a fixed harmonic principal coefficient and arbitrary trace-class remainder. -/
def thetaPrimeFixedPrincipalCorrection
    (c t : ℝ) (r : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  primeValuationHellingerGap (-|t|) p +
    c * routeNGammaSewnUniversalCriticalChannelMass p + r p

/-- The universal harmonic mass itself is not summable over primes. -/
theorem not_summable_routeNGammaSewnUniversalCriticalChannelMass :
    ¬ Summable routeNGammaSewnUniversalCriticalChannelMass := by
  intro hmass
  apply not_summable_routeNGammaSewnUniversalCriticalChannelAmplitude_sq
  exact hmass.congr fun p =>
    (routeNGammaSewnUniversalCriticalChannelAmplitude_sq p).symm

/-- A scalar multiple of the universal harmonic class plus a summable tail is summable exactly
when the scalar vanishes. -/
theorem summable_scalar_mul_universalCriticalMass_add_iff
    (c : ℝ) (h : Nat.Primes → ℝ) (hh : Summable h) :
    Summable (fun p =>
      c * routeNGammaSewnUniversalCriticalChannelMass p + h p) ↔ c = 0 := by
  constructor
  · intro hsum
    by_contra hc
    apply not_summable_routeNGammaSewnUniversalCriticalChannelMass
    have hscaled : Summable (fun p =>
        c * routeNGammaSewnUniversalCriticalChannelMass p) :=
      (hsum.sub hh).congr fun p => by ring
    exact (hscaled.mul_left c⁻¹).congr fun p => by
      field_simp [hc]
  · rintro rfl
    simpa using hh

/-- **Complete quotient-class law.** A fixed principal correction is summable precisely in one of
the two class-cancelling cases. -/
theorem summable_thetaPrimeFixedPrincipalCorrection_iff
    (c t : ℝ) (r : Nat.Primes → ℝ) (hr : Summable r) :
    Summable (thetaPrimeFixedPrincipalCorrection c t r) ↔
      (t = 0 ∧ c = 0) ∨ (t ≠ 0 ∧ c = -1) := by
  by_cases ht : t = 0
  · subst t
    rw [or_iff_left (by simp)]
    simp only [true_and]
    rw [show thetaPrimeFixedPrincipalCorrection c 0 r =
        fun p : Nat.Primes =>
          c * routeNGammaSewnUniversalCriticalChannelMass p + r p by
      funext p
      simp [thetaPrimeFixedPrincipalCorrection, primeValuationHellingerGap]]
    exact summable_scalar_mul_universalCriticalMass_add_iff c r hr
  · rw [or_iff_right (by simp [ht])]
    rw [and_iff_right ht]
    have htail : Summable (fun p : Nat.Primes =>
        thetaPrimePrincipalRelativeGap t p + r p) :=
      (summable_thetaPrimePrincipalRelativeGap_iff t).mpr ht |>.add hr
    rw [show thetaPrimeFixedPrincipalCorrection c t r =
        fun p : Nat.Primes =>
          (1 + c) * routeNGammaSewnUniversalCriticalChannelMass p +
            (thetaPrimePrincipalRelativeGap t p + r p) by
      funext p
      rw [thetaPrimeFixedPrincipalCorrection, thetaPrimePrincipalRelativeGap]
      ring,
      summable_scalar_mul_universalCriticalMass_add_iff (1 + c) _ htail]
    constructor <;> intro h <;> linarith

/-- Zero principal correction is the unique fixed coefficient retaining the required neutral-only
summability locus. -/
theorem summable_thetaPrimeUnrenormalizedGap_add_iff
    (t : ℝ) (r : Nat.Primes → ℝ) (hr : Summable r) :
    Summable (thetaPrimeFixedPrincipalCorrection 0 t r) ↔ t = 0 := by
  rw [summable_thetaPrimeFixedPrincipalCorrection_iff 0 t r hr]
  simp

/-- Coefficient `-1` gives the complementary, wrong-polarity locus. -/
theorem summable_thetaPrimeFullySubtractedGap_add_iff
    (t : ℝ) (r : Nat.Primes → ℝ) (hr : Summable r) :
    Summable (thetaPrimeFixedPrincipalCorrection (-1) t r) ↔ t ≠ 0 := by
  rw [summable_thetaPrimeFixedPrincipalCorrection_iff (-1) t r hr]
  simp

/-- Every other fixed principal coefficient admits no radial grade at all. -/
theorem not_summable_thetaPrimeFixedPrincipalCorrection_of_ne_zero_of_ne_neg_one
    (c t : ℝ) (r : Nat.Primes → ℝ) (hr : Summable r)
    (hc0 : c ≠ 0) (hc1 : c ≠ -1) :
    ¬ Summable (thetaPrimeFixedPrincipalCorrection c t r) := by
  rw [summable_thetaPrimeFixedPrincipalCorrection_iff c t r hr]
  simp [hc0, hc1]

/-- On an oriented Xi fibre, the unrenormalized principal class—with any summable tail—is exactly
the desired individual Route P positivity selector. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_unrenormalizedGap_add
    (q : XiZeroCopy) (r : Nat.Primes → ℝ) (hr : Summable r) :
    (∃ x : ℝ, 0 < x ∧ thetaXiReciprocalEigenvalue q ^ (2 : ℕ) = (x : ℂ)) ↔
      Summable (thetaPrimeFixedPrincipalCorrection 0
        (primeDepthBVWoldXiCenteredRate q.1) r) := by
  rw [summable_thetaPrimeUnrenormalizedGap_add_iff _ r hr,
    thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  constructor
  · intro hflux
    exact (mul_eq_zero.mp hflux).resolve_left
      (neg_ne_zero.mpr
        (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne')
  · intro hrate
    rw [hrate, mul_zero]

end

end RHTower.HedenmalmThetaSource
