import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate

/-!
# Exact completed prime--Gamma accretivity criteria for RH

The continued source anti-Herglotz condition is exactly the real accretivity of
the completed prime--Gamma flux after the centered coordinate change.  Combining
this identity with the one-Cauchy source gate makes both the full left-half-strip
condition and its countable Gaussian-rational restriction equivalent to RH.
-/

open Complex

namespace RHTower

noncomputable section

/-- Anti-Herglotzness in the centered upper half-strip gives completed
prime--Gamma accretivity in the original left half-strip coordinate. -/
theorem completedPrimeGammaLeftHalfAccretive_of_continuedPrimeArchUpperAntiHerglotz
    (hanti : ContinuedPrimeArchUpperAntiHerglotz) :
    CompletedPrimeGammaLeftHalfAccretive := by
  intro s hspos hshalf hzeta
  let z : ℂ := (s - 1 / 2) * (-I)
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hzim : z.im = 1 / 2 - s.re := by
    simp [z]
  have hzimpos : 0 < z.im := by rw [hzim]; linarith
  have hzimhalf : z.im < 1 / 2 := by rw [hzim]; linarith
  have hsource := hanti z hzimpos hzimhalf (by rw [hcoord]; exact hzeta)
  rw [continuedPrimeArchSourceRelativeTrace, hcoord] at hsource
  change (-I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ 0 at hsource
  simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul, one_mul] at hsource
  linarith

/-- The original-coordinate accretivity and centered anti-Herglotz signs are
the same source condition. -/
theorem completedPrimeGammaLeftHalfAccretive_iff_antiHerglotz :
    CompletedPrimeGammaLeftHalfAccretive ↔ ContinuedPrimeArchUpperAntiHerglotz :=
  ⟨continuedPrimeArchUpperAntiHerglotz_of_completedPrimeGammaLeftHalfAccretive,
    completedPrimeGammaLeftHalfAccretive_of_continuedPrimeArchUpperAntiHerglotz⟩

/-- Exact anti-Herglotz source criterion for RH. -/
theorem continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis :
    ContinuedPrimeArchUpperAntiHerglotz ↔ RiemannHypothesis := by
  rw [← continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz,
    continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis]

/-- Exact completed prime--Gamma left-half-strip accretivity criterion for RH. -/
theorem completedPrimeGammaLeftHalfAccretive_iff_riemannHypothesis :
    CompletedPrimeGammaLeftHalfAccretive ↔ RiemannHypothesis := by
  rw [completedPrimeGammaLeftHalfAccretive_iff_antiHerglotz,
    continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis]

/-- Full left-half-strip accretivity restricts to the countable
Gaussian-rational source family. -/
theorem completedPrimeGammaGaussianRatLeftHalfAccretive_of_full
    (hfull : CompletedPrimeGammaLeftHalfAccretive) :
    CompletedPrimeGammaGaussianRatLeftHalfAccretive := by
  intro q hq0 hqh hqz
  exact hfull (gaussianRatPoint q) hq0 hqh hqz

/-- Exact countable completed prime--Gamma source criterion for RH. -/
theorem completedPrimeGammaGaussianRatLeftHalfAccretive_iff_riemannHypothesis :
    CompletedPrimeGammaGaussianRatLeftHalfAccretive ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_completedPrimeGammaGaussianRatLeftHalfAccretive
  · intro hRH
    exact completedPrimeGammaGaussianRatLeftHalfAccretive_of_full
      (completedPrimeGammaLeftHalfAccretive_iff_riemannHypothesis.mpr hRH)

end

end RHTower
