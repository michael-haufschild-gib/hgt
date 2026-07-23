import GaloisForLFunctions.RHTower.XiPrimeSeamCalkinUniversalityLaw

/-!
# Finite Euler compression/Calkin universality

The all-finite-packet Euler commutator interface and the cofinal anchored interface are not
different phases: at every positive aperture each is equivalent to the complete all-scale
prime-seam Calkin certificate.
-/

namespace RHTower

noncomputable section

/-- All finite prime packets commute modulo compact operators exactly when arbitrarily large
anchored two-prime packets do. -/
theorem xiFiniteEulerCompressionEssentiallyCommuting_iff_cofinal
    (a : ℝ) (ha : 0 < a) :
    XiFiniteEulerCompressionEssentiallyCommuting a ↔
      XiCofinalFirstPrimeEulerCompressionEssentiallyCommuting a :=
  (xiFiniteEulerCompressionEssentiallyCommuting_iff_riemannHypothesis a ha).trans
    (xiCofinalFirstPrimeEulerCompressionEssentiallyCommuting_iff_riemannHypothesis
      a ha).symm

/-- One positive-aperture all-finite Euler commutator phase is equivalent to every currently
formalized prime-seam Calkin chart at every positive aperture. -/
theorem xiFiniteEulerCompressionEssentiallyCommuting_iff_allScaleCalkinCertificate
    (a : ℝ) (ha : 0 < a) :
    XiFiniteEulerCompressionEssentiallyCommuting a ↔
      XiPrimeSeamAllScaleCalkinCertificate :=
  (xiFiniteEulerCompressionEssentiallyCommuting_iff_riemannHypothesis a ha).trans
    xiPrimeSeamAllScaleCalkinCertificate_iff_riemannHypothesis.symm

/-- Quantifying the finite-packet interface over all positive apertures adds no information: it
is still exactly the all-scale Calkin certificate. -/
theorem allPositive_xiFiniteEulerCompressionEssentiallyCommuting_iff_allScaleCalkinCertificate :
    (∀ a : ℝ, 0 < a → XiFiniteEulerCompressionEssentiallyCommuting a) ↔
      XiPrimeSeamAllScaleCalkinCertificate := by
  constructor
  · intro hfinite
    exact
      (xiFiniteEulerCompressionEssentiallyCommuting_iff_allScaleCalkinCertificate
        1 (by norm_num)).mp (hfinite 1 (by norm_num))
  · intro hall a ha
    exact
      (xiFiniteEulerCompressionEssentiallyCommuting_iff_allScaleCalkinCertificate
        a ha).mpr hall

end

end RHTower
