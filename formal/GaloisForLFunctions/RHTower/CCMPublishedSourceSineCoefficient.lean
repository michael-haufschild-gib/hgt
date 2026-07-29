import GaloisForLFunctions.RHTower.CCMPolarPrimeStieltjesAutocorrelation

/-!
# The published CCM source coefficient as a completed-error cosine moment

The off-diagonal source coordinate in Connes--Consani--Moscovici is the sine transform of the
restricted Weil distribution.  This file identifies its polar--prime part with an endpoint-free
cosine moment of the completed critical-Mellin error.  Adding the finite archimedean sine term
gives the exact published source coefficient.  At the physical clock frequencies the endpoint
condition is automatic.

This is an unconditional source identity.  It reduces the central-slab order obstruction to the
sign of one explicit von-Mangoldt--Gamma functional; it does not assert that sign.
-/

open scoped BigOperators
open MeasureTheory Set Finset

noncomputable section

namespace RHTower

/-- Archimedean density in the one-sided logarithmic Weil distribution. -/
def ccmPublishedArchimedeanDensity (h : ℝ) : ℝ :=
  Real.exp (h / 2) / (Real.exp h - Real.exp (-h))

/-- The finite archimedean contribution to the published odd CCM source coordinate. -/
def ccmPublishedArchimedeanSineCoefficient (a ξ : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ h in Ioc (0 : ℝ) (2 * a),
    Real.sin (ξ * h) * ccmPublishedArchimedeanDensity h

/-- Polar--prime contribution to the published odd CCM source coordinate.  The sign agrees with
`D = W₀,₂ - Wℝ - Σ Wp` and `b(ξ) = -π⁻¹ ∫ sin(ξh) dD(h)`. -/
def ccmPublishedPolarPrimeSineCoefficient (a ξ : ℝ) : ℝ :=
  -(criticalMellinStieltjesPairing a
    (fun h => (Real.sin (ξ * h) : ℂ))).re / Real.pi

/-- Exact finite-aperture source coordinate `b(ξ)` from the CCM matrix. -/
def ccmPublishedSourceSineCoefficient (a ξ : ℝ) : ℝ :=
  ccmPublishedArchimedeanSineCoefficient a ξ +
    ccmPublishedPolarPrimeSineCoefficient a ξ

/-- Endpoint-free cosine moment of the completed prime--polar cumulative carrier. -/
def ccmCompletedErrorCosineMoment (a ξ : ℝ) : ℝ :=
  (∫ h in Ioc (0 : ℝ) (2 * a),
    (criticalMellinCompletedError h : ℂ) *
      ((ξ * Real.cos (ξ * h) : ℝ) : ℂ)).re

/-- Stieltjes integration by parts turns the sine coordinate into the completed-error cosine
moment whenever the sine test vanishes at the aperture endpoint. -/
theorem ccmPublishedPolarPrimeSineCoefficient_eq_completedErrorCosineMoment
    {a ξ : ℝ} (ha : 0 ≤ a) (hend : Real.sin (ξ * (2 * a)) = 0) :
    ccmPublishedPolarPrimeSineCoefficient a ξ =
      ccmCompletedErrorCosineMoment a ξ / Real.pi := by
  let F : ℝ → ℂ := fun h => (Real.sin (ξ * h) : ℂ)
  let F' : ℝ → ℂ := fun h => ((ξ * Real.cos (ξ * h) : ℝ) : ℂ)
  have hF : ∀ x ∈ Set.Icc (0 : ℝ) (2 * a), HasDerivAt F (F' x) x := by
    intro x _hx
    have hr : HasDerivAt (fun h : ℝ => Real.sin (ξ * h))
        (ξ * Real.cos (ξ * x)) x := by
      simpa only [Function.comp_apply, mul_one, mul_comm] using
        (Real.hasDerivAt_sin (ξ * x)).comp x
          ((hasDerivAt_id x).const_mul ξ)
    have hc :=
      (Complex.ofRealCLM.hasFDerivAt.comp x hr.hasFDerivAt).hasDerivAt
    simpa only [F, F', Function.comp_apply, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using hc
  have hF' : IntervalIntegrable F' volume 0 (2 * a) := by
    have hc : Continuous F' := by
      dsimp only [F']
      fun_prop
    exact hc.intervalIntegrable 0 (2 * a)
  have hFend : F (2 * a) = 0 := by
    simp only [F]
    exact_mod_cast hend
  have hpair := criticalMellinStieltjesPairing_integrationByParts
    ha hF hF' hFend
  rw [ccmPublishedPolarPrimeSineCoefficient, hpair]
  simp only [Complex.neg_re, neg_neg]
  rfl

/-- Physical CCM frequency for half-aperture `a`, so the full logarithmic aperture is `2a`. -/
def ccmPublishedPhysicalFrequency (a : ℝ) (n : ℕ) : ℝ :=
  Real.pi * n / a

/-- Every physical frequency kills the sine test at the full aperture endpoint. -/
theorem sin_ccmPublishedPhysicalFrequency_mul_endpoint
    {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    Real.sin (ccmPublishedPhysicalFrequency a n * (2 * a)) = 0 := by
  have harg : ccmPublishedPhysicalFrequency a n * (2 * a) =
      (2 * n : ℕ) * Real.pi := by
    rw [ccmPublishedPhysicalFrequency]
    push_cast
    field_simp
  rw [harg, Real.sin_nat_mul_pi]

/-- **Published source cosine law.**  At every positive physical CCM aperture, the actual
polar--prime sine coordinate is exactly the completed-error cosine moment divided by `π`. -/
theorem ccmPublishedPolarPrimeSineCoefficient_physical_eq_completedErrorCosineMoment
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ccmPublishedPolarPrimeSineCoefficient a (ccmPublishedPhysicalFrequency a n) =
      ccmCompletedErrorCosineMoment a (ccmPublishedPhysicalFrequency a n) / Real.pi := by
  exact ccmPublishedPolarPrimeSineCoefficient_eq_completedErrorCosineMoment ha.le
    (sin_ccmPublishedPhysicalFrequency_mul_endpoint ha.ne' n)

/-- The full published coefficient is the finite Gamma sine term plus the completed-error cosine
moment.  This is the exact source functional whose sign controls the singular-Loewner obstruction. -/
theorem ccmPublishedSourceSineCoefficient_physical_eq_arch_add_completedErrorCosineMoment
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ccmPublishedSourceSineCoefficient a (ccmPublishedPhysicalFrequency a n) =
      ccmPublishedArchimedeanSineCoefficient a (ccmPublishedPhysicalFrequency a n) +
        ccmCompletedErrorCosineMoment a (ccmPublishedPhysicalFrequency a n) / Real.pi := by
  rw [ccmPublishedSourceSineCoefficient,
    ccmPublishedPolarPrimeSineCoefficient_physical_eq_completedErrorCosineMoment ha n]

/-- The completed-error moment is literally the same moment of the normalized Chebyshev
Volterra potential. -/
theorem ccmCompletedErrorCosineMoment_eq_chebyshevVolterra
    (a ξ : ℝ) :
    ccmCompletedErrorCosineMoment a ξ =
      (∫ h in Ioc (0 : ℝ) (2 * a),
        (criticalMellinChebyshevVolterraPotential h : ℂ) *
          ((ξ * Real.cos (ξ * h) : ℝ) : ℂ)).re := by
  rw [ccmCompletedErrorCosineMoment]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  rw [criticalMellinCompletedError_eq_volterraPotential]
  exact hh.1.le

/-- The published source coordinate vanishes at zero frequency. -/
theorem ccmPublishedSourceSineCoefficient_zero (a : ℝ) :
    ccmPublishedSourceSineCoefficient a 0 = 0 := by
  simp [ccmPublishedSourceSineCoefficient,
    ccmPublishedArchimedeanSineCoefficient,
    ccmPublishedPolarPrimeSineCoefficient,
    criticalMellinStieltjesPairing]

end RHTower
