import GaloisForLFunctions.HTGeometry.ObserverCriticalCarrierConfinementLaw
import GaloisForLFunctions.HTGeometry.SublevelVanishing

/-!
# Analytic observer-minor sublevel law

A selected observer-Jacobian minor that is nonzero at one point has a
Gaussian-null zero set.  Finite Gaussian mass then upgrades nullity to a
fixed-confidence lower-tail statement: for every positive error budget there
is a positive determinant threshold whose sublevel has smaller mass.

This is qualitative rather than a dimension-uniform power law.  It is the
closed finite-system bridge from analytic transversality to robust approximate
observer tubes.
-/

open MeasureTheory ProbabilityTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A globally analytic observer with one nonzero selected jet has a
Gaussian-null selected-minor zero set. -/
theorem analytic_observerMinor_zeroSet_stdGaussian_zero
    {m v : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v)}
    (hF : AnalyticOnNhd ℝ F univ)
    (u : Fin v → EuclideanSpace ℝ (Fin m))
    (hdet0 :
      (observerMinor (fun z => fderiv ℝ F z) u 0).det ≠ 0) :
    stdGaussian (EuclideanSpace ℝ (Fin m))
      {x | (observerMinor (fun z => fderiv ℝ F z) u x).det = 0} = 0 := by
  have hminor := analyticOnNhd_observerMinor_fderiv hF u
  rw [stdGaussian_eq_withDensity]
  apply withDensity_absolutelyContinuous _ _
  apply volume_zero_zeroSet_of_radial_analytic hminor.continuous.measurable
  · intro ω
    have hray : AnalyticOnNhd ℝ
        (fun r : ℝ => r • (ω : EuclideanSpace ℝ (Fin m))) univ :=
      analyticOnNhd_id.smul analyticOnNhd_const
    simpa [Function.comp_def] using hminor.comp hray (mapsTo_univ _ _)
  · exact hdet0

/-- **Fixed-confidence analytic observer lower tail.**  Every positive error
budget admits a positive selected-minor threshold whose Gaussian lower tail is
strictly smaller than that budget. -/
theorem analytic_observerMinor_exists_small_stdGaussian_sublevel
    {m v : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin v)}
    (hF : AnalyticOnNhd ℝ F univ)
    (u : Fin v → EuclideanSpace ℝ (Fin m))
    (hdet0 :
      (observerMinor (fun z => fderiv ℝ F z) u 0).det ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ g : ℝ, 0 < g ∧
        (stdGaussian (EuclideanSpace ℝ (Fin m))).real
          {x | |(observerMinor (fun z => fderiv ℝ F z) u x).det| ≤ g} < ε := by
  intro ε hε
  exact exists_small_sublevel _
    (analyticOnNhd_observerMinor_fderiv hF u).continuous.measurable
    (analytic_observerMinor_zeroSet_stdGaussian_zero hF u hdet0) hε

end

end GaloisForLFunctions.HTGeometry
