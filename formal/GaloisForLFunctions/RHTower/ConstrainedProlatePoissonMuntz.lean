import GaloisForLFunctions.RHTower.ConstrainedProlatePointwiseRepresentative
import GaloisForLFunctions.RHTower.PoissonMuntzAbelMeanDefect

/-!
# Unconditional Poisson--Muntz law for canonical constrained prolate sources

The canonical two-mode source uses half endpoint values.  This makes every integer-aperture
boundary collision continuous after periodization.  Consequently the symmetric-Lebesgue input in
the general Poisson--Muntz theorem is automatic, and the zero-mean Abel boundary law applies with
no analytic hypothesis beyond positive apertures and nonzero eigenvalues.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Canonical constrained prolate sources have collision-continuous scaled periodizations. -/
theorem continuousAt_poissonMuntzScaledPeriodization_timeBandTwoModeConstrainedRealSource
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    ContinuousAt
      (poissonMuntzScaledPeriodization
        (timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
          f₁ χ₁ hχ₁ heig₁) b) 0 := by
  unfold poissonMuntzScaledPeriodization
  rw [timeBandTwoModeConstrainedRealSource_eq_halfEndpointCutoff]
  exact continuousAt_realL1Periodization_symmetricHalfEndpointCutoff_zero ha hb
    (continuous_timeBandTwoModeContinuousRealProfile a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁)
    (even_timeBandTwoModeContinuousRealProfile a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁)

/-- Symmetric-Lebesgue regularity is automatic for every canonical two-mode prolate source. -/
theorem tendsto_symmetricLebesgue_timeBandTwoModeConstrainedRealSource
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Tendsto (fun s : ℝ =>
      ((∫ t in (0 : ℝ)..s,
        |poissonMuntzAngularDatum
            (timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
              f₁ χ₁ hχ₁ heig₁) b t -
          poissonMuntzAngularDatum
            (timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
              f₁ χ₁ hχ₁ heig₁) b 0| +
        |poissonMuntzAngularDatum
            (timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
              f₁ χ₁ hχ₁ heig₁) b (-t) -
          poissonMuntzAngularDatum
            (timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
              f₁ χ₁ hχ₁ heig₁) b 0|) / s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact tendsto_poissonMuntz_symmetricLebesgueAverage_of_continuousAt
    (integrable_timeBandTwoModeConstrainedRealSource a ha.le
      f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁) hb
    (continuousAt_poissonMuntzScaledPeriodization_timeBandTwoModeConstrainedRealSource
      ha hb f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁)

/-- **Unconditional canonical prolate Poisson--Muntz boundary law.**  Every nonzero two-mode
time-band eigenpacket has an exact zero-mean real source whose square-root-normalized positive
Fourier-sample Abel tail converges to its endpoint-safe physical lattice charge. -/
theorem tendsto_sqrt_mul_poissonMuntzAbelSum_timeBandTwoModeConstrainedRealSource
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Tendsto (fun r : ℝ => (Real.sqrt b : ℂ) *
      poissonMuntzAbelSum
        (timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
          f₁ χ₁ hχ₁ heig₁) b r)
      (𝓝[<] 1)
      (𝓝 (((timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
          f₁ χ₁ hχ₁ heig₁ 0 : ℝ) : ℂ) /
            (2 * (Real.sqrt b : ℂ)) +
        ((∑' n : ℕ, timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
          f₁ χ₁ hχ₁ heig₁ ((n + 1 : ℝ) / b)) : ℂ) /
            (Real.sqrt b : ℂ))) := by
  exact tendsto_sqrt_mul_poissonMuntzAbelSum_physicalLattice_of_compactSupport
    (integrable_timeBandTwoModeConstrainedRealSource a ha.le
      f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁)
    (even_timeBandTwoModeConstrainedRealSource a
      f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁)
    (hasCompactSupport_timeBandTwoModeConstrainedRealSource a ha.le
      f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁)
    hb
    (integral_timeBandTwoModeConstrainedRealSource_eq_zero a ha.le
      f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁)
    (tendsto_symmetricLebesgue_timeBandTwoModeConstrainedRealSource
      ha hb f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁)

end RHTower
