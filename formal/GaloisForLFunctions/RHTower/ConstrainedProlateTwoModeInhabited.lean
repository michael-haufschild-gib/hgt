import GaloisForLFunctions.RHTower.ConstrainedProlatePointwiseRepresentative
import GaloisForLFunctions.RHTower.ConstrainedProlatePoissonMuntz
import GaloisForLFunctions.RHTower.PoissonMuntzRadialSource

/-!
# The two-mode constrained source is inhabited

The canonical constrained source is built from *two* live modes of the even time-band Fourier
block.  Each fixed signed index is live at every large aperture, so the first two indices are
simultaneously live there, and the constrained real source built from them exists with all four of
its analytic properties: integrable, even, compactly supported, of total mass zero.

This inhabits the hypotheses that every downstream statement about the constrained source carries.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace RHTower

/-- The first two signed prolate modes are simultaneously live at every large aperture. -/
theorem eventually_evenProlateSignedValue_ne_zero_pair :
    ∀ᶠ a : ℝ in atTop,
      evenProlateSignedValue a 0 ≠ 0 ∧ evenProlateSignedValue a 1 ≠ 0 :=
  (eventually_evenProlateSignedValue_ne_zero 0).and
    (eventually_evenProlateSignedValue_ne_zero 1)

/-- **The two-mode constrained real source exists.**  At every large aperture the first two signed
modes are live, and the source built from them is integrable, even, compactly supported and of
total mass zero. -/
theorem eventually_exists_twoModeConstrainedRealSource :
    ∀ᶠ a : ℝ in atTop, ∃ g : ℝ → ℝ,
      Integrable g ∧ Function.Even g ∧ HasCompactSupport g ∧ (∫ x : ℝ, g x) = 0 := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    eventually_evenProlateSignedValue_ne_zero 0,
    eventually_evenProlateSignedValue_ne_zero 1] with a ha h0 h1
  have hχ0 : ((evenProlateSignedValue a 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
  have hχ1 : ((evenProlateSignedValue a 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1
  refine ⟨timeBandTwoModeConstrainedRealSource a
      (evenProlateSignedMode a 0) ((evenProlateSignedValue a 0 : ℝ) : ℂ) hχ0
      (evenTimeBandFourier_apply_signedMode a 0)
      (evenProlateSignedMode a 1) ((evenProlateSignedValue a 1 : ℝ) : ℂ) hχ1
      (evenTimeBandFourier_apply_signedMode a 1), ?_, ?_, ?_, ?_⟩
  · exact integrable_timeBandTwoModeConstrainedRealSource a ha.le _ _ hχ0 _ _ _ hχ1 _
  · exact even_timeBandTwoModeConstrainedRealSource a _ _ hχ0 _ _ _ hχ1 _
  · exact hasCompactSupport_timeBandTwoModeConstrainedRealSource a ha.le _ _ hχ0 _ _ _ hχ1 _
  · exact integral_timeBandTwoModeConstrainedRealSource_eq_zero a ha.le _ _ hχ0 _ _ _ hχ1 _

/-- **`(19a)`--`(19b)` for the actual source.**  At every large aperture the constrained two-mode
real source exists and the Abel boundary value of its square-root normalized radial sum is exactly
its full radial source: Poisson centre plus physical lattice charge. -/
theorem eventually_exists_tendsto_poissonMuntzAbelSum_radialFullLogSource {lam t : ℝ}
    (hlam : 0 < lam) :
    ∀ᶠ a : ℝ in atTop, ∃ g : ℝ → ℝ,
      Integrable g ∧ Function.Even g ∧ HasCompactSupport g ∧ (∫ x : ℝ, g x) = 0 ∧
        Tendsto (fun r : ℝ => (Real.sqrt (lam * Real.exp t) : ℂ) *
            poissonMuntzAbelSum g (lam * Real.exp t) r) (𝓝[<] 1)
          (𝓝 ((HTGeometry.radialFullLogSource g lam t : ℝ) : ℂ)) := by
  have hb : (0 : ℝ) < lam * Real.exp t := by positivity
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    eventually_evenProlateSignedValue_ne_zero 0,
    eventually_evenProlateSignedValue_ne_zero 1] with a ha h0 h1
  have hχ0 : ((evenProlateSignedValue a 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
  have hχ1 : ((evenProlateSignedValue a 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1
  refine ⟨timeBandTwoModeConstrainedRealSource a
      (evenProlateSignedMode a 0) ((evenProlateSignedValue a 0 : ℝ) : ℂ) hχ0
      (evenTimeBandFourier_apply_signedMode a 0)
      (evenProlateSignedMode a 1) ((evenProlateSignedValue a 1 : ℝ) : ℂ) hχ1
      (evenTimeBandFourier_apply_signedMode a 1),
    integrable_timeBandTwoModeConstrainedRealSource a ha.le _ _ hχ0 _ _ _ hχ1 _,
    even_timeBandTwoModeConstrainedRealSource a _ _ hχ0 _ _ _ hχ1 _,
    hasCompactSupport_timeBandTwoModeConstrainedRealSource a ha.le _ _ hχ0 _ _ _ hχ1 _,
    integral_timeBandTwoModeConstrainedRealSource_eq_zero a ha.le _ _ hχ0 _ _ _ hχ1 _, ?_⟩
  exact tendsto_sqrt_mul_poissonMuntzAbelSum_eq_radialFullLogSource
    (integrable_timeBandTwoModeConstrainedRealSource a ha.le _ _ hχ0 _ _ _ hχ1 _)
    (even_timeBandTwoModeConstrainedRealSource a _ _ hχ0 _ _ _ hχ1 _)
    (hasCompactSupport_timeBandTwoModeConstrainedRealSource a ha.le _ _ hχ0 _ _ _ hχ1 _)
    hlam
    (integral_timeBandTwoModeConstrainedRealSource_eq_zero a ha.le _ _ hχ0 _ _ _ hχ1 _)
    (tendsto_symmetricLebesgue_timeBandTwoModeConstrainedRealSource ha hb _ _ hχ0 _ _ _ hχ1 _)

end RHTower
