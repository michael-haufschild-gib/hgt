import GaloisForLFunctions.RHTower.CCMSmallSupportCoercivity
import GaloisForLFunctions.RHTower.CCMThetaThreeEnergyComparison

/-!
# The arithmetic energy comparison on every sufficiently small support set

At each fixed ambient aperture, sources with small total support measure have
an arbitrarily prescribed physical energy margin. The set need not be an
interval or connected. This is an unconditional region of the exact
prime-plus-Gamma versus pole comparison, including all cross interactions.

The threshold depends on the ambient aperture and the requested margin.
No uniform all-aperture estimate, and hence no RH conclusion, is asserted.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace RHTower

open ThetaSourceWard

theorem CCMComplexSmoothInteriorSource.measurableSet_support
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    MeasurableSet (Function.support u) :=
  _root_.measurableSet_support u.continuous.measurable

theorem indicatorCutoff_ccmSmooth_source_support
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    indicatorCutoff (Function.support u) u.measurableSet_support
        (ccmArchimedeanFormEmbedding a u.toCCMFormVector) =
      ccmArchimedeanFormEmbedding a u.toCCMFormVector := by
  have hphysical : (ccmArchimedeanFormEmbedding a u.toCCMFormVector : ℝ → ℂ) =ᵐ[volume] u :=
    u.toCCMFormVector_physical_coeFn
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Function.support u) u.measurableSet_support
    (ccmArchimedeanFormEmbedding a u.toCCMFormVector), hphysical] with x hx hu
  rw [hx]
  by_cases hs : x ∈ Function.support u
  · rw [indicator_of_mem hs]
  · rw [indicator_of_notMem hs, hu]
    exact (Function.notMem_support.mp hs).symm

/-- The restriction norm is the literal local physical L² mass of the smooth source. -/
theorem norm_sq_indicatorCutoff_ccmSmooth
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (s : Set ℝ) (hs : MeasurableSet s) :
    ‖indicatorCutoff s hs (ccmArchimedeanFormEmbedding a u.toCCMFormVector)‖ ^ 2 =
      ∫ x in s, ‖u x‖ ^ 2 := by
  rw [norm_sq_eq_integral, ← integral_indicator hs]
  have hphysical : (ccmArchimedeanFormEmbedding a u.toCCMFormVector : ℝ → ℂ) =ᵐ[volume] u :=
    u.toCCMFormVector_physical_coeFn
  apply integral_congr_ae
  filter_upwards [indicatorCutoff_ae s hs (ccmArchimedeanFormEmbedding a u.toCCMFormVector),
    hphysical] with x hx hu
  rw [hx]
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs, hu]
  · simp only [indicator_of_notMem hxs, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]

/-- Actual smooth sources on arbitrary small sets satisfy the complete Weil coercivity bound. -/
theorem exists_ccmSmooth_smallSupport_coercivity (a : SuzukiPositiveAperture) (L : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ u : CCMComplexSmoothInteriorSource a,
      volume (Function.support u) ≤ ENNReal.ofReal delta →
        L * ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 +
            (1 / 2 : ℝ) * ‖u.toCCMFormVector‖ ^ 2 ≤
          ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_ccmSmallSupport_coercivity a L
  exact ⟨delta, hdelta, fun u hu => hbound (Function.support u) u.measurableSet_support hu
    u.toCCMFormVector (indicatorCutoff_ccmSmooth_source_support u)⟩

/-- Exact arithmetic comparison with arbitrary requested margin and a retained form-norm term. -/
theorem exists_smallMeasure_thetaThreeEnergy_gap (a : SuzukiPositiveAperture) (L : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ u : CCMComplexSmoothInteriorSource a,
      volume (Function.support u) ≤ ENNReal.ofReal delta →
        thetaPolarScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) +
            L * thetaGroundNormSq (ccmThetaGroundProfile u) +
            (1 / 2 : ℝ) * ‖u.toCCMFormVector‖ ^ 2 ≤
          thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
              (ccmThetaGroundProfile u).toBoundedContinuousFunction +
            thetaGammaScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_ccmSmooth_smallSupport_coercivity a L
  refine ⟨delta, hdelta, fun u hu => ?_⟩
  have h := hbound u hu
  rw [ccmRestrictedWeilSourceQuadratic_eq_three_theta_energies,
    ← thetaGroundNormSq_ccmProfile_eq_physical] at h
  linarith

/-- A nonpositive smooth source cannot concentrate an arbitrary fraction of its mass
on sets of vanishing measure. All arithmetic channels remain coupled. -/
theorem exists_ccmSmooth_nonpositive_localMass_fraction
    (a : SuzukiPositiveAperture) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (s : Set ℝ), MeasurableSet s →
      volume s ≤ ENNReal.ofReal delta → ∀ u : CCMComplexSmoothInteriorSource a,
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤ 0 →
          (∫ x in s, ‖u x‖ ^ 2) ≤ epsilon * thetaGroundNormSq (ccmThetaGroundProfile u) := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    exists_ccmNonpositive_smallSet_mass_fraction a epsilon hepsilon
  refine ⟨delta, hdelta, fun s hs hvol u hQ => ?_⟩
  have h := hbound s hs hvol u.toCCMFormVector hQ
  rw [norm_sq_indicatorCutoff_ccmSmooth] at h
  rw [thetaGroundNormSq_ccmProfile_eq_physical]
  exact h

end RHTower
