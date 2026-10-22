import GaloisForLFunctions.RHTower.CCM.CCMOddPrimeContinuousCancellation

/-!
# Cofinal compact smooth sources with arbitrarily accurate signed cancellation

The asymptotic pole calculation survives approximation in the complete form
norm. At every sufficiently large aperture there is a nonzero compact smooth
source whose full Weil energy is arbitrarily small relative to its negative
continuous part. The residual's sign is deliberately retained.
-/

noncomputable section
open Filter Set

namespace RHTower

/-- Relative prime--continuous cancellation on the actual odd form-domain sources. -/
theorem eventually_ccmOddPole_relative_cancellation (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a : SuzukiPositiveAperture in atTop,
      |ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))| +
        epsilon * ccmContinuousFormQuadratic a (ccmPolarParityFormVector a (-1)) < 0 := by
  have hq := (tendsto_ccmWeilParityPole_scaled_zero (-1) (Or.inr rfl)).abs
  simp only [abs_zero] at hq
  have hc := tendsto_ccmOddPoleGammaPolarBalance_scaled_neg_two
  filter_upwards [hq.eventually_lt_const hepsilon,
    hc.eventually_lt_const (by norm_num : (-2 : ℝ) < -1)] with a hqa hca
  rw [ccmContinuousFormQuadratic_oddPole]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)] at hqa
  have hscale : Real.exp (-(2 * a.1)) *
      (|ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))| +
        epsilon * ccmOddPoleGammaPolarBalance a) < 0 := by
    have hcε := mul_lt_mul_of_pos_left hca hepsilon
    nlinarith only [hqa, hcε]
  nlinarith only [hscale, Real.exp_pos (-(2 * a.1))]

/-- No approximate or abstract test replaces the actual compact smooth source in this conclusion. -/
theorem exists_cofinal_ccmSmoothSource_relative_cancellation (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : SuzukiPositiveAperture, ∀ a : SuzukiPositiveAperture, A ≤ a →
      ∃ u : CCMComplexSmoothInteriorSource a,
        0 < ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 ∧
        ccmContinuousArithmeticQuadratic u < 0 ∧
        |ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector| <
          epsilon * (-ccmContinuousArithmeticQuadratic u) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_ccmOddPole_relative_cancellation epsilon hepsilon)
  refine ⟨A, ?_⟩
  intro a ha
  let F : CCMArchimedeanFormDomain a → ℝ := fun v =>
    |ccmRestrictedWeilSourceQuadratic a v| + epsilon * ccmContinuousFormQuadratic a v
  have hc : Continuous F := (continuous_ccmRestrictedWeilSourceQuadratic a).abs.add
    ((continuous_ccmContinuousFormQuadratic a).const_mul epsilon)
  have hi : Iio (0 : ℝ) ∈ nhds (F (ccmPolarParityFormVector a (-1))) :=
    Iio_mem_nhds (hA a ha)
  have hmem : {v | F v < 0} ∈ nhds (ccmPolarParityFormVector a (-1)) := hc.continuousAt hi
  obtain ⟨u, hu⟩ := (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).mem_nhds hmem
  change F u.toCCMFormVector < 0 at hu
  have hneg : ccmContinuousFormQuadratic a u.toCCMFormVector < 0 := by
    have habs := abs_nonneg (ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector)
    dsimp only [F] at hu
    nlinarith only [habs, hu, hepsilon]
  have hne : ccmArchimedeanFormToAperture a u.toCCMFormVector ≠ 0 := by
    intro hz
    have hv : u.toCCMFormVector = 0 :=
      ccmArchimedeanFormToAperture_injective a (by simpa only [map_zero] using hz)
    simp only [hv, ccmContinuousFormQuadratic, ccmRestrictedWeilSourceQuadratic_zero,
      map_zero, inner_zero_left, Complex.zero_re, add_zero, lt_self_iff_false] at hneg
  refine ⟨u, sq_pos_of_pos (norm_pos_iff.mpr hne), ?_, ?_⟩
  · rwa [ccmContinuousFormQuadratic_ccmSmooth] at hneg
  · dsimp only [F] at hu
    rw [ccmContinuousFormQuadratic_ccmSmooth] at hu
    linarith only [hu]

end RHTower
