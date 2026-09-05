import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarInverse
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarBombieriYoshida
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarGroundState

/-!
# Exact ground-floor tests on images of the pole multiplier

Every pole-constrained smooth source is the unique image of `g ↦ g'' - g/4`
inside the same aperture. Smooth Rayleigh approximation therefore tests every
lower bound for the completed constrained ground using unrestricted smooth `g`.
The all-aperture nonnegative criterion is equivalent to RH, in both directions.
No sign estimate for the literal arithmetic form is assumed to have been proved.
-/

open Complex MeasureTheory Set

namespace RHTower

/-- Testing all images of the differential pole multiplier determines the exact lower
bound for the completed constrained ground, including at a fixed aperture. -/
theorem le_polarGroundEnergy_iff_polarMultiplier_floor
    (a : SuzukiPositiveAperture) (m : ℝ) :
    m ≤ ccmRestrictedWeilPolarGroundEnergy a ↔
      ∀ g : CCMComplexSmoothInteriorSource a,
        m * ‖ccmArchimedeanFormToAperture a g.polarMultiplier.toCCMFormVector‖ ^ 2 ≤
          ccmRestrictedWeilSourceQuadratic a g.polarMultiplier.toCCMFormVector := by
  constructor
  · intro hm g
    exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans
      (ccmRestrictedWeilPolarGroundEnergy_mul_le a _ (isPolarConstrained_polarMultiplier g))
  · intro hfloor
    by_contra hm
    have hlt : ccmRestrictedWeilPolarGroundEnergy a < m := lt_of_not_ge hm
    obtain ⟨f, hf, hne, hR⟩ := exists_polarConstrained_smooth_rayleigh_lt a (sub_pos.mpr hlt)
    obtain ⟨g, hg⟩ := exists_polarMultiplier_preimage f hf
    have hbound := hfloor g
    rw [hg] at hbound
    have hmass : 0 < ‖ccmArchimedeanFormToAperture a f.toCCMFormVector‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr hne) 2
    have hlower := (le_div_iff₀ hmass).mpr hbound
    linarith

/-- Nonnegative multiplier-image tests are equivalent to nonnegative constrained ground
at the same aperture. -/
theorem polarGroundEnergy_nonneg_iff_polarMultiplier_nonnegative
    (a : SuzukiPositiveAperture) :
    0 ≤ ccmRestrictedWeilPolarGroundEnergy a ↔
      ∀ g : CCMComplexSmoothInteriorSource a,
        0 ≤ ccmRestrictedWeilSourceQuadratic a g.polarMultiplier.toCCMFormVector := by
  simpa only [zero_mul] using le_polarGroundEnergy_iff_polarMultiplier_floor a 0

/-- RH is exactly nonnegativity of the literal source on all differential-multiplier
images. This parametrization has no pole constraints on its smooth input. -/
theorem riemannHypothesis_iff_polarMultiplier_nonnegative :
    RiemannHypothesis ↔ ∀ (a : SuzukiPositiveAperture)
      (g : CCMComplexSmoothInteriorSource a),
        0 ≤ ccmRestrictedWeilSourceQuadratic a g.polarMultiplier.toCCMFormVector := by
  constructor
  · intro hRH a g
    rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm]
    exact suzukiSmoothTestFormNonnegative_of_riemannHypothesis hRH a.1 a.2 _
  · intro hsource
    exact riemannHypothesis_of_polarGroundEnergy_nonneg fun a =>
      (polarGroundEnergy_nonneg_iff_polarMultiplier_nonnegative a).mpr (hsource a)

/-- The constrained all-aperture ground criterion, including its converse. -/
theorem riemannHypothesis_iff_polarGroundEnergy_nonneg :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilPolarGroundEnergy a := by
  constructor
  · intro hRH a
    exact (polarGroundEnergy_nonneg_iff_polarMultiplier_nonnegative a).mpr
      ((riemannHypothesis_iff_polarMultiplier_nonnegative.mp hRH) a)
  · exact riemannHypothesis_of_polarGroundEnergy_nonneg

/-- Failure of RH has a negative smooth witness in the exact image of the pole multiplier. -/
theorem not_riemannHypothesis_iff_exists_negative_polarMultiplier :
    ¬ RiemannHypothesis ↔ ∃ (a : SuzukiPositiveAperture)
      (g : CCMComplexSmoothInteriorSource a),
        ccmRestrictedWeilSourceQuadratic a g.polarMultiplier.toCCMFormVector < 0 := by
  simp only [riemannHypothesis_iff_polarMultiplier_nonnegative, not_forall, not_le]

/-- At a first nonpositive aperture every nonzero smooth constrained interior source
still has strictly positive energy. -/
theorem polarSmoothSource_pos_of_smaller_groundEnergy_pos
    (a : SuzukiPositiveAperture)
    (hbefore : ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
      0 < ccmRestrictedWeilPolarGroundEnergy b)
    (f : CCMComplexSmoothInteriorSource a) (hf : IsPolarConstrained a f.toCCMFormVector)
    (hne : ccmArchimedeanFormToAperture a f.toCCMFormVector ≠ 0) :
    0 < ccmRestrictedWeilSourceQuadratic a f.toCCMFormVector := by
  obtain ⟨b, hba, hs⟩ := exists_strict_smaller_aperture_of_compact_tsupport a f
  let fb := f.restrictAperture b hs
  have hval : f.toCCMFormVector.1 = fb.toCCMFormVector.1 :=
    (f.restrictAperture_toCCMFormVector_val b hs).symm
  have hfb : IsPolarConstrained b fb.toCCMFormVector :=
    (isPolarConstrained_iff_of_val_eq hba.le hval).mp hf
  have hnorm := norm_ccmArchimedeanFormToAperture_eq_of_val_eq hval
  have hbmass : 0 < ‖ccmArchimedeanFormToAperture b fb.toCCMFormVector‖ ^ 2 := by
    rw [← hnorm]
    exact pow_pos (norm_pos_iff.mpr hne) 2
  rw [ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hba.le hval]
  exact (mul_pos (hbefore b hba) hbmass).trans_le
    (ccmRestrictedWeilPolarGroundEnergy_mul_le b _ hfb)

/-- At a first zero the complete multiplier-image core has strictly positive energies
but admits Rayleigh quotients arbitrarily close to zero. -/
theorem polarMultiplier_firstZero_no_uniform_positive_floor
    (a : SuzukiPositiveAperture) (hzero : ccmRestrictedWeilPolarGroundEnergy a = 0)
    (hbefore : ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
      0 < ccmRestrictedWeilPolarGroundEnergy b) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      ccmArchimedeanFormToAperture a g.polarMultiplier.toCCMFormVector ≠ 0 ∧
      0 < ccmRestrictedWeilSourceQuadratic a g.polarMultiplier.toCCMFormVector /
        ‖ccmArchimedeanFormToAperture a g.polarMultiplier.toCCMFormVector‖ ^ 2 ∧
      ccmRestrictedWeilSourceQuadratic a g.polarMultiplier.toCCMFormVector /
        ‖ccmArchimedeanFormToAperture a g.polarMultiplier.toCCMFormVector‖ ^ 2 < ε := by
  obtain ⟨f, hf, hne, hR⟩ := exists_polarConstrained_smooth_rayleigh_lt a hε
  obtain ⟨g, hg⟩ := exists_polarMultiplier_preimage f hf
  refine ⟨g, ?_⟩
  rw [hg]
  rw [hzero, zero_add] at hR
  exact ⟨hne, div_pos (polarSmoothSource_pos_of_smaller_groundEnergy_pos a hbefore f hf hne)
    (pow_pos (norm_pos_iff.mpr hne) 2), hR⟩

/-- Closed alternative: RH holds, or a first constrained null ground coexists with
strict positivity on its entire nonzero smooth interior core and with positive
multiplier-image Rayleigh quotients arbitrarily close to zero. -/
theorem riemannHypothesis_or_polar_firstZero_core_boundary :
    RiemannHypothesis ∨ ∃ (a : SuzukiPositiveAperture) (v : CCMArchimedeanFormDomain a),
      ccmRestrictedWeilPolarGroundEnergy a = 0 ∧
      IsPolarConstrained a v ∧ ‖ccmArchimedeanFormToAperture a v‖ = 1 ∧
      ccmRestrictedWeilSourceQuadratic a v = 0 ∧
      (∀ f : CCMComplexSmoothInteriorSource a, IsPolarConstrained a f.toCCMFormVector →
        ccmArchimedeanFormToAperture a f.toCCMFormVector ≠ 0 →
          0 < ccmRestrictedWeilSourceQuadratic a f.toCCMFormVector) ∧
      (∀ ε : ℝ, 0 < ε → ∃ g : CCMComplexSmoothInteriorSource a,
        ccmArchimedeanFormToAperture a g.polarMultiplier.toCCMFormVector ≠ 0 ∧
        0 < ccmRestrictedWeilSourceQuadratic a g.polarMultiplier.toCCMFormVector /
          ‖ccmArchimedeanFormToAperture a g.polarMultiplier.toCCMFormVector‖ ^ 2 ∧
        ccmRestrictedWeilSourceQuadratic a g.polarMultiplier.toCCMFormVector /
          ‖ccmArchimedeanFormToAperture a g.polarMultiplier.toCCMFormVector‖ ^ 2 < ε) := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    have hnot : ¬ ∀ a : SuzukiPositiveAperture,
        0 ≤ ccmRestrictedWeilPolarGroundEnergy a :=
      fun h => hRH (riemannHypothesis_of_polarGroundEnergy_nonneg h)
    push Not at hnot
    obtain ⟨b, hb⟩ := hnot
    obtain ⟨a, ha, hbefore, _⟩ := exists_polar_degeneracy_threshold hb.le
    obtain ⟨v, hv, hn, hQ⟩ := exists_polarConstrained_groundState a
    exact ⟨a, v, ha, hv, hn, hQ.trans ha,
      polarSmoothSource_pos_of_smaller_groundEnergy_pos a hbefore,
      fun _ hε => polarMultiplier_firstZero_no_uniform_positive_floor a ha hbefore hε⟩

end RHTower
