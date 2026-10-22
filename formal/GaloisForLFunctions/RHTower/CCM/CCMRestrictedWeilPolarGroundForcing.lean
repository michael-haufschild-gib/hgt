import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarStrictDomain

/-!
# The exact two-pole forcing of a constrained Weil ground

The side-bump moment matrix supplies a section of both pole coordinates on the full form
domain. Its continuous annihilator is exactly the span of those two coordinates. The
constrained ground functional therefore has a physical representative: the ground mass
term plus a unique combination of the literal exponential pole profiles. The converse
Friedrichs representation theorem proves actual unrestricted operator-domain membership.

No regularity of a ground vector or RH premise is used. The forcing coefficients need
not be assumed zero; the resulting equation is a forced equation, not a claimed
unrestricted eigen-equation.
-/

open Complex MeasureTheory Set
open scoped InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- One exponential moment as a continuous functional on the complete form domain. -/
def ccmPolarCoordinate (a : SuzukiPositiveAperture) (s : ℝ) :
    CCMArchimedeanFormDomain a →L[ℂ] ℂ :=
  (innerSL ℂ (ccmPolarApertureVector a s)).comp (ccmArchimedeanFormToAperture a)

/-- A strict-interior section of the two moment coordinates, from the actual side bumps. -/
def ccmPolarCoordinateSection (a : SuzukiPositiveAperture) (cp cm : ℂ) :
    CCMArchimedeanFormDomain a :=
  polarCramerAlpha a cp cm • (polarRightBump a).toCCMFormVector +
    polarCramerBeta a cp cm • (polarLeftBump a).toCCMFormVector

private theorem coordinate_section (a : SuzukiPositiveAperture) (cp cm : ℂ) (s : ℝ) :
    ccmPolarCoordinate a s (ccmPolarCoordinateSection a cp cm) =
      polarCramerAlpha a cp cm * (polarMomentR a s : ℂ) +
        polarCramerBeta a cp cm * (polarMomentL a s : ℂ) := by
  rw [ccmPolarCoordinateSection, map_add, map_smul, map_smul]
  change polarCramerAlpha a cp cm * inner ℂ (ccmPolarApertureVector a s)
    (ccmArchimedeanFormToAperture a (polarRightBump a).toCCMFormVector) +
      polarCramerBeta a cp cm * inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (polarLeftBump a).toCCMFormVector) = _
  rw [inner_polar_polarRightBump, inner_polar_polarLeftBump]

theorem ccmPolarCoordinate_section_plus (a : SuzukiPositiveAperture) (cp cm : ℂ) :
    ccmPolarCoordinate a (1 / 2) (ccmPolarCoordinateSection a cp cm) = cp := by
  rw [coordinate_section]
  linear_combination -polarCramer_plus a cp cm

theorem ccmPolarCoordinate_section_minus (a : SuzukiPositiveAperture) (cp cm : ℂ) :
    ccmPolarCoordinate a (-1 / 2) (ccmPolarCoordinateSection a cp cm) = cm := by
  rw [coordinate_section]
  linear_combination -polarCramer_minus a cp cm

/-- The complete form-domain correction in a biorthogonal pole frame. -/
def ccmPolarCoordinateCorrection (a : SuzukiPositiveAperture)
    (v : CCMArchimedeanFormDomain a) : CCMArchimedeanFormDomain a :=
  v - ccmPolarCoordinate a (1 / 2) v • ccmPolarCoordinateSection a 1 0 -
    ccmPolarCoordinate a (-1 / 2) v • ccmPolarCoordinateSection a 0 1

theorem isPolarConstrained_ccmPolarCoordinateCorrection (a : SuzukiPositiveAperture)
    (v : CCMArchimedeanFormDomain a) :
    IsPolarConstrained a (ccmPolarCoordinateCorrection a v) := by
  change ccmPolarCoordinate a (1 / 2) (ccmPolarCoordinateCorrection a v) = 0 ∧
    ccmPolarCoordinate a (-1 / 2) (ccmPolarCoordinateCorrection a v) = 0
  simp only [ccmPolarCoordinateCorrection, map_sub, map_smul,
    ccmPolarCoordinate_section_plus, ccmPolarCoordinate_section_minus,
    smul_eq_mul, mul_one, mul_zero, sub_self, sub_zero]
  exact ⟨True.intro, True.intro⟩

/-- The two literal pole profiles as physical forcing. -/
def ccmPolarForcing (a : SuzukiPositiveAperture) (c : ℂ × ℂ) : suzukiApertureHilbert a :=
  c.1 • ccmPolarApertureVector a (1 / 2) + c.2 • ccmPolarApertureVector a (-1 / 2)

theorem inner_ccmPolarForcing (a : SuzukiPositiveAperture) (c : ℂ × ℂ)
    (v : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmPolarForcing a c) (ccmArchimedeanFormToAperture a v) =
      (starRingEnd ℂ) c.1 * ccmPolarCoordinate a (1 / 2) v +
        (starRingEnd ℂ) c.2 * ccmPolarCoordinate a (-1 / 2) v := by
  rw [ccmPolarForcing, inner_add_left]
  rw [inner_smul_left (ccmPolarApertureVector a (1 / 2))
    (ccmArchimedeanFormToAperture a v) c.1,
    inner_smul_left (ccmPolarApertureVector a (-1 / 2))
      (ccmArchimedeanFormToAperture a v) c.2]
  rfl

/-- Exact continuous annihilator classification: the two pole coordinates are all the
possible functionals lost on imposing the constraints, with unique physical coefficients. -/
theorem existsUnique_ccmPolarForcing_representative (a : SuzukiPositiveAperture)
    (F : CCMArchimedeanFormDomain a →L[ℂ] ℂ)
    (hF : ∀ v, IsPolarConstrained a v → F v = 0) :
    ∃! c : ℂ × ℂ, ∀ v, F v =
      inner ℂ (ccmPolarForcing a c) (ccmArchimedeanFormToAperture a v) := by
  let ep := ccmPolarCoordinateSection a 1 0
  let em := ccmPolarCoordinateSection a 0 1
  refine ⟨((starRingEnd ℂ) (F ep), (starRingEnd ℂ) (F em)), ?_, ?_⟩
  · intro v
    have hc := hF _ (isPolarConstrained_ccmPolarCoordinateCorrection a v)
    simp only [ccmPolarCoordinateCorrection, map_sub, map_smul, smul_eq_mul] at hc
    rw [inner_ccmPolarForcing]
    simp only [Complex.conj_conj]
    change F v = F ep * ccmPolarCoordinate a (1 / 2) v +
      F em * ccmPolarCoordinate a (-1 / 2) v
    linear_combination hc
  · intro c hc
    have hp := hc ep
    have hm := hc em
    rw [inner_ccmPolarForcing] at hp hm
    simp only [ep, em, ccmPolarCoordinate_section_plus, ccmPolarCoordinate_section_minus,
      mul_one, mul_zero, add_zero, zero_add] at hp hm
    apply Prod.ext
    · simpa only [Complex.conj_conj] using (congrArg (starRingEnd ℂ) hp).symm
    · simpa only [Complex.conj_conj] using (congrArg (starRingEnd ℂ) hm).symm

end RHTower

namespace RHTower

theorem ccmPolarForcing_injective (a : SuzukiPositiveAperture) :
    Function.Injective (ccmPolarForcing a) := by
  intro c d h
  have hp := congrArg (fun f => inner ℂ f (ccmArchimedeanFormToAperture a
    (ccmPolarCoordinateSection a 1 0))) h
  have hm := congrArg (fun f => inner ℂ f (ccmArchimedeanFormToAperture a
    (ccmPolarCoordinateSection a 0 1))) h
  simp only [inner_ccmPolarForcing, ccmPolarCoordinate_section_plus,
    ccmPolarCoordinate_section_minus, mul_one, mul_zero, add_zero, zero_add] at hp hm
  exact Prod.ext (by simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ) hp)
    (by simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ) hm)

/-- Constrained stationarity is the exact annihilation of the shifted form on constrained tests. -/
theorem polarGround_shifted_form_zero (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (hground : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ))
    (v : CCMArchimedeanFormDomain a) (hv : IsPolarConstrained a v) :
    ccmRestrictedWeilForm a u v -
      inner ℂ ((ccmRestrictedWeilPolarGroundEnergy a : ℂ) • ccmArchimedeanFormToAperture a u)
        (ccmArchimedeanFormToAperture a v) = 0 := by
  let K := ccmRestrictedWeilFormBirmanSchwinger a (ccmRestrictedWeilPolarGroundEnergy a)
  have hr := mem_compactConstrainedRadical_of_null (ccmPolarConstraintSubmodule a) K
    (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a _)
    (fun w hw => by
      rw [ccmRestrictedWeil_shifted_diagonal]
      exact sub_nonneg.mpr (ccmRestrictedWeilPolarGroundEnergy_mul_le a w hw)) hu
    (by rw [ccmRestrictedWeil_shifted_diagonal, hground, sub_self])
  have hz := ((mem_compactConstrainedRadical _ K u).mp hr).2 v hv
  have hz' : inner ℂ (u - K u) v = 0 := by
    have hc := congrArg (starRingEnd ℂ) hz
    rw [inner_conj_symm (𝕜 := ℂ) (u - K u) v, map_zero] at hc
    exact hc
  rw [ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger]
  exact hz'

/-- The constrained ground functional has exactly two physical pole-forcing coefficients. -/
theorem existsUnique_polarGround_forcing_form (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (hground : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ)) :
    ∃! c : ℂ × ℂ, ∀ v,
      ccmRestrictedWeilForm a u v =
        inner ℂ ((ccmRestrictedWeilPolarGroundEnergy a : ℂ) •
          ccmArchimedeanFormToAperture a u + ccmPolarForcing a c)
            (ccmArchimedeanFormToAperture a v) := by
  let E := ccmRestrictedWeilPolarGroundEnergy a
  let w := u - ccmRestrictedWeilFormBirmanSchwinger a E u
  let F : CCMArchimedeanFormDomain a →L[ℂ] ℂ := innerSL ℂ w
  have hshift (v : CCMArchimedeanFormDomain a) :
      ccmRestrictedWeilForm a u v -
        inner ℂ ((E : ℂ) • ccmArchimedeanFormToAperture a u)
          (ccmArchimedeanFormToAperture a v) = F v :=
    ccmRestrictedWeilForm_sub_groundMass_eq_inner_one_sub_birmanSchwinger a E u v
  have hF : ∀ v, IsPolarConstrained a v → F v = 0 := by
    intro v hv
    rw [← hshift]
    exact polarGround_shifted_form_zero a u hu hground v hv
  obtain ⟨c, hc, huniq⟩ := existsUnique_ccmPolarForcing_representative a F hF
  refine ⟨c, ?_, ?_⟩
  · intro v
    rw [inner_add_left, ← hc]
    linear_combination hshift v
  · intro d hd
    apply huniq d
    intro v
    have h := hd v
    rw [inner_add_left] at h
    linear_combination h - hshift v

/-- An attained constrained ground belongs to the full unrestricted operator domain.
Its unrestricted eigen-equation has precisely the unique two-pole forcing. -/
theorem existsUnique_polarGround_operator_forcing (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (hground : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ)) :
    ∃! c : ℂ × ℂ, ∃ hmem : ccmArchimedeanFormToAperture a u ∈
      (ccmRestrictedWeilOperator a).domain,
      ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u, hmem⟩ =
        (ccmRestrictedWeilPolarGroundEnergy a : ℂ) • ccmArchimedeanFormToAperture a u +
          ccmPolarForcing a c := by
  obtain ⟨c, hc, _⟩ := existsUnique_polarGround_forcing_form a u hu hground
  obtain ⟨hm, hA⟩ := boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (ccmArchimedeanFormToAperture a) (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a) (denseRange_ccmArchimedeanFormToAperture a)
    u ((ccmRestrictedWeilPolarGroundEnergy a : ℂ) • ccmArchimedeanFormToAperture a u +
      ccmPolarForcing a c) hc
  refine ⟨c, ⟨hm, hA⟩, ?_⟩
  rintro d ⟨hdm, hd⟩
  apply ccmPolarForcing_injective a
  exact add_left_cancel (hd.symm.trans hA)

/-- Hypothesis-free actual-source existence: every aperture has a normalized constrained
operator ground with uniquely determined forcing in the two literal pole profiles. -/
theorem exists_normalized_polarGround_operator_forcing (a : SuzukiPositiveAperture) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ‖ccmArchimedeanFormToAperture a u‖ = 1 ∧
      ccmRestrictedWeilSourceQuadratic a u = ccmRestrictedWeilPolarGroundEnergy a ∧
      ∃! c : ℂ × ℂ, ∃ hmem : ccmArchimedeanFormToAperture a u ∈
        (ccmRestrictedWeilOperator a).domain,
        ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u, hmem⟩ =
          (ccmRestrictedWeilPolarGroundEnergy a : ℂ) • ccmArchimedeanFormToAperture a u +
            ccmPolarForcing a c := by
  obtain ⟨u, hu, hn, hQ⟩ := exists_polarConstrained_groundState a
  refine ⟨u, hu, hn, hQ, existsUnique_polarGround_operator_forcing a u hu ?_⟩
  simpa only [hn, one_pow, mul_one] using hQ

end RHTower
