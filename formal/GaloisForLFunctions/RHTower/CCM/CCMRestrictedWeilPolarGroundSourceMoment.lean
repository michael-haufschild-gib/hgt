import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarSourceCancellation
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundParityForcing

/-!
# Boundary–arithmetic determination of Weil ground forcing

Self-adjointness and the exact pole Gram matrix determine the one-profile
forcing scalar of an actual constrained parity ground. Its numerator is the
literal boundary-minus-arithmetic-error functional and its denominator is
strictly positive in both parity sectors. The existence theorem retains the
actual unrestricted operator domain and makes no source-sign assumption.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology ENNReal
noncomputable section
namespace RHTower

/-- The actual self-adjoint Weil operator retains the full complex mixed pairing. -/
theorem inner_ccmRestrictedWeilOperator_comm (a : SuzukiPositiveAperture)
    (u v : (ccmRestrictedWeilOperator a).domain) :
    inner ℂ (ccmRestrictedWeilOperator a u) (v : suzukiApertureHilbert a) =
      inner ℂ (u : suzukiApertureHilbert a) (ccmRestrictedWeilOperator a v) := by
  have h := LinearPMap.adjoint_isFormalAdjoint
    (ccmRestrictedWeilOperator_isSelfAdjoint a).dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp (ccmRestrictedWeilOperator_isSelfAdjoint a)] at h
  exact h u v

/-- The exact boundary–arithmetic source functional on the complete form domain. -/
def ccmPolarBoundarySourceFunctional (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] ℂ :=
  (innerSL ℂ (ccmPolarWeilBoundaryDefect a)).comp (ccmArchimedeanFormToAperture a)

/-- Every complete form vector has the actual boundary-minus-arithmetic-error integral. -/
theorem ccmPolarBoundarySourceFunctional_eq_integral (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    ccmPolarBoundarySourceFunctional a u =
      ∫ x : ℝ, (centralInterval a.1).indicator (ccmPolarBoundaryArithmeticProfile a) x *
        (ccmArchimedeanFormToAperture a u : SoninL2) x := by
  change inner ℂ (ccmPolarWeilBoundaryDefect a : SoninL2)
    (ccmArchimedeanFormToAperture a u : SoninL2) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmPolarWeilBoundaryDefect_coeFn a] with x hx
  rw [hx]
  by_cases hm : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hm, RCLike.inner_apply,
      ccmPolarBoundaryArithmeticProfile, Complex.conj_ofReal]
    ring!
  · simp [indicator_of_notMem hm]

/-- Exact self Gram entry of the positive pole. -/
theorem inner_ccmPolarApertureVector_half_self (a : SuzukiPositiveAperture) :
    inner ℂ (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (1/2)) =
      ((2*Real.sinh a.1 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmPolarApertureVector a (1/2))]
  convert congrArg (fun r : ℝ => (r : ℂ)) (norm_sq_ccmPolarApertureVector_half a) using 1
  simp only [Complex.ofReal_pow]
  rfl

/-- Both even and odd pole Gram denominators are strictly positive at every aperture. -/
theorem polarParityGram_pos (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) : 0 < 2*Real.sinh a.1+2*a.1*r := by
  have h := Real.self_lt_sinh_iff.mpr a.property
  rcases hr with rfl | rfl <;> nlinarith [a.property]

/-- The single-profile forcing scalar is exactly the source moment divided by its parity Gram entry. -/
theorem polarSingleForcing_coefficient_eq_source_div (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (r E : ℝ) (hr : r=1 ∨ r=-1) (c : ℂ)
    (hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain)
    (hH : ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
      (E:ℂ) • ccmArchimedeanFormToAperture a u + c •
        (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2))) :
    c = ccmPolarBoundarySourceFunctional a u / ((2*Real.sinh a.1+2*a.1*r:ℝ):ℂ) := by
  have hpair := inner_ccmRestrictedWeilOperator_comm a
    ⟨ccmPolarApertureVector a (1/2),ccmPolarApertureVector_mem_weilOperator_domain a (1/2)⟩
    ⟨ccmArchimedeanFormToAperture a u,hm⟩
  have hs := inner_polarWeil_on_constrained_eq_boundaryArithmetic_integral a ⟨u,hu⟩
  rw [← ccmPolarBoundarySourceFunctional_eq_integral] at hs
  rw [hs,hH] at hpair
  have hcross : inner ℂ (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2)) =
      ((2*a.1:ℝ):ℂ) := by
    simpa only [neg_neg, neg_div] using inner_ccmPolarApertureVector_opposite a (-1/2)
  rw [inner_add_right,
    inner_smul_right (ccmPolarApertureVector a (1/2)) (ccmArchimedeanFormToAperture a u) (E:ℂ),
    inner_smul_right (ccmPolarApertureVector a (1/2))
      (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2)) c,
    inner_add_right,
    inner_smul_right (ccmPolarApertureVector a (1/2)) (ccmPolarApertureVector a (-1/2)) (r:ℂ),
    hu.1, mul_zero, zero_add, inner_ccmPolarApertureVector_half_self, hcross] at hpair
  have hd : (((2*Real.sinh a.1+2*a.1*r:ℝ):ℂ)) ≠ 0 := by
    exact_mod_cast (polarParityGram_pos a hr).ne'
  apply (eq_div_iff hd).mpr
  push_cast at hpair ⊢
  linear_combination -hpair

/-- The exact source functional has its literal L² defect bound. -/
theorem norm_ccmPolarBoundarySourceFunctional_apply_le (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    ‖ccmPolarBoundarySourceFunctional a u‖ ≤
      ‖ccmPolarWeilBoundaryDefect a‖ * ‖ccmArchimedeanFormToAperture a u‖ :=
  norm_inner_le_norm (𝕜 := ℂ) (ccmPolarWeilBoundaryDefect a) (ccmArchimedeanFormToAperture a u)

/-- Hypothesis-free source determination of an actual parity ground's forcing at every aperture. -/
theorem exists_polarGround_boundarySource_forcing (a : SuzukiPositiveAperture) :
    ∃ (u : CCMArchimedeanFormDomain a) (r : ℝ),
      (r=1 ∨ r=-1) ∧ IsPolarConstrained a u ∧
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
      ccmArchimedeanFormReflection a u = (r:ℂ) • u ∧
      ccmRestrictedWeilSourceQuadratic a u =
        ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ∧
      ∃ hm : ccmArchimedeanFormToAperture a u ∈ (ccmRestrictedWeilOperator a).domain,
        ccmRestrictedWeilOperator a ⟨ccmArchimedeanFormToAperture a u,hm⟩ =
          (ccmRestrictedWeilPolarGroundEnergy a:ℂ) • ccmArchimedeanFormToAperture a u +
            (ccmPolarBoundarySourceFunctional a u / ((2*Real.sinh a.1+2*a.1*r:ℝ):ℂ)) •
              (ccmPolarApertureVector a (1/2)+(r:ℂ) • ccmPolarApertureVector a (-1/2)) := by
  obtain ⟨u,r,c,hr,hu,hne,hpar,hQ,hm,hH⟩ := exists_polarGround_singleProfile_forcing a
  have hc := polarSingleForcing_coefficient_eq_source_div a u hu r
    (ccmRestrictedWeilPolarGroundEnergy a) hr c hm hH
  exact ⟨u,r,hr,hu,hne,hpar,hQ,hm,by rwa [← hc]⟩

end RHTower
