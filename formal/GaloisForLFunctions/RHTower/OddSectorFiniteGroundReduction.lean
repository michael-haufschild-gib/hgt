import GaloisForLFunctions.RHTower.OddSectorArithmeticGroundOperator

/-!
# A finite-dimensional exact space for every blind odd optimizer

The arithmetic-corrected ground equation is a fixed-point equation for a
compact operator on the complete form domain. Its eigenvalue-one space is
finite dimensional and nonzero. The blind unit section of this single linear
space is exactly the set of all blind minimizers.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry

/-- Compact form-domain operator for the attained arithmetic-corrected energy. -/
def arithmeticGroundCompact (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  (ccmArchimedeanFormToAperture a).adjoint ∘L
    ((blindMinimum a : ℂ) • ContinuousLinearMap.id ℂ (suzukiApertureHilbert a) -
      arithmeticRemainder a) ∘L ccmArchimedeanFormToAperture a

theorem arithmeticGroundCompact_isCompact (a : SuzukiPositiveAperture) :
    IsCompactOperator (arithmeticGroundCompact a) := by
  have h := (isCompactOperator_ccmArchimedeanFormToAperture a).clm_comp
    ((blindMinimum a : ℂ) • ContinuousLinearMap.id ℂ (suzukiApertureHilbert a) -
      arithmeticRemainder a)
  exact h.clm_comp (ccmArchimedeanFormToAperture a).adjoint

theorem inner_arithmeticGroundCompact (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    inner ℂ (arithmeticGroundCompact a u) v =
      (blindMinimum a : ℂ) *
        inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) -
      inner ℂ (arithmeticRemainder a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a v) := by
  change inner ℂ ((ccmArchimedeanFormToAperture a).adjoint
    ((blindMinimum a : ℂ) • ccmArchimedeanFormToAperture a u -
      arithmeticRemainder a (ccmArchimedeanFormToAperture a u))) v = _
  rw [(ccmArchimedeanFormToAperture a).adjoint_inner_left,inner_sub_left,
    inner_smul_left,Complex.conj_ofReal]

theorem arithmeticGroundCompact_fixed_iff (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    arithmeticGroundCompact a u = u ↔
      ∀ v : CCMArchimedeanFormDomain a,arithmeticForm a u v = (blindMinimum a : ℂ) *
        inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
  constructor
  · intro hu v
    have h := inner_arithmeticGroundCompact a u v
    rw [hu] at h
    unfold arithmeticForm
    linear_combination h
  · intro hu
    apply ext_inner_right ℂ
    intro v
    rw [inner_arithmeticGroundCompact]
    have h := hu v
    unfold arithmeticForm at h
    linear_combination -h

/-- The same linear space captures every blind minimizer at this aperture. -/
def arithmeticGroundSpace (a : SuzukiPositiveAperture) :
    Submodule ℂ (CCMArchimedeanFormDomain a) :=
  Module.End.eigenspace (arithmeticGroundCompact a).toLinearMap 1

theorem arithmeticGroundSpace_finiteDimensional (a : SuzukiPositiveAperture) :
    FiniteDimensional ℂ (arithmeticGroundSpace a) :=
  (arithmeticGroundCompact a).finite_dimensional_eigenspace
    (arithmeticGroundCompact_isCompact a) 1 one_ne_zero

theorem mem_arithmeticGroundSpace_iff (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    u ∈ arithmeticGroundSpace a ↔
      ∀ v : CCMArchimedeanFormDomain a,arithmeticForm a u v = (blindMinimum a : ℂ) *
        inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
  rw [arithmeticGroundSpace,Module.End.mem_eigenspace_iff,one_smul]
  exact arithmeticGroundCompact_fixed_iff a u

/-- Membership of a blind unit source is exactly attainment of the original Weil minimum. -/
theorem blind_minimum_iff_mem_arithmeticGroundSpace (a : SuzukiPositiveAperture)
    (u : BlindUnitSource a) :
    ccmRestrictedWeilSourceQuadratic a u.1 = blindMinimum a ↔ u.1 ∈ arithmeticGroundSpace a := by
  constructor
  · intro hu
    exact (mem_arithmeticGroundSpace_iff a u.1).mpr (arithmeticForm_ground_equation a u hu)
  · intro hu
    have h := congrArg Complex.re ((mem_arithmeticGroundSpace_iff a u.1).mp hu u.1)
    rw [arithmeticForm_diagonal a ⟨u.1,u.2.1⟩,formTrace_blind,
      inner_self_eq_norm_sq_to_K] at h
    simpa [formEnergy,u.2.2.1] using h

theorem arithmeticGroundSpace_nontrivial (a : SuzukiPositiveAperture) :
    Nontrivial (arithmeticGroundSpace a) := by
  let u := blindMinimizer a
  have hu : u.1 ∈ arithmeticGroundSpace a :=
    (blind_minimum_iff_mem_arithmeticGroundSpace a u).mp rfl
  apply nontrivial_of_ne (⟨u.1,hu⟩ : arithmeticGroundSpace a) 0
  intro hz
  have he : u.1 = 0 := congrArg Subtype.val hz
  have hn := u.2.2.1
  rw [he,map_zero,norm_zero] at hn
  exact zero_ne_one hn

/-- Every vector in the finite space belongs to the physical operator domain at the exact energy. -/
theorem arithmeticGroundSpace_operator (a : SuzukiPositiveAperture) (u : arithmeticGroundSpace a) :
    ∃ hmem : ccmArchimedeanFormToAperture a u.1 ∈ (arithmeticGroundOperator a).domain,
      arithmeticGroundOperator a ⟨ccmArchimedeanFormToAperture a u.1,hmem⟩ =
        (blindMinimum a : ℂ) • ccmArchimedeanFormToAperture a u.1 := by
  apply boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (ccmArchimedeanFormToAperture a) (arithmeticRemainder a)
    (arithmeticRemainder_isSelfAdjoint a) (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a) u.1
  intro v
  change arithmeticForm a u.1 v = _
  rw [(mem_arithmeticGroundSpace_iff a u.1).mp u.2 v,inner_smul_left,Complex.conj_ofReal]

/-- Unconditional finite-dimensional reduction of the entire blind odd optimizer set,
with the represented operator equation on every vector of the produced space. -/
theorem exists_finite_arithmetic_ground_reduction (a : SuzukiPositiveAperture) :
    ∃ S : Submodule ℂ (CCMArchimedeanFormDomain a),
      FiniteDimensional ℂ S ∧ Nontrivial S ∧
      (∃ u : BlindUnitSource a,u.1 ∈ S) ∧
      (∀ u : BlindUnitSource a,
        ccmRestrictedWeilSourceQuadratic a u.1 = blindMinimum a ↔ u.1 ∈ S) ∧
      ∀ u : S,∃ hmem : ccmArchimedeanFormToAperture a u.1 ∈ (arithmeticGroundOperator a).domain,
        arithmeticGroundOperator a ⟨ccmArchimedeanFormToAperture a u.1,hmem⟩ =
          (blindMinimum a : ℂ) • ccmArchimedeanFormToAperture a u.1 :=
  ⟨arithmeticGroundSpace a,arithmeticGroundSpace_finiteDimensional a,
    arithmeticGroundSpace_nontrivial a,
    ⟨blindMinimizer a,(blind_minimum_iff_mem_arithmeticGroundSpace a (blindMinimizer a)).mp rfl⟩,
    blind_minimum_iff_mem_arithmeticGroundSpace a,
    arithmeticGroundSpace_operator a⟩

end RHTower.OddSector
