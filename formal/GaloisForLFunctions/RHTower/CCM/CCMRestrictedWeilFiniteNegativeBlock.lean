import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaSlepianStrictSource
import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow
import GaloisForLFunctions.HTGeometry.CompactOperatorFiniteSchurReduction

/-!
# Finite negative blocks for the actual CCM restricted-Weil form

At zero energy, the exact restricted-Weil form is the identity form minus the quadratic form of
the actual compact Birman--Schwinger operator.  Consequently that compact operator is bounded
below with constant one on every closed nonpositive block.  Compactness then forces every such
block to be finite-dimensional.

This is the exact finite-Morse reduction for the CCM source: any failure of restricted-Weil
positivity is confined to a finite-dimensional Schur block of the literal prime--polar pencil.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Exact zero-energy identity between the restricted-Weil form and its actual compact
Birman--Schwinger pencil. -/
theorem ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a u v =
      inner ℂ u v -
        inner ℂ (ccmRestrictedWeilFormBirmanSchwinger a 0 u) v := by
  unfold ccmRestrictedWeilForm ccmRestrictedWeilFormBirmanSchwinger
    ccmRestrictedWeilBirmanSchwingerForcing
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

/-- A closed complex subspace on which the actual CCM restricted-Weil form is nonpositive. -/
structure CCMRestrictedWeilNonpositiveBlock (a : SuzukiPositiveAperture) where
  carrier : Submodule ℂ (CCMArchimedeanFormDomain a)
  isClosed : IsClosed (carrier : Set (CCMArchimedeanFormDomain a))
  nonpositive : ∀ u ∈ carrier, (ccmRestrictedWeilForm a u u).re ≤ 0

namespace CCMRestrictedWeilNonpositiveBlock

/-- On every actual nonpositive block, the zero-energy Birman--Schwinger pencil has lower norm
bound exactly one. -/
theorem zeroBirmanSchwinger_boundedBelow
    (a : SuzukiPositiveAperture) (N : CCMRestrictedWeilNonpositiveBlock a) :
    ∀ u ∈ N.carrier, (1 : ℝ) * ‖u‖ ≤
      ‖ccmRestrictedWeilFormBirmanSchwinger a 0 u‖ := by
  intro u hu
  by_cases huz : u = 0
  · simp [huz]
  have hid := congrArg Complex.re
    (ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner a u u)
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  have hinner : ‖u‖ ^ 2 ≤
      (inner ℂ (ccmRestrictedWeilFormBirmanSchwinger a 0 u) u).re := by
    rw [Complex.sub_re] at hid
    rw [hself] at hid
    linarith [N.nonpositive u hu]
  have hcauchy :
      (inner ℂ (ccmRestrictedWeilFormBirmanSchwinger a 0 u) u).re ≤
        ‖ccmRestrictedWeilFormBirmanSchwinger a 0 u‖ * ‖u‖ := by
    refine le_trans (Complex.re_le_norm _) ?_
    exact norm_inner_le_norm (𝕜 := ℂ)
      (ccmRestrictedWeilFormBirmanSchwinger a 0 u) u
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr huz
  simp only [one_mul]
  nlinarith

/-- Every closed nonpositive block of the actual CCM restricted-Weil form is finite-dimensional. -/
theorem finiteDimensional
    (a : SuzukiPositiveAperture) (N : CCMRestrictedWeilNonpositiveBlock a) :
    FiniteDimensional ℂ N.carrier := by
  exact finiteDimensional_of_isCompactOperator_of_bounded_below
    (isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger a 0)
    N.carrier N.isClosed zero_lt_one (N.zeroBirmanSchwinger_boundedBelow a)

end CCMRestrictedWeilNonpositiveBlock

/-- **Actual finite Schur reduction.**  At every aperture there is one closed exterior sector with
finite-dimensional orthogonal complement on which the literal restricted-Weil form is uniformly
coercive.  Thus every negative direction must interact with one finite block; the remaining issue
is the source-specific Schur coupling to that block. -/
theorem exists_ccmRestrictedWeil_finiteSchurBlock
    (a : SuzukiPositiveAperture) :
    ∃ M : Submodule ℂ (CCMArchimedeanFormDomain a),
      IsClosed (M : Set (CCMArchimedeanFormDomain a)) ∧
        FiniteDimensional ℂ Mᗮ ∧
          ∀ u ∈ M, u ≠ 0 →
            (1 / 2 : ℝ) * ‖u‖ ^ 2 < (ccmRestrictedWeilForm a u u).re := by
  let K := ccmRestrictedWeilFormBirmanSchwinger a 0
  obtain ⟨M, hMclosed, hMperp, hcontract⟩ :=
    exists_finiteCodimensional_strictContractionKernel_of_isCompactOperator K
      (isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger a 0)
  refine ⟨M, hMclosed, hMperp, ?_⟩
  intro u hu hune
  have hKnorm : ‖K u‖ < (1 / 2 : ℝ) * ‖u‖ := hcontract u hu hune
  have hid := congrArg Complex.re
    (ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner a u u)
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  rw [Complex.sub_re, hself] at hid
  have hcauchy :
      (inner ℂ (K u) u).re ≤ ‖K u‖ * ‖u‖ := by
    refine le_trans (Complex.re_le_norm _) ?_
    exact norm_inner_le_norm (𝕜 := ℂ) (K u) u
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hune
  have hinner : (inner ℂ (K u) u).re < (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
    calc
      _ ≤ ‖K u‖ * ‖u‖ := hcauchy
      _ < ((1 / 2 : ℝ) * ‖u‖) * ‖u‖ :=
        mul_lt_mul_of_pos_right hKnorm hupos
      _ = (1 / 2 : ℝ) * ‖u‖ ^ 2 := by ring
  linarith

end RHTower
