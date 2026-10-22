import GaloisForLFunctions.HTGeometry.CompactSelfAdjointReducingTail
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFiniteNegativeBlock

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Exact block-diagonal finite reduction of the literal restricted-Weil form. -/
structure CCMRestrictedWeilReducingBlockCertificate (a : SuzukiPositiveAperture) where
  exterior : Submodule ℂ (CCMArchimedeanFormDomain a)
  exterior_isClosed : IsClosed (exterior : Set (CCMArchimedeanFormDomain a))
  exceptional_finiteDimensional : FiniteDimensional ℂ exterior.orthogonal
  exceptional_eq_peripheralSpectrum : exterior.orthogonal =
    compactPeripheralSpectralSubspace (ccmRestrictedWeilFormBirmanSchwinger a 0) (1 / 2)
  exterior_birmanSchwinger_invariant : ∀ u ∈ exterior,
    ccmRestrictedWeilFormBirmanSchwinger a 0 u ∈ exterior
  exceptional_birmanSchwinger_invariant : ∀ u ∈ exterior.orthogonal,
    ccmRestrictedWeilFormBirmanSchwinger a 0 u ∈ exterior.orthogonal
  exterior_coercive : ∀ u ∈ exterior, u ≠ 0 →
    (1 / 2 : ℝ) * ‖u‖ ^ 2 < (ccmRestrictedWeilForm a u u).re
  mixed_zero : ∀ f : exterior.orthogonal, ∀ m : exterior,
    ccmRestrictedWeilForm a f m = 0 ∧ ccmRestrictedWeilForm a m f = 0
  orthogonal_sum : ∀ f : exterior.orthogonal, ∀ m : exterior,
    (ccmRestrictedWeilForm a
      ((f : CCMArchimedeanFormDomain a) + m)
      ((f : CCMArchimedeanFormDomain a) + m)).re =
      (ccmRestrictedWeilForm a f f).re + (ccmRestrictedWeilForm a m m).re
  positivity_iff_exceptional :
    (∀ u : CCMArchimedeanFormDomain a, 0 ≤ (ccmRestrictedWeilForm a u u).re) ↔
      ∀ f : exterior.orthogonal, 0 ≤ (ccmRestrictedWeilForm a f f).re

/-- The actual compact self-adjoint Birman--Schwinger operator has a reducing finite peripheral
block. Consequently the restricted-Weil form has no Schur coupling tax: whole positivity is exactly
positivity on the finite exceptional block. -/
theorem exists_ccmRestrictedWeil_reducingFiniteBlock
    (a : SuzukiPositiveAperture) :
    Nonempty (CCMRestrictedWeilReducingBlockCertificate a) := by
  let K := ccmRestrictedWeilFormBirmanSchwinger a 0
  have hKcompact : IsCompactOperator K :=
    isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger a 0
  have hKself : K.adjoint = K :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp
      (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a 0)
  obtain ⟨M, hMclosed, hMfinite, hMperipheral, hMinv, hMperpinv, hcontract⟩ :=
    exists_finiteCodimensional_reducing_strictContraction K hKcompact hKself
      (1 / 2 : ℝ) (by norm_num)
  have hcoercive : ∀ u ∈ M, u ≠ 0 →
      (1 / 2 : ℝ) * ‖u‖ ^ 2 < (ccmRestrictedWeilForm a u u).re := by
    intro u hu hune
    have hKnorm : ‖K u‖ < (1 / 2 : ℝ) * ‖u‖ := hcontract u hu hune
    have hid := congrArg Complex.re
      (ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner a u u)
    have hselfinner : (inner ℂ u u).re = ‖u‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
    rw [Complex.sub_re, hselfinner] at hid
    have hcauchy : (inner ℂ (K u) u).re ≤ ‖K u‖ * ‖u‖ := by
      refine le_trans (Complex.re_le_norm _) ?_
      exact norm_inner_le_norm (𝕜 := ℂ) (K u) u
    have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hune
    have hinner : (inner ℂ (K u) u).re < (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
      calc
        _ ≤ ‖K u‖ * ‖u‖ := hcauchy
        _ < ((1 / 2 : ℝ) * ‖u‖) * ‖u‖ := mul_lt_mul_of_pos_right hKnorm hupos
        _ = (1 / 2 : ℝ) * ‖u‖ ^ 2 := by ring
    linarith
  have hmixed : ∀ f : M.orthogonal, ∀ m : M,
      ccmRestrictedWeilForm a f m = 0 ∧ ccmRestrictedWeilForm a m f = 0 := by
    intro f m
    have hfperp : (f : CCMArchimedeanFormDomain a) ∈ M.orthogonal := f.property
    have hKfperp : K (f : CCMArchimedeanFormDomain a) ∈ M.orthogonal :=
      hMperpinv f f.property
    have hminnerf : inner ℂ (m : CCMArchimedeanFormDomain a)
        (f : CCMArchimedeanFormDomain a) = 0 :=
      (Submodule.mem_orthogonal M (f : CCMArchimedeanFormDomain a)).mp hfperp m m.property
    have hfinerm : inner ℂ (f : CCMArchimedeanFormDomain a)
        (m : CCMArchimedeanFormDomain a) = 0 :=
      (inner_eq_zero_symm (x := (m : CCMArchimedeanFormDomain a))
        (y := (f : CCMArchimedeanFormDomain a))).mp hminnerf
    have hKfinerm : inner ℂ (K (f : CCMArchimedeanFormDomain a))
        (m : CCMArchimedeanFormDomain a) = 0 :=
      (inner_eq_zero_symm (x := (m : CCMArchimedeanFormDomain a))
        (y := K (f : CCMArchimedeanFormDomain a))).mp
        ((Submodule.mem_orthogonal M (K (f : CCMArchimedeanFormDomain a))).mp
          hKfperp m m.property)
    have hKminnerf : inner ℂ (K (m : CCMArchimedeanFormDomain a))
        (f : CCMArchimedeanFormDomain a) = 0 :=
      (Submodule.mem_orthogonal M (f : CCMArchimedeanFormDomain a)).mp hfperp
        (K (m : CCMArchimedeanFormDomain a)) (hMinv m m.property)
    constructor
    · rw [ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner,
        hfinerm, hKfinerm, sub_zero]
    · rw [ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner,
        hminnerf, hKminnerf, sub_zero]
  have hsum : ∀ f : M.orthogonal, ∀ m : M,
      (ccmRestrictedWeilForm a
        ((f : CCMArchimedeanFormDomain a) + m)
        ((f : CCMArchimedeanFormDomain a) + m)).re =
        (ccmRestrictedWeilForm a f f).re + (ccmRestrictedWeilForm a m m).re := by
    intro f m
    rw [ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner]
    rw [ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner]
    rw [ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner]
    simp only [map_add, inner_add_left, inner_add_right, Complex.sub_re, Complex.add_re]
    rcases hmixed f m with ⟨hfm, hmf⟩
    rw [ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner] at hfm hmf
    have hfmre := congrArg Complex.re hfm
    have hmfre := congrArg Complex.re hmf
    simp only [Complex.sub_re, Complex.zero_re] at hfmre hmfre
    linarith
  refine ⟨⟨M, hMclosed, hMfinite, hMperipheral, hMinv, hMperpinv,
    hcoercive, hmixed, hsum, ?_⟩⟩
  constructor
  · intro hfull f
    exact hfull f
  · intro hexceptional u
    letI : M.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace M
    letI : M.orthogonal.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace M.orthogonal
    let m : M := M.orthogonalProjectionOnto u
    let f : M.orthogonal := M.orthogonal.orthogonalProjectionOnto u
    have hdecomp : (f : CCMArchimedeanFormDomain a) + m = u := by
      change M.orthogonal.starProjection u + M.starProjection u = u
      rw [add_comm]
      exact M.starProjection_add_starProjection_orthogonal u
    rw [← hdecomp, hsum f m]
    have hmnonneg : 0 ≤ (ccmRestrictedWeilForm a m m).re := by
      by_cases hm : m = 0
      · rw [hm, ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner]
        simp
      exact le_trans
        (mul_nonneg (by norm_num) (sq_nonneg ‖m‖))
        (le_of_lt (hcoercive m m.property (fun h => hm (Subtype.ext h))))
    exact add_nonneg (hexceptional f) hmnonneg

end RHTower
