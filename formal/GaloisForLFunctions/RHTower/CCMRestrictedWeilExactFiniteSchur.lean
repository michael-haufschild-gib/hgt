import GaloisForLFunctions.HTGeometry.CoerciveFiniteSchurComplement
import GaloisForLFunctions.RHTower.CCMRestrictedWeilFiniteNegativeBlock

open scoped InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry ContinuousLinearMap

/-- Bounded zero-energy operator representing the literal restricted-Weil form. -/
def ccmRestrictedWeilZeroFormOperator (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a) -
    ccmRestrictedWeilFormBirmanSchwinger a 0

theorem ccmRestrictedWeilZeroFormOperator_adjoint
    (a : SuzukiPositiveAperture) :
    (ccmRestrictedWeilZeroFormOperator a).adjoint =
      ccmRestrictedWeilZeroFormOperator a := by
  rw [ccmRestrictedWeilZeroFormOperator,
    ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.isSelfAdjoint_iff'.mp
      (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a 0)]

theorem inner_ccmRestrictedWeilZeroFormOperator
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmRestrictedWeilZeroFormOperator a u) v =
      ccmRestrictedWeilForm a u v := by
  rw [ccmRestrictedWeilZeroFormOperator, sub_apply, inner_sub_left,
    id_apply, ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner]

/-- Kernel-checked exact finite-dimensional Schur certificate for one actual CCM aperture. -/
structure CCMRestrictedWeilFiniteSchurCertificate (a : SuzukiPositiveAperture) where
  exterior : Submodule ℂ (CCMArchimedeanFormDomain a)
  exterior_isClosed : IsClosed (exterior : Set (CCMArchimedeanFormDomain a))
  exceptional_finiteDimensional : FiniteDimensional ℂ exteriorᗮ
  exceptionalBlock : exteriorᗮ →L[ℂ] CCMArchimedeanFormDomain a
  coupling : exterior →L[ℂ] CCMArchimedeanFormDomain a
  reverseCoupling : exteriorᗮ →L[ℂ] exterior
  exteriorBlock : exterior →L[ℂ] exterior
  exteriorInverse : exterior →L[ℂ] exterior
  schurComplement : exteriorᗮ →L[ℂ] CCMArchimedeanFormDomain a
  inverse_exterior : ∀ m, exteriorInverse (exteriorBlock m) = m
  exterior_inverse : ∀ m, exteriorBlock (exteriorInverse m) = m
  exterior_coercive : ∀ m : exterior,
    (1 / 2 : ℝ) * ‖m‖ ^ 2 ≤
      (inner ℂ ((exteriorBlock m : exterior) : CCMArchimedeanFormDomain a) (m : CCMArchimedeanFormDomain a)).re
  schur_formula : ∀ f : exteriorᗮ,
    schurComplement f = exceptionalBlock f - coupling (exteriorInverse (reverseCoupling f))
  source_block : ∀ f : exteriorᗮ, ∀ m : exterior,
    (inner ℂ (exceptionalBlock f + coupling m) (f : CCMArchimedeanFormDomain a) +
      inner ℂ (((reverseCoupling f + exteriorBlock m : exterior) : CCMArchimedeanFormDomain a))
        (m : CCMArchimedeanFormDomain a)).re =
      (ccmRestrictedWeilForm a ((f : CCMArchimedeanFormDomain a) + m)
        ((f : CCMArchimedeanFormDomain a) + m)).re
  completed_square : ∀ f : exteriorᗮ, ∀ m : exterior,
    (inner ℂ (exceptionalBlock f + coupling m) (f : CCMArchimedeanFormDomain a) +
      inner ℂ (((reverseCoupling f + exteriorBlock m : exterior) : CCMArchimedeanFormDomain a))
        (m : CCMArchimedeanFormDomain a)).re =
      (inner ℂ (schurComplement f) (f : CCMArchimedeanFormDomain a)).re +
        (inner ℂ
          ((exteriorBlock (m + exteriorInverse (reverseCoupling f)) : exterior) : CCMArchimedeanFormDomain a)
          ((m + exteriorInverse (reverseCoupling f) : exterior) : CCMArchimedeanFormDomain a)).re
  positivity_iff_finiteSchur :
    (∀ u : CCMArchimedeanFormDomain a, 0 ≤ (ccmRestrictedWeilForm a u u).re) ↔
      ∀ f : exteriorᗮ, 0 ≤ (inner ℂ (schurComplement f) (f : CCMArchimedeanFormDomain a)).re

noncomputable def ccmFiniteSchurExceptionalBlock (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a)) [Mᗮ.HasOrthogonalProjection] :
    Mᗮ →L[ℂ] CCMArchimedeanFormDomain a :=
  ccmRestrictedWeilZeroFormOperator a ∘L Mᗮ.subtypeL

noncomputable def ccmFiniteSchurCoupling (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a)) [Mᗮ.HasOrthogonalProjection] :
    M →L[ℂ] CCMArchimedeanFormDomain a :=
  ccmRestrictedWeilZeroFormOperator a ∘L M.subtypeL

noncomputable def ccmFiniteSchurReverseCoupling (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a)) [M.HasOrthogonalProjection] :
    Mᗮ →L[ℂ] M :=
  M.orthogonalProjectionOnto ∘L ccmRestrictedWeilZeroFormOperator a ∘L Mᗮ.subtypeL

noncomputable def ccmFiniteSchurExteriorBlock (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a)) [M.HasOrthogonalProjection] :
    M →L[ℂ] M :=
  finiteSchurExteriorBlock (ccmRestrictedWeilZeroFormOperator a) M

theorem ccmFiniteSchurExteriorBlock_coercive
    (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a))
    [M.HasOrthogonalProjection]
    (hMcoercive : ∀ u ∈ M, u ≠ 0 →
      (1 / 2 : ℝ) * ‖u‖ ^ 2 < (ccmRestrictedWeilForm a u u).re) :
    ∀ m : M, (1 / 2 : ℝ) * ‖m‖ ^ 2 ≤
      (inner ℂ
        ((ccmFiniteSchurExteriorBlock a M m : M) : CCMArchimedeanFormDomain a)
        (m : CCMArchimedeanFormDomain a)).re := by
  intro m
  by_cases hm : m = 0
  · simp [hm]
  have hstrict := hMcoercive (m : CCMArchimedeanFormDomain a) m.property
    (fun h => hm (Subtype.ext h))
  have hinner : (inner ℂ
      ((ccmFiniteSchurExteriorBlock a M m : M) : CCMArchimedeanFormDomain a)
      (m : CCMArchimedeanFormDomain a)).re =
      (ccmRestrictedWeilForm a m m).re := by
    rw [ccmFiniteSchurExteriorBlock, finiteSchurExteriorBlock]
    simp only [ContinuousLinearMap.comp_apply]
    rw [coe_orthogonalProjectionOnto_inner_eq]
    rw [← inner_ccmRestrictedWeilZeroFormOperator]
    simp only [Submodule.subtypeL_apply]
  rw [hinner]
  exact le_of_lt hstrict

theorem ccmFiniteSchurBlock_eq_form
    (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a))
    [CompleteSpace M] [CompleteSpace Mᗮ]
    [M.HasOrthogonalProjection] [Mᗮ.HasOrthogonalProjection]
    (f : Mᗮ) (m : M) :
    (inner ℂ (ccmFiniteSchurExceptionalBlock a M f + ccmFiniteSchurCoupling a M m)
        (f : CCMArchimedeanFormDomain a) +
      inner ℂ (((ccmFiniteSchurReverseCoupling a M f +
        ccmFiniteSchurExteriorBlock a M m : M) : CCMArchimedeanFormDomain a)) (m : CCMArchimedeanFormDomain a)).re =
      (ccmRestrictedWeilForm a ((f : CCMArchimedeanFormDomain a) + m)
        ((f : CCMArchimedeanFormDomain a) + m)).re := by
  unfold ccmFiniteSchurExceptionalBlock ccmFiniteSchurCoupling
    ccmFiniteSchurReverseCoupling ccmFiniteSchurExteriorBlock
  unfold finiteSchurExteriorBlock
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  simp only [Submodule.coe_add]
  rw [inner_add_left]
  rw [inner_add_left]
  rw [coe_orthogonalProjectionOnto_inner_eq,
    coe_orthogonalProjectionOnto_inner_eq]
  rw [← inner_ccmRestrictedWeilZeroFormOperator]
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_re]

theorem ccmFiniteSchurCoupling_pair
    (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a))
    [CompleteSpace M] [CompleteSpace M.orthogonal]
    [M.HasOrthogonalProjection] [M.orthogonal.HasOrthogonalProjection]
    (f : M.orthogonal) (m : M) :
    inner ℂ (ccmFiniteSchurCoupling a M m) (f : CCMArchimedeanFormDomain a) =
      inner ℂ (m : CCMArchimedeanFormDomain a)
        ((ccmFiniteSchurReverseCoupling a M f : M) : CCMArchimedeanFormDomain a) := by
  let T := ccmRestrictedWeilZeroFormOperator a
  have hTsymm (x y : CCMArchimedeanFormDomain a) :
      inner ℂ (T x) y = inner ℂ x (T y) := by
    calc
      inner ℂ (T x) y = inner ℂ x (T.adjoint y) :=
        (T.adjoint_inner_right x y).symm
      _ = inner ℂ x (T y) := by rw [ccmRestrictedWeilZeroFormOperator_adjoint]
  rw [ccmFiniteSchurCoupling, ccmFiniteSchurReverseCoupling]
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [hTsymm]
  exact (inner_coe_orthogonalProjectionOnto_eq M m _).symm

theorem ccmFiniteSchurExteriorBlock_symmetric_ambient
    (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a))
    [CompleteSpace M] [M.HasOrthogonalProjection]
    (m n : M) :
    inner ℂ
        ((ccmFiniteSchurExteriorBlock a M m : M) : CCMArchimedeanFormDomain a)
        (n : CCMArchimedeanFormDomain a) =
      inner ℂ (m : CCMArchimedeanFormDomain a)
        ((ccmFiniteSchurExteriorBlock a M n : M) : CCMArchimedeanFormDomain a) := by
  let T := ccmRestrictedWeilZeroFormOperator a
  have hTsymm (x y : CCMArchimedeanFormDomain a) :
      inner ℂ (T x) y = inner ℂ x (T y) := by
    calc
      inner ℂ (T x) y = inner ℂ x (T.adjoint y) :=
        (T.adjoint_inner_right x y).symm
      _ = inner ℂ x (T y) := by rw [ccmRestrictedWeilZeroFormOperator_adjoint]
  rw [ccmFiniteSchurExteriorBlock, finiteSchurExteriorBlock]
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [coe_orthogonalProjectionOnto_inner_eq, hTsymm,
    inner_coe_orthogonalProjectionOnto_eq]

theorem ccmRestrictedWeilForm_nonneg_iff_finiteSchurBlocks
    (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a))
    [M.HasOrthogonalProjection] [Mᗮ.HasOrthogonalProjection]
    (A : Mᗮ →L[ℂ] CCMArchimedeanFormDomain a) (B : M →L[ℂ] CCMArchimedeanFormDomain a)
    (C : Mᗮ →L[ℂ] M) (D : M →L[ℂ] M)
    (hblock : ∀ f : Mᗮ, ∀ m : M,
      (inner ℂ (A f + B m) (f : CCMArchimedeanFormDomain a) +
        inner ℂ (((C f + D m : M) : CCMArchimedeanFormDomain a)) (m : CCMArchimedeanFormDomain a)).re =
        (ccmRestrictedWeilForm a ((f : CCMArchimedeanFormDomain a) + m)
          ((f : CCMArchimedeanFormDomain a) + m)).re) :
    (∀ u : CCMArchimedeanFormDomain a, 0 ≤ (ccmRestrictedWeilForm a u u).re) ↔
      ∀ f : Mᗮ, ∀ m : M,
        0 ≤ (inner ℂ (A f + B m) (f : CCMArchimedeanFormDomain a) +
          inner ℂ (((C f + D m : M) : CCMArchimedeanFormDomain a)) (m : CCMArchimedeanFormDomain a)).re := by
  constructor
  · intro hfull f m
    rw [hblock f m]
    exact hfull _
  · intro hblocks u
    let m : M := M.orthogonalProjectionOnto u
    let f : Mᗮ := Mᗮ.orthogonalProjectionOnto u
    have hsum : (f : CCMArchimedeanFormDomain a) + m = u := by
      change Mᗮ.starProjection u + M.starProjection u = u
      rw [add_comm]
      exact M.starProjection_add_starProjection_orthogonal u
    have h := hblocks f m
    rw [hblock f m, hsum] at h
    exact h

set_option maxHeartbeats 1000000

/-- The actual CCM restricted-Weil form admits an exact finite-dimensional Schur reduction. -/
theorem exists_ccmRestrictedWeil_exactFiniteSchurComplement
    (a : SuzukiPositiveAperture) :
    Nonempty (CCMRestrictedWeilFiniteSchurCertificate a) := by
  obtain ⟨M, hMclosed, hMfinite, hMcoercive⟩ :=
    exists_ccmRestrictedWeil_finiteSchurBlock a
  letI : CompleteSpace M := hMclosed.completeSpace_coe
  letI : M.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M
  letI : FiniteDimensional ℂ Mᗮ := hMfinite
  letI : CompleteSpace Mᗮ := inferInstance
  letI : Mᗮ.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace Mᗮ
  let A : Mᗮ →L[ℂ] CCMArchimedeanFormDomain a := ccmFiniteSchurExceptionalBlock a M
  let B : M →L[ℂ] CCMArchimedeanFormDomain a := ccmFiniteSchurCoupling a M
  let C : Mᗮ →L[ℂ] M := ccmFiniteSchurReverseCoupling a M
  let D : M →L[ℂ] M := ccmFiniteSchurExteriorBlock a M
  have hDcoercive : ∀ m : M,
      (1 / 2 : ℝ) * ‖m‖ ^ 2 ≤
        (inner ℂ ((D m : M) : CCMArchimedeanFormDomain a) (m : CCMArchimedeanFormDomain a)).re :=
    ccmFiniteSchurExteriorBlock_coercive a M hMcoercive
  have hDcoerciveSubtype : ∀ m : M,
      (1 / 2 : ℝ) * ‖m‖ ^ 2 ≤ (inner ℂ (D m) m).re := by
    intro m
    rw [M.coe_inner]
    exact hDcoercive m
  obtain ⟨Dinv, hDright, hDleft, _hDinvNorm⟩ :=
    @exists_inverse_of_coercive M inferInstance inferInstance inferInstance D
      (1 / 2 : ℝ) (by norm_num) hDcoerciveSubtype
  have hblock : ∀ f : Mᗮ, ∀ m : M,
      (inner ℂ (A f + B m) (f : CCMArchimedeanFormDomain a) +
        inner ℂ (((C f + D m : M) : CCMArchimedeanFormDomain a)) (m : CCMArchimedeanFormDomain a)).re =
        (ccmRestrictedWeilForm a ((f : CCMArchimedeanFormDomain a) + m)
          ((f : CCMArchimedeanFormDomain a) + m)).re :=
    ccmFiniteSchurBlock_eq_form a M
  have hfull_iff_block :
      (∀ u : CCMArchimedeanFormDomain a,
          0 ≤ (ccmRestrictedWeilForm a u u).re) ↔
        ∀ f : Mᗮ, ∀ m : M, 0 ≤
          (inner ℂ (A f + B m) (f : CCMArchimedeanFormDomain a) +
            inner ℂ (((C f + D m : M) : CCMArchimedeanFormDomain a)) (m : CCMArchimedeanFormDomain a)).re :=
    ccmRestrictedWeilForm_nonneg_iff_finiteSchurBlocks a M A B C D hblock
  let S : Mᗮ →L[ℂ] CCMArchimedeanFormDomain a := A - B ∘L Dinv ∘L C
  have hS : ∀ f : Mᗮ, S f = A f - B (Dinv (C f)) := by
    intro f
    rfl
  have hcompleteSquare : ∀ f : Mᗮ, ∀ m : M,
      (inner ℂ (A f + B m) (f : CCMArchimedeanFormDomain a) +
        inner ℂ (((C f + D m : M) : CCMArchimedeanFormDomain a)) (m : CCMArchimedeanFormDomain a)).re =
        (inner ℂ (S f) (f : CCMArchimedeanFormDomain a)).re +
          (inner ℂ
            ((D (m + Dinv (C f)) : M) : CCMArchimedeanFormDomain a)
            ((m + Dinv (C f) : M) : CCMArchimedeanFormDomain a)).re := by
    intro f m
    have hBpair (x : M) :
        inner ℂ (B x) (f : CCMArchimedeanFormDomain a) =
          inner ℂ (x : CCMArchimedeanFormDomain a)
            ((C f : M) : CCMArchimedeanFormDomain a) := by
      simpa only [B, C] using ccmFiniteSchurCoupling_pair a M f x
    have hDsymm (x y : M) :
        inner ℂ ((D x : M) : CCMArchimedeanFormDomain a)
            (y : CCMArchimedeanFormDomain a) =
          inner ℂ (x : CCMArchimedeanFormDomain a)
            ((D y : M) : CCMArchimedeanFormDomain a) := by
      simpa only [D] using ccmFiniteSchurExteriorBlock_symmetric_ambient a M x y
    have hDrightC : D (Dinv (C f)) = C f := hDright _
    rw [hS f]
    simp only [map_add, Submodule.coe_add, inner_add_left, inner_add_right,
      inner_sub_left, Complex.add_re, Complex.sub_re]
    rw [hBpair m, hBpair (Dinv (C f)), hDsymm m (Dinv (C f)),
      hDrightC]
    have hre :
        (inner ℂ ((Dinv (C f) : M) : CCMArchimedeanFormDomain a)
          ((C f : M) : CCMArchimedeanFormDomain a)).re =
        (inner ℂ ((C f : M) : CCMArchimedeanFormDomain a)
          ((Dinv (C f) : M) : CCMArchimedeanFormDomain a)).re := by
      have h := congrArg Complex.re
        (inner_conj_symm
          ((Dinv (C f) : M) : CCMArchimedeanFormDomain a)
          ((C f : M) : CCMArchimedeanFormDomain a))
      simpa only [Complex.conj_re] using h.symm
    rw [hre]
    ring
  refine ⟨⟨M, hMclosed, hMfinite, A, B, C, D, Dinv, S,
    hDleft, hDright, hDcoercive, hS, hblock, hcompleteSquare, ?_⟩⟩
  rw [hfull_iff_block]
  constructor
  · intro hall f
    have h := hall f (-(Dinv (C f)))
    rw [hcompleteSquare f] at h
    simp only [neg_add_cancel, map_zero, Submodule.coe_zero, inner_zero_left,
      Complex.zero_re, add_zero] at h
    exact h
  · intro hschur f m
    rw [hcompleteSquare f m]
    exact add_nonneg (hschur f)
      (le_trans (mul_nonneg (by norm_num) (sq_nonneg _)) (hDcoercive _))

set_option maxHeartbeats 200000

end RHTower

