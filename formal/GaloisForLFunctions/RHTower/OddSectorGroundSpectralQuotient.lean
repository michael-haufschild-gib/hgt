import GaloisForLFunctions.RHTower.OddSectorGroundDivisionCalculus
import GaloisForLFunctions.HTGeometry.CompactPositiveFormGap
import GaloisForLFunctions.HTGeometry.CoerciveCompactSpectralVanishing

/-!
# Spectral detection on the actual odd ground quotient

A closed odd subspace containing the full ground radical and invariant under
normalized division cannot have a nontrivial quotient without a division
eigenvector modulo that radical. Positivity, compactness, and coercivity here
are derived from the actual arithmetic-corrected form.
-/

open Complex Set
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature
open GaloisForLFunctions.HTGeometry

theorem inner_identity_sub_groundCompact (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    inner ℂ ((1-arithmeticGroundCompact a) u) v = arithmeticShiftedForm a u v := by
  change inner ℂ (u-arithmeticGroundCompact a u) v = _
  rw [inner_sub_left,inner_arithmeticGroundCompact]
  unfold arithmeticShiftedForm arithmeticForm
  ring

/-- The actual shifted form is coercive on every complete odd subspace
meeting its ground radical only at zero. -/
theorem exists_oddSubspace_coercive_metric (a : SuzukiPositiveAperture)
    (L : Submodule ℂ (CCMArchimedeanFormDomain a)) [CompleteSpace L]
    (hodd : ∀ u ∈ L, ccmArchimedeanFormReflection a u = -u)
    (hzero : ∀ u : L, (u : CCMArchimedeanFormDomain a) ∈ oddArithmeticGroundSpace a → u = 0) :
    ∃ metric : CoerciveInnerProductRenorm.Datum L, ∃ C : ℝ, 0 < C ∧
      ∀ u v : L, inner ℂ (metric.op u) v = (C : ℂ)*arithmeticShiftedForm a u v := by
  let K : L →L[ℂ] L := L.orthogonalProjectionOnto.comp
    ((arithmeticGroundCompact a).comp L.subtypeL)
  have hK : IsCompactOperator K :=
    ((arithmeticGroundCompact_isCompact a).comp_clm L.subtypeL).clm_comp
      L.orthogonalProjectionOnto
  let B : L →L[ℂ] L := 1-K
  have hform (u v : L) : inner ℂ (B u) v =
      arithmeticShiftedForm a u v := by
    change inner ℂ (u-L.orthogonalProjectionOnto (arithmeticGroundCompact a u)) v = _
    rw [inner_sub_left (𝕜 := ℂ) u
      (L.orthogonalProjectionOnto (arithmeticGroundCompact a u)) v,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    change inner ℂ (u : CCMArchimedeanFormDomain a) v -
      inner ℂ (arithmeticGroundCompact a u) v = _
    rw [← inner_sub_left (𝕜 := ℂ) (u : CCMArchimedeanFormDomain a)
      (arithmeticGroundCompact a u) (v : CCMArchimedeanFormDomain a)]
    exact inner_identity_sub_groundCompact a u v
  have hpos : ContinuousLinearMap.IsPositive (𝕜 := ℂ) (E := L) B := by
    refine ⟨?_,?_⟩
    · intro u v
      change inner ℂ (B u) v = inner ℂ u (B v)
      rw [hform,← inner_conj_symm (𝕜 := ℂ) u (B v),hform]
      exact arithmeticShiftedForm_conj a u v
    · intro u
      change 0 ≤ (inner ℂ (B u) u).re
      rw [hform]
      exact arithmeticShiftedForm_odd_nonneg a ⟨u,hodd u u.property⟩
  have hker : ∀ u : L, B u = 0 → u = 0 := by
    intro u hu
    apply hzero u
    apply (mem_oddArithmeticGroundSpace_iff a u).mpr
    refine ⟨hodd u u.property,?_⟩
    rw [← hform,hu,inner_zero_left (𝕜 := ℂ) u,Complex.zero_re]
  obtain ⟨C,hC,hcoer⟩ := exists_positive_form_scale_of_compact K hK hpos hker
  let metric : CoerciveInnerProductRenorm.Datum L :=
    { op := (C : ℂ) • B
      selfAdjoint := (show IsSelfAdjoint (C : ℂ) from by simp [isSelfAdjoint_iff]).smul
        hpos.isSelfAdjoint
      coercive := fun u => by
        change ‖u‖^2 ≤ (inner ℂ ((C : ℂ) • (B u)) u).re
        rw [inner_smul_left]
        simpa only [Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
          Complex.ofReal_im,zero_mul,sub_zero] using hcoer u }
  refine ⟨metric,C,hC,fun u v => ?_⟩
  change inner ℂ ((C : ℂ) • (B u)) v = _
  rw [inner_smul_left (𝕜 := ℂ),Complex.conj_ofReal,hform]

/-- A closed invariant odd space with no quotient eigenvectors is precisely
the actual ground radical. All analytic hypotheses on the form are discharged. -/
theorem oddGroundSpace_eq_of_division_no_quotient_eigenvectors
    (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    (V : Submodule ℂ (CCMArchimedeanFormDomain a))
    (hclosed : IsClosed (V : Set (CCMArchimedeanFormDomain a)))
    (hodd : ∀ u ∈ V, ccmArchimedeanFormReflection a u = -u)
    (hground : oddArithmeticGroundSpace a ≤ V)
    (hinv : ∀ u ∈ V, groundDivisionCLM a hG b hb hz u ∈ V)
    (hno : ∀ μ : ℂ, ∀ u ∈ V,
      groundDivisionCLM a hG b hb hz u - μ • u ∈ oddArithmeticGroundSpace a →
        u ∈ oddArithmeticGroundSpace a) :
    V = oddArithmeticGroundSpace a := by
  let N := oddArithmeticGroundSpace a
  letI : FiniteDimensional ℂ N := oddArithmeticGroundSpace_finiteDimensional a
  let L : Submodule ℂ (CCMArchimedeanFormDomain a) := V ⊓ Nᗮ
  have hLclosed : IsClosed (L : Set (CCMArchimedeanFormDomain a)) :=
    hclosed.inter N.isClosed_orthogonal
  letI : CompleteSpace L := hLclosed.completeSpace_coe
  have hLzero (u : L) (hu : (u : CCMArchimedeanFormDomain a) ∈ N) : u = 0 := by
    apply Subtype.ext
    exact inner_self_eq_zero.mp (u.property.2 u hu)
  obtain ⟨metric,C,_hC,hmetric⟩ := exists_oddSubspace_coercive_metric a L
    (fun u hu => hodd u hu.1) hLzero
  let D := groundDivisionCLM a hG b hb hz
  let T₀ := ((1-N.starProjection).comp D).comp L.subtypeL
  have hTmem (u : L) : T₀ u ∈ L := by
    change D u-N.starProjection (D u) ∈ L
    exact ⟨V.sub_mem (hinv u u.property.1)
      (hground (N.starProjection_apply_mem _)),N.sub_starProjection_mem_orthogonal (D u)⟩
  let T : L →L[ℂ] L := T₀.codRestrict L hTmem
  have hTval (u : L) : (T u : CCMArchimedeanFormDomain a) =
      D u-N.starProjection (D u) := rfl
  have hTcompact : IsCompactOperator T :=
    (((groundDivisionCLM_isCompact a hG b hb hz).clm_comp (1-N.starProjection)).comp_clm
      L.subtypeL).codRestrict hTmem hLclosed
  have hTsym (u v : L) : inner ℂ (metric.op (T u)) v = inner ℂ (metric.op u) (T v) := by
    rw [hmetric,hmetric]
    congr 1
    rw [hTval,hTval,arithmeticShiftedForm_sub_left,arithmeticShiftedForm_sub_right,
      arithmeticShiftedForm_ground_left a (N.starProjection_apply_mem _),
      arithmeticShiftedForm_ground_right a (N.starProjection_apply_mem _),sub_zero,sub_zero]
    exact (groundDivisionCLM_symmetric_form a hG b hb hz
      (hodd u u.property.1) (hodd v v.property.1)).symm
  have hTno (μ : ℂ) (_hμ : μ ≠ 0) (u : L) (hu : T u = μ • u) : u = 0 := by
    apply hLzero u
    apply hno μ u u.property.1
    have he := congrArg (fun v : L => (v : CCMArchimedeanFormDomain a)) hu
    rw [hTval] at he
    have hid : D u-μ • (u : CCMArchimedeanFormDomain a) = N.starProjection (D u) := by
      change D u-N.starProjection (D u) = μ • (u : CCMArchimedeanFormDomain a) at he
      rw [← he]
      abel
    rw [hid]
    exact N.starProjection_apply_mem _
  have hTzero := CoerciveInnerProductRenorm.compact_eq_zero_of_no_nonzero_eigenvectors
    metric T hTcompact hTsym hTno
  have hallzero (u : L) : u = 0 := by
    apply hLzero u
    apply hno 0 u u.property.1
    simp only [zero_smul,sub_zero]
    have he := hTval u
    rw [hTzero,zero_apply] at he
    have hid : D u = N.starProjection (D u) := (sub_eq_zero.mp he.symm)
    rw [hid]
    exact N.starProjection_apply_mem _
  apply le_antisymm ?_ hground
  intro u hu
  have hm : u-N.starProjection u ∈ L :=
    ⟨V.sub_mem hu (hground (N.starProjection_apply_mem _)),
      N.sub_starProjection_mem_orthogonal u⟩
  have he := congrArg (fun v : L => (v : CCMArchimedeanFormDomain a))
    (hallzero ⟨u-N.starProjection u,hm⟩)
  have hid : u = N.starProjection u := sub_eq_zero.mp he
  rw [hid]
  exact N.starProjection_apply_mem _

end RHTower.OddSector
