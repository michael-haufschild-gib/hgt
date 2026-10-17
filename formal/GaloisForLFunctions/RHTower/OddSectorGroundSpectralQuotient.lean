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

private theorem exists_metric_from_positive_compact
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : H →L[ℂ] H) (hK : IsCompactOperator K)
    (hpos : ContinuousLinearMap.IsPositive (𝕜 := ℂ) (E := H) (1-K))
    (hker : ∀ u : H, (1-K) u = 0 → u = 0) :
    ∃ metric : CoerciveInnerProductRenorm.Datum H, ∃ C : ℝ, 0 < C ∧
      ∀ u v : H, inner ℂ (metric.op u) v = (C : ℂ)*inner ℂ ((1-K) u) v := by
  obtain ⟨C,hC,hcoer⟩ := exists_positive_form_scale_of_compact (H := H) K hK hpos hker
  let metric : CoerciveInnerProductRenorm.Datum H :=
    { op := (C : ℂ) • (1-K)
      selfAdjoint := (show IsSelfAdjoint (C : ℂ) from by simp [isSelfAdjoint_iff]).smul
        hpos.isSelfAdjoint
      coercive := fun u => by
        change ‖u‖^2 ≤ (inner ℂ ((C : ℂ) • ((1-K) u)) u).re
        rw [inner_smul_left (𝕜 := ℂ) ((1-K) u) u (C : ℂ)]
        simpa only [Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
          Complex.ofReal_im,zero_mul,sub_zero] using hcoer u }
  refine ⟨metric,C,hC,fun u v => ?_⟩
  change inner ℂ ((C : ℂ) • ((1-K) u)) v = _
  rw [inner_smul_left (𝕜 := ℂ) ((1-K) u) v (C : ℂ),Complex.conj_ofReal]

private def compressedGroundCompact (a : SuzukiPositiveAperture)
    (L : Submodule ℂ (CCMArchimedeanFormDomain a)) [CompleteSpace L] : L →L[ℂ] L :=
  L.orthogonalProjectionOnto.comp ((arithmeticGroundCompact a).comp L.subtypeL)

private theorem compressedGroundCompact_isCompact (a : SuzukiPositiveAperture)
    (L : Submodule ℂ (CCMArchimedeanFormDomain a)) [CompleteSpace L] :
    IsCompactOperator (compressedGroundCompact a L) :=
  ((arithmeticGroundCompact_isCompact a).comp_clm L.subtypeL).clm_comp L.orthogonalProjectionOnto

private theorem inner_compressedGroundForm (a : SuzukiPositiveAperture)
    (L : Submodule ℂ (CCMArchimedeanFormDomain a)) [CompleteSpace L] (u v : L) :
    inner ℂ ((1-compressedGroundCompact a L) u) v = arithmeticShiftedForm a u v := by
  change inner ℂ (u-L.orthogonalProjectionOnto (arithmeticGroundCompact a u)) v = _
  rw [inner_sub_left (𝕜 := ℂ) u
    (L.orthogonalProjectionOnto (arithmeticGroundCompact a u)) v,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  change inner ℂ (u : CCMArchimedeanFormDomain a) v -
    inner ℂ (arithmeticGroundCompact a u) v = _
  rw [← inner_sub_left (𝕜 := ℂ) (u : CCMArchimedeanFormDomain a)
    (arithmeticGroundCompact a u) (v : CCMArchimedeanFormDomain a)]
  exact inner_identity_sub_groundCompact a u v

private theorem compressedGroundForm_positive (a : SuzukiPositiveAperture)
    (L : Submodule ℂ (CCMArchimedeanFormDomain a)) [CompleteSpace L]
    (hodd : ∀ u ∈ L, ccmArchimedeanFormReflection a u = -u) :
    @ContinuousLinearMap.IsPositive ℂ L inferInstance
      (Submodule.normedAddCommGroup L) (Submodule.innerProductSpace L)
      ((1 : L →L[ℂ] L)-compressedGroundCompact a L) := by
  refine ⟨?_,?_⟩
  · intro u v
    change inner ℂ ((1-compressedGroundCompact a L) u) v =
      inner ℂ u ((1-compressedGroundCompact a L) v)
    rw [inner_compressedGroundForm,
      ← inner_conj_symm (𝕜 := ℂ) u ((1-compressedGroundCompact a L) v),
      inner_compressedGroundForm]
    exact arithmeticShiftedForm_conj a v u
  · intro u
    change 0 ≤ (inner ℂ ((1-compressedGroundCompact a L) u) u).re
    rw [inner_compressedGroundForm]
    exact arithmeticShiftedForm_odd_nonneg a ⟨u,hodd u u.property⟩

private theorem compressedGroundForm_kernel (a : SuzukiPositiveAperture)
    (L : Submodule ℂ (CCMArchimedeanFormDomain a)) [CompleteSpace L]
    (hodd : ∀ u ∈ L, ccmArchimedeanFormReflection a u = -u)
    (hzero : ∀ u : L, (u : CCMArchimedeanFormDomain a) ∈ oddArithmeticGroundSpace a → u = 0)
    (u : L) (hu : (1-compressedGroundCompact a L) u = 0) : u = 0 := by
  apply hzero u
  apply (mem_oddArithmeticGroundSpace_iff a u).mpr
  refine ⟨hodd u u.property,?_⟩
  rw [← inner_compressedGroundForm a L u u,hu,inner_zero_left (𝕜 := ℂ) u,Complex.zero_re]

/-- The actual shifted form is coercive on every complete odd subspace
meeting its ground radical only at zero. -/
theorem exists_oddSubspace_coercive_metric (a : SuzukiPositiveAperture)
    (L : Submodule ℂ (CCMArchimedeanFormDomain a)) [CompleteSpace L]
    (hodd : ∀ u ∈ L, ccmArchimedeanFormReflection a u = -u)
    (hzero : ∀ u : L, (u : CCMArchimedeanFormDomain a) ∈ oddArithmeticGroundSpace a → u = 0) :
    ∃ metric : @CoerciveInnerProductRenorm.Datum L (Submodule.normedAddCommGroup L)
      (Submodule.innerProductSpace L) inferInstance, ∃ C : ℝ, 0 < C ∧
      ∀ u v : L, inner ℂ (metric.op u) v = (C : ℂ)*arithmeticShiftedForm a u v := by
  obtain ⟨metric,C,hC,hmetric⟩ := @exists_metric_from_positive_compact L
    (Submodule.normedAddCommGroup L) (Submodule.innerProductSpace L) inferInstance
    (compressedGroundCompact a L) (compressedGroundCompact_isCompact a L)
    (compressedGroundForm_positive a L hodd) (compressedGroundForm_kernel a L hodd hzero)
  refine ⟨metric,C,hC,fun u v => ?_⟩
  rw [hmetric,inner_compressedGroundForm]

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
  let R : CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
    ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a)-N.starProjection
  let T₀ : L →L[ℂ] CCMArchimedeanFormDomain a := R.comp (D.comp L.subtypeL)
  have hTmem (u : L) : T₀ u ∈ L := by
    change D u-N.starProjection (D u) ∈ L
    exact ⟨V.sub_mem (hinv u u.property.1)
      (hground (N.starProjection_apply_mem _)),N.sub_starProjection_mem_orthogonal (D u)⟩
  let T : L →L[ℂ] L := T₀.codRestrict L hTmem
  have hTval (u : L) : (T u : CCMArchimedeanFormDomain a) =
      D u-N.starProjection (D u) := rfl
  have hTcompact : IsCompactOperator T := by
    have hDc : IsCompactOperator D := groundDivisionCLM_isCompact a hG b hb hz
    have hcomp : IsCompactOperator (D.comp L.subtypeL) := hDc.comp_clm L.subtypeL
    have hc₀ : IsCompactOperator T₀ := hcomp.clm_comp R
    exact hc₀.codRestrict hTmem hLclosed
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
