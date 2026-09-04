import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicIndex
import GaloisForLFunctions.HTGeometry.CompactPerturbationFredholm
import GaloisForLFunctions.RHTower.CCMArithmeticPrimeFredholmOrientation

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

def RestrictedUnitaryDatum.compression (D : RestrictedUnitaryDatum H) :
    LinearMap.range (D.projection : H →ₗ[ℂ] H) →L[ℂ]
      LinearMap.range (D.projection : H →ₗ[ℂ] H) :=
  (D.projection.codRestrict
      (LinearMap.range (D.projection : H →ₗ[ℂ] H))
      (fun x => ⟨x, rfl⟩)).comp
    (D.unitary.comp
      (LinearMap.range (D.projection : H →ₗ[ℂ] H)).subtypeL)

def RestrictedUnitaryDatum.adjointCompression (D : RestrictedUnitaryDatum H) :
    LinearMap.range (D.projection : H →ₗ[ℂ] H) →L[ℂ]
      LinearMap.range (D.projection : H →ₗ[ℂ] H) :=
  (D.projection.codRestrict
      (LinearMap.range (D.projection : H →ₗ[ℂ] H))
      (fun x => ⟨x, rfl⟩)).comp
    ((ContinuousLinearMap.adjoint D.unitary).comp
      (LinearMap.range (D.projection : H →ₗ[ℂ] H)).subtypeL)

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.isClosed_range_projection
    (D : RestrictedUnitaryDatum H) :
    IsClosed ((LinearMap.range (D.projection : H →ₗ[ℂ] H) :
      Submodule ℂ H) : Set H) := by
  have heq : LinearMap.range (D.projection : H →ₗ[ℂ] H) =
      LinearMap.ker ((D.projection - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    ext x
    rw [mem_range_restrictedProjection_iff_apply_eq
      D.projection D.projection_idempotent]
    rw [LinearMap.mem_ker]
    change D.projection x = x ↔ D.projection x - x = 0
    constructor
    · exact sub_eq_zero.mpr
    · exact sub_eq_zero.mp
  rw [heq]
  exact ContinuousLinearMap.isClosed_ker (D.projection - 1)

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.compression_apply_coe
    (D : RestrictedUnitaryDatum H)
    (x : LinearMap.range (D.projection : H →ₗ[ℂ] H)) :
    ((D.compression x : LinearMap.range
      (D.projection : H →ₗ[ℂ] H)) : H) = D.projection (D.unitary x) := rfl

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.adjointCompression_apply_coe
    (D : RestrictedUnitaryDatum H)
    (x : LinearMap.range (D.projection : H →ₗ[ℂ] H)) :
    ((D.adjointCompression x : LinearMap.range
      (D.projection : H →ₗ[ℂ] H)) : H) =
      D.projection (ContinuousLinearMap.adjoint D.unitary x) := rfl

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.adjoint_compression
    (D : RestrictedUnitaryDatum H) :
    letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
      D.isClosed_range_projection.completeSpace_coe
    ContinuousLinearMap.adjoint D.compression = D.adjointCompression := by
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_right ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (y : H) (D.projection (D.unitary x)) =
    inner ℂ (D.projection (ContinuousLinearMap.adjoint D.unitary y)) (x : H)
  have hx : D.projection (x : H) = x :=
    (mem_range_restrictedProjection_iff_apply_eq
      D.projection D.projection_idempotent x).mp x.2
  have hy : D.projection (y : H) = y :=
    (mem_range_restrictedProjection_iff_apply_eq
      D.projection D.projection_idempotent y).mp y.2
  calc
    inner ℂ (y : H) (D.projection (D.unitary x)) =
        inner ℂ (ContinuousLinearMap.adjoint D.projection (y : H))
          (D.unitary x) :=
      (ContinuousLinearMap.adjoint_inner_left
        D.projection (D.unitary x) (y : H)).symm
    _ = inner ℂ (y : H) (D.unitary x) := by
      simp only [D.projection_adjoint, hy]
    _ = inner ℂ (ContinuousLinearMap.adjoint D.unitary (y : H)) (x : H) :=
      (ContinuousLinearMap.adjoint_inner_left D.unitary (x : H) (y : H)).symm
    _ = inner ℂ
        (D.projection (ContinuousLinearMap.adjoint D.unitary (y : H))) (x : H) := by
      simpa only [D.projection_adjoint, hx] using
        (ContinuousLinearMap.adjoint_inner_right
          D.projection (ContinuousLinearMap.adjoint D.unitary (y : H)) (x : H))

def RestrictedUnitaryDatum.compressionGramDefect
    (D : RestrictedUnitaryDatum H) :
    LinearMap.range (D.projection : H →ₗ[ℂ] H) →L[ℂ]
      LinearMap.range (D.projection : H →ₗ[ℂ] H) :=
  (D.projection.codRestrict
      (LinearMap.range (D.projection : H →ₗ[ℂ] H))
      (fun x => ⟨x, rfl⟩)).comp
    ((ContinuousLinearMap.adjoint D.unitary).comp
      ((D.projection * D.unitary - D.unitary * D.projection).comp
        (D.projection.comp
          (LinearMap.range (D.projection : H →ₗ[ℂ] H)).subtypeL)))

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.compressionGramDefect_isCompactOperator
    (D : RestrictedUnitaryDatum H) :
    IsCompactOperator D.compressionGramDefect := by
  have hcompact : IsCompactOperator
      (D.projection * D.unitary - D.unitary * D.projection) :=
    D.commutator_isHilbertSchmidt.isCompactOperator
  have hpre := hcompact.comp_clm
    (D.projection.comp
      (LinearMap.range (D.projection : H →ₗ[ℂ] H)).subtypeL)
  have hmid := hpre.clm_comp (ContinuousLinearMap.adjoint D.unitary)
  have hpost := hmid.clm_comp
    (D.projection.codRestrict
      (LinearMap.range (D.projection : H →ₗ[ℂ] H))
      (fun x => ⟨x, rfl⟩))
  change IsCompactOperator (fun x =>
    (D.projection.codRestrict
      (LinearMap.range (D.projection : H →ₗ[ℂ] H))
      (fun z => ⟨z, rfl⟩))
      (ContinuousLinearMap.adjoint D.unitary
        ((D.projection * D.unitary - D.unitary * D.projection)
          (D.projection ((LinearMap.range
            (D.projection : H →ₗ[ℂ] H)).subtypeL x)))))
  exact hpost

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.adjointCompression_comp_compression
    (D : RestrictedUnitaryDatum H) :
    D.adjointCompression.comp D.compression = 1 + D.compressionGramDefect := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  have hx : D.projection (x : H) = x :=
    (mem_range_restrictedProjection_iff_apply_eq
      D.projection D.projection_idempotent x).mp x.2
  have hPP : D.projection * D.projection = D.projection :=
    D.projection_idempotent
  have hUU : ContinuousLinearMap.adjoint D.unitary * D.unitary = 1 :=
    D.adjoint_mul_unitary
  have hinner : ContinuousLinearMap.adjoint D.unitary *
      (D.unitary * D.projection) = D.projection := by
    rw [← mul_assoc, hUU, one_mul]
  have hcollapse : D.projection *
      (ContinuousLinearMap.adjoint D.unitary *
        (D.unitary * D.projection)) = D.projection := by
    rw [hinner, hPP]
  change D.projection (ContinuousLinearMap.adjoint D.unitary
      (D.projection (D.unitary x))) =
    x + D.projection (ContinuousLinearMap.adjoint D.unitary
      ((D.projection * D.unitary - D.unitary * D.projection)
        (D.projection x)))
  have hop : D.projection * ContinuousLinearMap.adjoint D.unitary *
        D.projection * D.unitary * D.projection =
      D.projection + D.projection * ContinuousLinearMap.adjoint D.unitary *
        (D.projection * D.unitary - D.unitary * D.projection) * D.projection := by
    noncomm_ring [hcollapse, hPP]
  simpa [mul_apply_eq_comp, hx] using
    congrArg (fun T : H →L[ℂ] H => T (x : H)) hop

theorem RestrictedUnitaryDatum.isClosed_range_compression
    (D : RestrictedUnitaryDatum H) :
    letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
      D.isClosed_range_projection.completeSpace_coe
    IsClosed (Set.range D.compression) := by
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  have hgram : (ContinuousLinearMap.adjoint D.compression).comp D.compression =
      1 + D.compressionGramDefect := by
    rw [D.adjoint_compression]
    exact D.adjointCompression_comp_compression
  have hclosedGram : IsClosed
      (Set.range ((ContinuousLinearMap.adjoint D.compression).comp D.compression)) := by
    rw [hgram]
    exact GaloisForLFunctions.HTGeometry.isClosed_range_one_add_of_isCompactOperator
      D.compressionGramDefect D.compressionGramDefect_isCompactOperator
  exact GaloisForLFunctions.HTGeometry.isClosed_range_of_isClosed_range_adjoint_comp_self
    D.compression hclosedGram

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.finiteDimensional_ker_compression
    (D : RestrictedUnitaryDatum H) :
    letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
      D.isClosed_range_projection.completeSpace_coe
    FiniteDimensional ℂ (LinearMap.ker (D.compression :
      LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
        LinearMap.range (D.projection : H →ₗ[ℂ] H))) := by
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  have hfd := GaloisForLFunctions.HTGeometry.finiteDimensional_ker_one_add_of_isCompactOperator
    D.compressionGramDefect D.compressionGramDefect_isCompactOperator
  have hker := GaloisForLFunctions.HTGeometry.ker_adjoint_comp_self D.compression
  rw [D.adjoint_compression, D.adjointCompression_comp_compression] at hker
  rw [← hker]
  exact hfd

omit [TopologicalSpace.SeparableSpace H] in
def RestrictedUnitaryDatum.adjointDatum (D : RestrictedUnitaryDatum H) :
    RestrictedUnitaryDatum H where
  projection := D.projection
  unitary := ContinuousLinearMap.adjoint D.unitary
  projection_idempotent := D.projection_idempotent
  projection_adjoint := D.projection_adjoint
  adjoint_mul_unitary := by
    rw [ContinuousLinearMap.adjoint_adjoint]
    exact D.unitary_mul_adjoint
  unitary_mul_adjoint := by
    rw [ContinuousLinearMap.adjoint_adjoint]
    exact D.adjoint_mul_unitary
  commutator_isHilbertSchmidt := by
    have h := D.commutator_isHilbertSchmidt.adjoint.neg
    simpa only [ContinuousLinearMap.adjoint.map_sub,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      D.projection_adjoint, ContinuousLinearMap.mul_def, neg_sub] using h

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.adjointDatum_compression
    (D : RestrictedUnitaryDatum H) :
    D.adjointDatum.compression = D.adjointCompression := rfl

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.finiteDimensional_ker_adjointCompression
    (D : RestrictedUnitaryDatum H) :
    letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
      D.isClosed_range_projection.completeSpace_coe
    FiniteDimensional ℂ (LinearMap.ker (D.adjointCompression :
      LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
        LinearMap.range (D.projection : H →ₗ[ℂ] H))) := by
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  rw [← D.adjointDatum_compression]
  exact D.adjointDatum.finiteDimensional_ker_compression

theorem RestrictedUnitaryDatum.finiteDimensional_coker_compression
    (D : RestrictedUnitaryDatum H) :
    letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
      D.isClosed_range_projection.completeSpace_coe
    FiniteDimensional ℂ
      (LinearMap.range (D.projection : H →ₗ[ℂ] H) ⧸
        LinearMap.range (D.compression :
          LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
            LinearMap.range (D.projection : H →ₗ[ℂ] H))) := by
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  let S := LinearMap.range (D.compression :
    LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
      LinearMap.range (D.projection : H →ₗ[ℂ] H))
  have hclosedS : IsClosed (S : Set
      (LinearMap.range (D.projection : H →ₗ[ℂ] H))) := by
    exact D.isClosed_range_compression
  letI : S.HasOrthogonalProjection :=
    GaloisForLFunctions.HTGeometry.hasOrthogonalProjection_of_isClosed hclosedS
  haveI hfdOrth : FiniteDimensional ℂ Sᗮ := by
    rw [show Sᗮ = LinearMap.ker
        ((ContinuousLinearMap.adjoint D.compression :
          LinearMap.range (D.projection : H →ₗ[ℂ] H) →L[ℂ]
            LinearMap.range (D.projection : H →ₗ[ℂ] H)) :
          LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
            LinearMap.range (D.projection : H →ₗ[ℂ] H)) by
      exact ContinuousLinearMap.orthogonal_range D.compression]
    rw [D.adjoint_compression]
    exact D.finiteDimensional_ker_adjointCompression
  exact (Submodule.quotientEquivOrthogonal S).toLinearEquiv.symm.finiteDimensional

def RestrictedUnitaryDatum.compressionPMap (D : RestrictedUnitaryDatum H) :
    LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ.[ℂ]
      LinearMap.range (D.projection : H →ₗ[ℂ] H) :=
  D.compression.toLinearMap.toPMap ⊤

theorem RestrictedUnitaryDatum.compressionPMap_isFredholm
    (D : RestrictedUnitaryDatum H) :
    letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
      D.isClosed_range_projection.completeSpace_coe
    D.compressionPMap.IsFredholm := by
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  refine {
    finiteDimensional_kernel := ?_
    isClosed_range := ?_
    finiteDimensional_cokernel := ?_ }
  · rw [RestrictedUnitaryDatum.compressionPMap, kernel_toPMap_top]
    exact D.finiteDimensional_ker_compression
  · rw [RestrictedUnitaryDatum.compressionPMap, rangeSubmodule_toPMap_top]
    exact D.isClosed_range_compression
  · rw [RestrictedUnitaryDatum.compressionPMap, rangeSubmodule_toPMap_top]
    exact D.finiteDimensional_coker_compression

omit [TopologicalSpace.SeparableSpace H] in
def RestrictedUnitaryDatum.compressionKernelEquivNegativeEndpoint
    (D : RestrictedUnitaryDatum H) :
    LinearMap.ker (D.compression :
      LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
        LinearMap.range (D.projection : H →ₗ[ℂ] H)) ≃ₗ[ℂ]
      ↥(LinearMap.range (D.projection : H →ₗ[ℂ] H) ⊓
        LinearMap.ker (D.conjugateProjection : H →ₗ[ℂ] H)) where
  toFun x := ⟨(x.1 : H), x.1.2, by
    have hPU := congrArg (fun y : LinearMap.range
      (D.projection : H →ₗ[ℂ] H) => (y : H)) x.2
    change D.projection (D.unitary (x.1 : H)) = 0 at hPU
    change ContinuousLinearMap.adjoint D.unitary
      (D.projection (D.unitary (x.1 : H))) = 0
    rw [hPU, map_zero]⟩
  invFun z := ⟨⟨(z : H), z.2.1⟩, by
    have hR : D.conjugateProjection (z : H) = 0 := z.2.2
    change ContinuousLinearMap.adjoint D.unitary
      (D.projection (D.unitary (z : H))) = 0 at hR
    have hUR := congrArg D.unitary hR
    have hcancel : ∀ y : H,
        D.unitary (ContinuousLinearMap.adjoint D.unitary y) = y := by
      intro y
      have h := congrArg (fun T : H →L[ℂ] H => T y) D.unitary_mul_adjoint
      simpa [mul_apply_eq_comp] using h
    simp only [map_zero] at hUR
    rw [hcancel] at hUR
    apply Subtype.ext
    exact hUR⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.finrank_ker_compression_eq_negativeEndpoint
    (D : RestrictedUnitaryDatum H) :
    Module.finrank ℂ (LinearMap.ker (D.compression :
      LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
        LinearMap.range (D.projection : H →ₗ[ℂ] H))) =
      Module.finrank ℂ
        ↥(LinearMap.range (D.projection : H →ₗ[ℂ] H) ⊓
          LinearMap.ker (D.conjugateProjection : H →ₗ[ℂ] H)) :=
  D.compressionKernelEquivNegativeEndpoint.finrank_eq

omit [TopologicalSpace.SeparableSpace H] in
def RestrictedUnitaryDatum.adjointCompressionKernelEquivPositiveEndpoint
    (D : RestrictedUnitaryDatum H) :
    LinearMap.ker (D.adjointCompression :
      LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
        LinearMap.range (D.projection : H →ₗ[ℂ] H)) ≃ₗ[ℂ]
      ↥(LinearMap.range (D.conjugateProjection : H →ₗ[ℂ] H) ⊓
        LinearMap.ker (D.projection : H →ₗ[ℂ] H)) where
  toFun x := ⟨ContinuousLinearMap.adjoint D.unitary (x.1 : H), by
    have hcancel : ∀ y : H,
        D.unitary (ContinuousLinearMap.adjoint D.unitary y) = y := by
      intro y
      have h := congrArg (fun T : H →L[ℂ] H => T y) D.unitary_mul_adjoint
      simpa [mul_apply_eq_comp] using h
    have hxP : D.projection (x.1 : H) = x.1 :=
      (mem_range_restrictedProjection_iff_apply_eq
        D.projection D.projection_idempotent x.1).mp x.1.2
    constructor
    · apply (mem_range_restrictedProjection_iff_apply_eq
        D.conjugateProjection D.conjugateProjection_idempotent _).mpr
      change ContinuousLinearMap.adjoint D.unitary
        (D.projection (D.unitary
          (ContinuousLinearMap.adjoint D.unitary (x.1 : H)))) =
        ContinuousLinearMap.adjoint D.unitary (x.1 : H)
      rw [hcancel, hxP]
    · have hzero := congrArg (fun y : LinearMap.range
        (D.projection : H →ₗ[ℂ] H) => (y : H)) x.2
      exact hzero⟩
  invFun z := ⟨⟨D.unitary (z : H), by
    have hR : D.conjugateProjection (z : H) = z :=
      (mem_range_restrictedProjection_iff_apply_eq
        D.conjugateProjection D.conjugateProjection_idempotent z).mp z.2.1
    change ContinuousLinearMap.adjoint D.unitary
      (D.projection (D.unitary (z : H))) = z at hR
    have hUR := congrArg D.unitary hR
    have hcancel : ∀ y : H,
        D.unitary (ContinuousLinearMap.adjoint D.unitary y) = y := by
      intro y
      have h := congrArg (fun T : H →L[ℂ] H => T y) D.unitary_mul_adjoint
      simpa [mul_apply_eq_comp] using h
    apply (mem_range_restrictedProjection_iff_apply_eq
      D.projection D.projection_idempotent _).mpr
    simpa only [hcancel] using hUR⟩, by
      have hcancel : ∀ y : H,
          ContinuousLinearMap.adjoint D.unitary (D.unitary y) = y := by
        intro y
        have h := congrArg (fun T : H →L[ℂ] H => T y) D.adjoint_mul_unitary
        simpa [mul_apply_eq_comp] using h
      apply Subtype.ext
      change D.projection
        (ContinuousLinearMap.adjoint D.unitary (D.unitary (z : H))) = 0
      rw [hcancel]
      exact z.2.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun T : H →L[ℂ] H => T (x.1 : H)) D.unitary_mul_adjoint
    simpa [mul_apply_eq_comp] using h
  right_inv z := by
    apply Subtype.ext
    have h := congrArg (fun T : H →L[ℂ] H => T (z : H)) D.adjoint_mul_unitary
    simpa [mul_apply_eq_comp] using h

omit [TopologicalSpace.SeparableSpace H] in
theorem RestrictedUnitaryDatum.finrank_ker_adjointCompression_eq_positiveEndpoint
    (D : RestrictedUnitaryDatum H) :
    Module.finrank ℂ (LinearMap.ker (D.adjointCompression :
      LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
        LinearMap.range (D.projection : H →ₗ[ℂ] H))) =
      Module.finrank ℂ
        ↥(LinearMap.range (D.conjugateProjection : H →ₗ[ℂ] H) ⊓
          LinearMap.ker (D.projection : H →ₗ[ℂ] H)) :=
  D.adjointCompressionKernelEquivPositiveEndpoint.finrank_eq

theorem RestrictedUnitaryDatum.finrank_coker_compression_eq_positiveEndpoint
    (D : RestrictedUnitaryDatum H) :
    letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
      D.isClosed_range_projection.completeSpace_coe
    Module.finrank ℂ
        (LinearMap.range (D.projection : H →ₗ[ℂ] H) ⧸
          LinearMap.range (D.compression :
            LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
              LinearMap.range (D.projection : H →ₗ[ℂ] H))) =
      Module.finrank ℂ
        ↥(LinearMap.range (D.conjugateProjection : H →ₗ[ℂ] H) ⊓
          LinearMap.ker (D.projection : H →ₗ[ℂ] H)) := by
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  let S := LinearMap.range (D.compression :
    LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
      LinearMap.range (D.projection : H →ₗ[ℂ] H))
  have hclosedS : IsClosed (S : Set
      (LinearMap.range (D.projection : H →ₗ[ℂ] H))) :=
    D.isClosed_range_compression
  letI : S.HasOrthogonalProjection :=
    GaloisForLFunctions.HTGeometry.hasOrthogonalProjection_of_isClosed hclosedS
  calc
    Module.finrank ℂ
        (LinearMap.range (D.projection : H →ₗ[ℂ] H) ⧸ S) =
        Module.finrank ℂ Sᗮ :=
      (Submodule.quotientEquivOrthogonal S).toLinearEquiv.finrank_eq
    _ = Module.finrank ℂ
        (LinearMap.ker ((ContinuousLinearMap.adjoint D.compression :
          LinearMap.range (D.projection : H →ₗ[ℂ] H) →L[ℂ]
            LinearMap.range (D.projection : H →ₗ[ℂ] H)) :
          LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
            LinearMap.range (D.projection : H →ₗ[ℂ] H))) := by
      rw [ContinuousLinearMap.orthogonal_range]
    _ = Module.finrank ℂ (LinearMap.ker (D.adjointCompression :
          LinearMap.range (D.projection : H →ₗ[ℂ] H) →ₗ[ℂ]
            LinearMap.range (D.projection : H →ₗ[ℂ] H))) := by
      rw [D.adjoint_compression]
    _ = _ := D.finrank_ker_adjointCompression_eq_positiveEndpoint

theorem RestrictedUnitaryDatum.index_compressionPMap_eq_neg_relativeIndex
    (D : RestrictedUnitaryDatum H) :
    letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
      D.isClosed_range_projection.completeSpace_coe
    LinearPMap.index D.compressionPMap =
      -restrictedProjectionRelativeIndex D.conjugateProjection D.projection := by
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  rw [LinearPMap.index_eq, RestrictedUnitaryDatum.compressionPMap,
    kernel_toPMap_top, rangeSubmodule_toPMap_top,
    D.finrank_ker_compression_eq_negativeEndpoint,
    D.finrank_coker_compression_eq_positiveEndpoint,
    D.relativeIndex_eq_intersection_finrank_sub]
  ring

theorem RestrictedUnitaryDatum.opTrace_cubicDefect_eq_neg_compressionIndex
    (D : RestrictedUnitaryDatum H) :
    letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
      D.isClosed_range_projection.completeSpace_coe
    opTrace (restrictedProjectionCubicDefect
        D.conjugateProjection D.projection) =
      ((-LinearPMap.index D.compressionPMap : ℤ) : ℂ) := by
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  rw [D.opTrace_cubicDefect_eq_relativeIndex,
    D.index_compressionPMap_eq_neg_relativeIndex]
  simp

/-- Closed universal certificate for Fredholmness and exact cubic-index orientation of every
restricted unitary compression on a separable complex Hilbert space. -/
theorem restrictedUnitaryFredholmCompression_closed :
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (D : RestrictedUnitaryDatum H),
      letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
        D.isClosed_range_projection.completeSpace_coe
      D.compressionPMap.IsFredholm ∧
      LinearPMap.index D.compressionPMap =
        -restrictedProjectionRelativeIndex D.conjugateProjection D.projection ∧
      opTrace (restrictedProjectionCubicDefect
          D.conjugateProjection D.projection) =
        ((-LinearPMap.index D.compressionPMap : ℤ) : ℂ) := by
  intro H _ _ _ _ D
  letI : CompleteSpace (LinearMap.range (D.projection : H →ₗ[ℂ] H)) :=
    D.isClosed_range_projection.completeSpace_coe
  exact ⟨D.compressionPMap_isFredholm,
    D.index_compressionPMap_eq_neg_relativeIndex,
    D.opTrace_cubicDefect_eq_neg_compressionIndex⟩

end RHTower
