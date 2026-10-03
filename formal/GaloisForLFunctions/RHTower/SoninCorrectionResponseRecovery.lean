import GaloisForLFunctions.RHTower.SoninTimeBandSchatten
import GaloisForLFunctions.RHTower.SoninSemilocalRelativeTrace
import GaloisForLFunctions.HTGeometry.SchattenOneBanach

/-!
# Exact nuclear recovery of complete complex Sonin sources

The full response pair `(C(D), C(D*))` and the original time-band pair
`(D(AB+BA), D*(AB+BA))` have bounded real-linear reconstruction maps in
both directions. Thus summability and cofinal trace-norm admission are
equivalent. The compact inverse is constructed unconditionally at every
positive aperture; no source convergence is assumed or concluded here.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
local notation "Op" => (SoninL2 →L[ℂ] SoninL2)
local notation "S1" => SchattenOneOperator SoninL2

private theorem correction_mul_projection_zero (a : ℝ) :
    centralSoninProjectionCorrection a * centralSoninProjection a = 0 := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let Q : Op := centralSoninProjection a
  have hQQ : Q * Q = Q := (centralSoninCarrier a).isIdempotentElem_starProjection
  have hAQ : A.starProjection * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    exact A.starProjection_apply_eq_zero_iff.mpr
      (((A.orthogonal ⊓ B.orthogonal).starProjection_apply_mem f).1)
  have hBQ : B.starProjection * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    exact B.starProjection_apply_eq_zero_iff.mpr
      (((A.orthogonal ⊓ B.orthogonal).starProjection_apply_mem f).2)
  have hJ : centralSoninProjectionCorrection a = Q - (1 - A.starProjection - B.starProjection) := by
    simp only [centralSoninProjectionCorrection, Q, A, B,
      centralPhysicalForbidden, centralFourierForbidden, centralInterval,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection]
  rw [hJ]
  change (Q - (1 - A.starProjection - B.starProjection)) * Q = 0
  noncomm_ring [hQQ, hAQ, hBQ]

private theorem one_add_correction_apply_eq_zero (a : ℝ) (x : SoninL2)
    (hx : (1 + centralSoninProjectionCorrection a) x = 0) : x = 0 := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let K := centralSoninCarrier a
  have hform : 1 + centralSoninProjectionCorrection a =
      K.starProjection + A.starProjection + B.starProjection := by
    simp only [centralSoninProjectionCorrection, K, A, B,
      centralSoninProjection, centralPhysicalForbidden, centralFourierForbidden, centralInterval,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection]
    abel
  have hquad (P : Submodule ℂ SoninL2) [P.HasOrthogonalProjection] :
      (inner ℂ (P.starProjection x) x).re = ‖P.starProjection x‖ ^ (2 : ℕ) := by
    convert! P.re_inner_starProjection_eq_normSq x using 1
  have hsum := congrArg (fun y : SoninL2 => (inner ℂ y x).re) hx
  rw [hform] at hsum
  simp only [add_apply, inner_add_left, Complex.add_re, inner_zero_left,
    Complex.zero_re, hquad] at hsum
  have hK : K.starProjection x = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖A.starProjection x‖, sq_nonneg ‖B.starProjection x‖,
      norm_nonneg (K.starProjection x)]
  have hA : A.starProjection x = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖K.starProjection x‖, sq_nonneg ‖B.starProjection x‖,
      norm_nonneg (A.starProjection x)]
  have hB : B.starProjection x = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖K.starProjection x‖, sq_nonneg ‖A.starProjection x‖,
      norm_nonneg (B.starProjection x)]
  have hxK : x ∈ K :=
    ⟨A.starProjection_apply_eq_zero_iff.mp hA, B.starProjection_apply_eq_zero_iff.mp hB⟩
  exact (Submodule.starProjection_eq_self_iff.mpr hxK).symm.trans hK

/-- The actual sum of the physical, Fourier and Sonin projections is boundedly
invertible. Its inverse is obtained from the compact correction, without a gap premise. -/
theorem isUnit_one_add_centralSoninProjectionCorrection (a : ℝ) (ha : 0 < a) :
    IsUnit (1 + centralSoninProjectionCorrection a) := by
  have hcpt := (centralSoninProjectionCorrection_memSchattenClass_one a ha).isCompactOperator one_pos
  have hno : ¬ Module.End.HasEigenvalue (centralSoninProjectionCorrection a : SoninL2 →ₗ[ℂ] SoninL2)
      (-1 : ℂ) := by
    intro h
    obtain ⟨x, hx, hxne⟩ := h.exists_hasEigenvector
    have hjx : centralSoninProjectionCorrection a x = -x := by
      simp only [Module.End.mem_genEigenspace_one, neg_one_smul] at hx
      exact hx
    apply hxne
    apply one_add_correction_apply_eq_zero a x
    simp only [add_apply, one_apply_eq_self, hjx, add_neg_cancel]
  have hs : (-1 : ℂ) ∉ spectrum ℂ (centralSoninProjectionCorrection a) := by
    exact fun h => hno ((hcpt.hasEigenvalue_iff_mem_spectrum (by norm_num)).mpr h)
  have hu := (spectrum.notMem_iff.mp hs).neg
  simpa only [Algebra.algebraMap_eq_smul_one, neg_one_smul, neg_sub, neg_neg, sub_neg_eq_add,
    add_comm] using hu

/-- Canonical bounded inverse used to recover the unsquared source. -/
def soninCorrectionSourceInverse (a : ℝ) : Op :=
  Ring.inverse (1 + centralSoninProjectionCorrection a)

private theorem source_inverse_mul (a : ℝ) (ha : 0 < a) :
    soninCorrectionSourceInverse a * (1 + centralSoninProjectionCorrection a) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_one_add_centralSoninProjectionCorrection a ha)

private theorem response_active_block (a : ℝ) (D : Op) :
    centralSoninCornerCorrectionResponse a D * (1 - centralSoninProjection a) =
      (1 + centralSoninProjectionCorrection a) *
        ((1 - centralSoninProjection a) * (D * centralSoninProjectionCorrection a)) := by
  let Q := centralSoninProjection a
  let J := centralSoninProjectionCorrection a
  have hJQ : J * Q = 0 := correction_mul_projection_zero a
  have hQQ : Q * Q = Q := (centralSoninCarrier a).isIdempotentElem_starProjection
  have hQ0 : centralSoninFormalComplement a = Q - J := by
    dsimp [Q, J, centralSoninProjectionCorrection, centralSoninFormalComplement]
    abel
  rw [centralSoninCornerCorrectionResponse_eq_correction_factorization, hQ0]
  change ((1 - Q) * D * J - J * D * (Q - J)) * (1 - Q) =
    (1 + J) * ((1 - Q) * (D * J))
  noncomm_ring [hJQ, hQQ]
  rw [← mul_assoc J Q, hJQ, zero_mul, smul_zero, add_zero]

/-- Exact recovery of the full left source from both blocks of the complete
response. No projection or mixed response term is discarded. -/
theorem soninCorrectionSource_recovery (a : ℝ) (ha : 0 < a)
    (D : Op) :
    D * centralSoninProjectionCorrection a =
      soninCorrectionSourceInverse a *
        (centralSoninCornerCorrectionResponse a D * (1 - centralSoninProjection a)) -
      adjoint (centralSoninCornerCorrectionResponse a (adjoint D) * centralSoninProjection a) := by
  have hQ : adjoint (centralSoninProjection a) = centralSoninProjection a :=
    (isSelfAdjoint_starProjection (centralSoninCarrier a)).star_eq
  rw [response_active_block, ← mul_assoc, source_inverse_mul a ha, one_mul,
    centralSoninCornerCorrectionResponse_mul_projection, map_neg,
    adjoint_mul_soninL2, adjoint_mul_soninL2,
    adjoint_centralSoninProjectionCorrection, adjoint_adjoint, hQ]
  noncomm_ring

private def traceSandwich (L R : Op) : S1 →L[ℂ] S1 :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨L ∘L T.val ∘L R,
        memSchattenClass_one_comp_right (memSchattenClass_one_comp_left T.property L) R⟩
      map_add' := by
        intro S T
        apply SchattenOneOperator.ext
        apply ContinuousLinearMap.ext
        intro x
        change L (S.val (R x) + T.val (R x)) = _
        exact map_add L _ _
      map_smul' := by
        intro c T
        apply SchattenOneOperator.ext
        apply ContinuousLinearMap.ext
        intro x
        change L (c • T.val (R x)) = _
        exact map_smul L c _ }
    (‖L‖ * ‖R‖) (fun T => by
      change traceNorm SoninL2 ((L ∘L T.val) ∘L R) ≤ _
      calc
        _ ≤ traceNorm SoninL2 (L ∘L T.val) * ‖R‖ :=
          traceNorm_comp_right_le (memSchattenClass_one_comp_left T.property L).one_summable R
        _ ≤ (‖L‖ * traceNorm SoninL2 T.val) * ‖R‖ :=
          mul_le_mul_of_nonneg_right (traceNorm_comp_left_le T.summable L) (norm_nonneg _)
        _ = _ := by rw [SchattenOneOperator.norm_def]; ring)

private def traceAdjointReal : S1 →L[ℝ] S1 :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨adjoint T.val,
        (memRectSchattenClass_iff_memSchattenClass 1 _).mp
          ((memRectSchattenClass_adjoint_iff 1 T.val).mpr
            ((memRectSchattenClass_iff_memSchattenClass 1 T.val).mpr T.property))⟩
      map_add' := by
        intro S T
        apply SchattenOneOperator.ext
        exact (adjoint : Op ≃ₗᵢ⋆[ℂ] Op).map_add S.val T.val
      map_smul' := by
        intro c T
        apply SchattenOneOperator.ext
        change adjoint ((c : ℂ) • T.val) = (c : ℂ) • adjoint T.val
        simpa only [Complex.conj_ofReal] using
          (adjoint : Op ≃ₗᵢ⋆[ℂ] Op).map_smulₛₗ (c : ℂ) T.val }
    1 (fun T => by
      change traceNorm SoninL2 (adjoint T.val) ≤ 1 * traceNorm SoninL2 T.val
      rw [← rectTraceNorm_eq_traceNorm, ← rectTraceNorm_eq_traceNorm,
        rectTraceNorm_adjoint, one_mul])

/-- A single canonical right inverse removes the full projection resolvent
from the unsquared source while preserving the actual two time-band legs. -/
theorem centralSoninProjectionCorrection_eq_timeBand_mul_inverse (a : ℝ) (ha : 0 < a) :
    centralSoninProjectionCorrection a =
      ((centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection +
        (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection) *
          soninCorrectionSourceInverse a := by
  have hU : (1 + centralSoninProjectionCorrection a) * soninCorrectionSourceInverse a = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_one_add_centralSoninProjectionCorrection a ha)
  calc
    _ = centralSoninProjectionCorrection a *
        ((1 + centralSoninProjectionCorrection a) * soninCorrectionSourceInverse a) := by rw [hU, mul_one]
    _ = (centralSoninProjectionCorrection a * centralSoninProjectionCorrection a +
        centralSoninProjectionCorrection a) * soninCorrectionSourceInverse a := by noncomm_ring
    _ = _ := by rw [centralSoninProjectionCorrection_sq_add_self_eq_anticommutator]


/-- Complete pair of original responses, retaining the adjoint source needed
for complex arithmetic continuation. -/
def soninNuclearResponsePair (a : ℝ) (ha : 0 < a) (D : Op) : S1 × S1 :=
  (⟨centralSoninCornerCorrectionResponse a D,
    (centralSoninCornerCorrectionResponse_mem_timeBandIdeal a ha D).memSchattenClass_one⟩,
   ⟨centralSoninCornerCorrectionResponse a (adjoint D),
    (centralSoninCornerCorrectionResponse_mem_timeBandIdeal a ha (adjoint D)).memSchattenClass_one⟩)

/-- The corresponding unsquared left-source pair, with proved nuclear membership. -/
def soninNuclearLeftSourcePair (a : ℝ) (ha : 0 < a) (D : Op) : S1 × S1 :=
  (⟨D * centralSoninProjectionCorrection a,
    memSchattenClass_one_comp_left (centralSoninProjectionCorrection_memSchattenClass_one a ha) D⟩,
   ⟨adjoint D * centralSoninProjectionCorrection a,
    memSchattenClass_one_comp_left (centralSoninProjectionCorrection_memSchattenClass_one a ha) (adjoint D)⟩)

/-- The bounded real-linear inverse on both original response blocks. -/
def soninPairedResponseRecovery (a : ℝ) : S1 × S1 →L[ℝ] S1 × S1 :=
  let A := (traceSandwich (soninCorrectionSourceInverse a) (1 - centralSoninProjection a)).restrictScalars ℝ
  let B := traceAdjointReal.comp ((traceSandwich 1 (centralSoninProjection a)).restrictScalars ℝ)
  (A.comp (ContinuousLinearMap.fst ℝ S1 S1) - B.comp (ContinuousLinearMap.snd ℝ S1 S1)).prod
    (A.comp (ContinuousLinearMap.snd ℝ S1 S1) - B.comp (ContinuousLinearMap.fst ℝ S1 S1))

/-- Forward map on the unsquared pair; both correction legs are kept. -/
def soninPairedResponseForward (a : ℝ) : S1 × S1 →L[ℝ] S1 × S1 :=
  let A := (traceSandwich (1 - centralSoninProjection a) 1).restrictScalars ℝ
  let B := ((traceSandwich 1 (centralSoninFormalComplement a)).restrictScalars ℝ).comp traceAdjointReal
  (A.comp (ContinuousLinearMap.fst ℝ S1 S1) - B.comp (ContinuousLinearMap.snd ℝ S1 S1)).prod
    (A.comp (ContinuousLinearMap.snd ℝ S1 S1) - B.comp (ContinuousLinearMap.fst ℝ S1 S1))

/-- Exact recovery for every complex source, with no self-adjointness premise. -/
theorem soninPairedResponseRecovery_apply (a : ℝ) (ha : 0 < a) (D : Op) :
    soninPairedResponseRecovery a (soninNuclearResponsePair a ha D) =
      soninNuclearLeftSourcePair a ha D := by
  apply Prod.ext
  · apply SchattenOneOperator.ext
    change soninCorrectionSourceInverse a * centralSoninCornerCorrectionResponse a D *
        (1 - centralSoninProjection a) -
        adjoint (1 * centralSoninCornerCorrectionResponse a (adjoint D) * centralSoninProjection a) = _
    rw [one_mul, mul_assoc]
    exact (soninCorrectionSource_recovery a ha D).symm
  · apply SchattenOneOperator.ext
    change soninCorrectionSourceInverse a * centralSoninCornerCorrectionResponse a (adjoint D) *
        (1 - centralSoninProjection a) -
        adjoint (1 * centralSoninCornerCorrectionResponse a D * centralSoninProjection a) =
          adjoint D * centralSoninProjectionCorrection a
    rw [one_mul, mul_assoc]
    simpa only [adjoint_adjoint] using (soninCorrectionSource_recovery a ha (adjoint D)).symm

private theorem forward_algebra (a : ℝ) (D : Op) :
    (1 - centralSoninProjection a) * (D * centralSoninProjectionCorrection a) * 1 -
      1 * adjoint (adjoint D * centralSoninProjectionCorrection a) * centralSoninFormalComplement a =
      centralSoninCornerCorrectionResponse a D := by
  rw [mul_one, one_mul, adjoint_mul_soninL2, adjoint_centralSoninProjectionCorrection,
    adjoint_adjoint, centralSoninCornerCorrectionResponse_eq_correction_factorization]
  noncomm_ring

/-- The recovered pair reconstructs the complete original response pair. -/
theorem soninPairedResponseForward_apply (a : ℝ) (ha : 0 < a) (D : Op) :
    soninPairedResponseForward a (soninNuclearLeftSourcePair a ha D) =
      soninNuclearResponsePair a ha D := by
  apply Prod.ext
  · apply SchattenOneOperator.ext
    exact forward_algebra a D
  · apply SchattenOneOperator.ext
    change (1 - centralSoninProjection a) * (adjoint D * centralSoninProjectionCorrection a) * 1 -
      1 * adjoint (D * centralSoninProjectionCorrection a) * centralSoninFormalComplement a =
        centralSoninCornerCorrectionResponse a (adjoint D)
    simpa only [adjoint_adjoint] using forward_algebra a (adjoint D)

/-- Nuclear summation of the full complex response pair is exactly nuclear
summation of the unsquared left-source pair. -/
theorem summable_soninNuclearResponsePair_iff {ι : Type*}
    (a : ℝ) (ha : 0 < a) (D : ι → Op) :
    Summable (fun i => soninNuclearResponsePair a ha (D i)) ↔
      Summable (fun i => soninNuclearLeftSourcePair a ha (D i)) := by
  constructor
  · intro h
    simpa only [soninPairedResponseRecovery_apply] using (soninPairedResponseRecovery a).summable h
  · intro h
    simpa only [soninPairedResponseForward_apply] using (soninPairedResponseForward a).summable h

/-- Exact equivalence of cofinal trace-norm admission, including signed
prime–polar families and complex-parameter source families. -/
theorem tendsto_soninNuclearResponsePair_iff {ι : Type*}
    (a : ℝ) (ha : 0 < a) (D : ι → Op) (l : Filter ι) :
    (∃ T : S1 × S1, Filter.Tendsto (fun i => soninNuclearResponsePair a ha (D i)) l (nhds T)) ↔
      (∃ T : S1 × S1, Filter.Tendsto (fun i => soninNuclearLeftSourcePair a ha (D i)) l (nhds T)) := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨soninPairedResponseRecovery a T, ?_⟩
    exact ((soninPairedResponseRecovery a).continuous.continuousAt.tendsto.comp hT).congr
      fun i => soninPairedResponseRecovery_apply a ha (D i)
  · rintro ⟨T, hT⟩
    refine ⟨soninPairedResponseForward a T, ?_⟩
    exact ((soninPairedResponseForward a).continuous.continuousAt.tendsto.comp hT).congr
      fun i => soninPairedResponseForward_apply a ha (D i)

/-- Literal time-band pair obtained from the original complex source and its
adjoint. The coe theorem identifies both components as D(AB+BA). -/
def soninNuclearTimeBandSourcePair (a : ℝ) (ha : 0 < a) (D : Op) : S1 × S1 :=
  let R := traceSandwich 1 (1 + centralSoninProjectionCorrection a)
  R.prodMap R (soninNuclearLeftSourcePair a ha D)

/-- Both time-band legs and both source directions remain literal operators. -/
theorem soninNuclearTimeBandSourcePair_coe (a : ℝ) (ha : 0 < a) (D : Op) :
    let L := (centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection +
      (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection
    ((soninNuclearTimeBandSourcePair a ha D).1.val,
      (soninNuclearTimeBandSourcePair a ha D).2.val) = (D * L, adjoint D * L) := by
  dsimp only
  have h (E : Op) : 1 * (E * centralSoninProjectionCorrection a) *
      (1 + centralSoninProjectionCorrection a) =
        E * ((centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection +
          (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection) := by
    rw [one_mul, mul_assoc, mul_add, mul_one, add_comm,
      centralSoninProjectionCorrection_sq_add_self_eq_anticommutator]
  exact Prod.ext (h D) (h (adjoint D))

private theorem recover_left_from_timeBand (a : ℝ) (ha : 0 < a) (D : Op) :
    let R := traceSandwich 1 (soninCorrectionSourceInverse a)
    R.prodMap R (soninNuclearTimeBandSourcePair a ha D) = soninNuclearLeftSourcePair a ha D := by
  have hU : (1 + centralSoninProjectionCorrection a) * soninCorrectionSourceInverse a = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_one_add_centralSoninProjectionCorrection a ha)
  have h (E : Op) : 1 * (1 * (E * centralSoninProjectionCorrection a) *
      (1 + centralSoninProjectionCorrection a)) * soninCorrectionSourceInverse a =
      E * centralSoninProjectionCorrection a := by
    simp only [one_mul, mul_assoc, hU, mul_one]
  apply Prod.ext <;> apply SchattenOneOperator.ext
  · exact h D
  · exact h (adjoint D)

/-- The complete complex response pair is summable exactly when the literal
signed time-band source pair is summable in genuine Schatten-one. -/
theorem summable_soninNuclearResponsePair_iff_timeBand {ι : Type*}
    (a : ℝ) (ha : 0 < a) (D : ι → Op) :
    Summable (fun i => soninNuclearResponsePair a ha (D i)) ↔
      Summable (fun i => soninNuclearTimeBandSourcePair a ha (D i)) := by
  rw [summable_soninNuclearResponsePair_iff]
  constructor
  · intro h
    let R := traceSandwich 1 (1 + centralSoninProjectionCorrection a)
    exact (R.prodMap R).summable h
  · intro h
    let R := traceSandwich 1 (soninCorrectionSourceInverse a)
    exact ((R.prodMap R).summable h).congr fun i => recover_left_from_timeBand a ha (D i)

/-- Cofinal source admission has no hidden gain from the full response:
it is exactly admission of (D(AB+BA), D*(AB+BA)). -/
theorem tendsto_soninNuclearResponsePair_iff_timeBand {ι : Type*}
    (a : ℝ) (ha : 0 < a) (D : ι → Op) (l : Filter ι) :
    (∃ T : S1 × S1, Filter.Tendsto (fun i => soninNuclearResponsePair a ha (D i)) l (nhds T)) ↔
      (∃ T : S1 × S1, Filter.Tendsto (fun i => soninNuclearTimeBandSourcePair a ha (D i)) l (nhds T)) := by
  rw [tendsto_soninNuclearResponsePair_iff]
  constructor
  · rintro ⟨T, hT⟩
    let R := traceSandwich 1 (1 + centralSoninProjectionCorrection a)
    exact ⟨R.prodMap R T, (R.prodMap R).continuous.continuousAt.tendsto.comp hT⟩
  · rintro ⟨T, hT⟩
    let R := traceSandwich 1 (soninCorrectionSourceInverse a)
    refine ⟨R.prodMap R T, ?_⟩
    exact ((R.prodMap R).continuous.continuousAt.tendsto.comp hT).congr
      fun i => recover_left_from_timeBand a ha (D i)

end RHTower
