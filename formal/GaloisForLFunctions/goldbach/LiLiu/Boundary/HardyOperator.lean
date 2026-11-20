import GaloisForLFunctions.goldbach.LiLiu.Boundary.HardyTrace

/-! # Restriction of the arithmetic operator to the Hardy trace space

Every column belongs to the trace space. Hermitian symmetry therefore
kills its orthogonal complement, so a boundary test and its Hardy
projection have the same arithmetic quadratic form.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory HTGeometry
open scoped ComplexConjugate InnerProductSpace
noncomputable section

def hardyOperator {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) : hardySpace a (1/8) →L[ℂ] hardySpace a (1/8) :=
  (hardySpace a (1/8)).orthogonalProjectionOnto ∘L
    ((arithmeticSqKernel hN h ha hab).op ∘L (hardySpace a (1/8)).subtypeL)

theorem hardyOperator_hilbertSchmidt {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) : (hardyOperator hN h ha hab).IsHilbertSchmidt :=
  (((arithmeticSqKernel hN h ha hab).isHilbertSchmidt_op.comp_right _).comp_left _)

instance {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1)) {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) :
    Fact (IsCompactOperator (hardyOperator hN h ha hab)) :=
  ⟨(hardyOperator_hilbertSchmidt hN h ha hab).isCompactOperator⟩

theorem hardyOperator_symmetric {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) : (hardyOperator hN h ha hab).IsSymmetric := by
  let H := hardySpace a (1/8)
  let K := arithmeticSqKernel hN h ha hab
  have hK := arithmeticSqKernel_symmetric hN h ha hab
  intro x y
  change ⟪H.orthogonalProjectionOnto (K.op x),y⟫_ℂ = ⟪x,H.orthogonalProjectionOnto (K.op y)⟫_ℂ
  rw [← H.adjoint_subtypeL,H.subtypeL.adjoint_inner_left,H.subtypeL.adjoint_inner_right]
  exact hK _ _

theorem arithmeticSqKernel_zero_orthogonal {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) {f : Lp ℂ 2 (boundaryMeasure a (1/8))}
    (hf : f ∈ (hardySpace a (1/8))ᗮ) : (arithmeticSqKernel hN h ha hab).op f = 0 := by
  let K := arithmeticSqKernel hN h ha hab
  apply Lp.ext
  filter_upwards [K.op_coeFn f,Lp.coeFn_zero ℂ 2 (boundaryMeasure a (1/8))] with s hs h0
  rw [hs,h0,Pi.zero_apply]
  obtain ⟨u,hu,he⟩ := arithmetic_column_trace hN h ha hab s
  have H := ((hardySpace a (1/8)).mem_orthogonal f).mp hf u hu
  calc
    K.apply f s = ⟪u,f⟫_ℂ := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [he] with z hz
      rw [hz,RCLike.inner_apply]
      have hs' := ha.trans_le (clippedPoint_re hab s).1
      have hz' := ha.trans_le (clippedPoint_re hab z).1
      change extendedKernel (n+1) a s z * f z = f z * conj (extendedKernel (n+1) a z s)
      rw [extendedKernel,extendedKernel,boundaryKernel_hermitian _ hs' hz',mul_comm]
    _ = 0 := H

/-- The projection in the definition of the Hardy operator acts identically
on the range. This identifies it with the integral restriction in (2.17). -/
theorem arithmeticSqKernel_mem_hardy {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) (f : Lp ℂ 2 (boundaryMeasure a (1/8))) :
    (arithmeticSqKernel hN h ha hab).op f ∈ hardySpace a (1/8) := by
  let H := hardySpace a (1/8)
  rw [← H.orthogonal_orthogonal,H.orthogonal.mem_orthogonal]
  intro v hv
  rw [← arithmeticSqKernel_symmetric hN h ha hab v f,arithmeticSqKernel_zero_orthogonal hN h ha hab hv,
    inner_zero_left]

theorem hardyOperator_form {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1)) {a : ℝ}
    (ha : 0 < a) (hab : a ≤ 1/8) (f : Lp ℂ 2 (boundaryMeasure a (1/8))) :
    ⟪f,(arithmeticSqKernel hN h ha hab).op f⟫_ℂ =
      ⟪(hardySpace a (1/8)).orthogonalProjectionOnto f,
        hardyOperator hN h ha hab ((hardySpace a (1/8)).orthogonalProjectionOnto f)⟫_ℂ := by
  let H := hardySpace a (1/8)
  let K := arithmeticSqKernel hN h ha hab
  let p := H.orthogonalProjectionOnto f
  have hd : f-(p : Lp ℂ 2 _) ∈ Hᗮ := Submodule.sub_starProjection_mem_orthogonal f
  have hzero := arithmeticSqKernel_zero_orthogonal hN h ha hab hd
  have hp : K.op f = K.op (p : Lp ℂ 2 _) := sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  have he := (H.mem_orthogonal' _).mp hd (K.op f) (arithmeticSqKernel_mem_hardy hN h ha hab f)
  rw [inner_sub_left,sub_eq_zero] at he
  change ⟪f,K.op f⟫_ℂ = ⟪p,H.orthogonalProjectionOnto (K.op (p : Lp ℂ 2 _))⟫_ℂ
  rw [he,hp,← H.adjoint_subtypeL,H.subtypeL.adjoint_inner_right]
  rfl

theorem hardyOperator_form_bound {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1)) {a : ℝ}
    (ha : 0 < a) (hab : a ≤ 1/8) (f : Lp ℂ 2 (boundaryMeasure a (1/8))) :
    ‖⟪f,(arithmeticSqKernel hN h ha hab).op f⟫_ℂ‖ ≤ ‖hardyOperator hN h ha hab‖ * ‖f‖^2 := by
  rw [hardyOperator_form]
  let p := (hardySpace a (1/8)).orthogonalProjectionOnto f
  let T := hardyOperator hN h ha hab
  calc
    ‖⟪p,T p⟫_ℂ‖ ≤ ‖p‖*‖T p‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖*(‖T‖*‖f‖) := by
      have hp := (hardySpace a (1/8)).norm_orthogonalProjectionOnto_apply_le f
      exact mul_le_mul hp ((T.le_opNorm p).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _)))
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

#print axioms arithmeticSqKernel_mem_hardy
#print axioms hardyOperator_form_bound
end
end GaloisForLFunctions.Goldbach.LiLiu
