import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoprimeHeight

/-! The actual primitive-cone response computes the constant-mode Mayer
cofactor. The rank-one determinant update uses the supplied response and
therefore introduces no inverse-operator premise. -/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerNuclear MayerFredholm MayerParameter MayerCancellation
open MayerCoprimeSource MayerCoprimeHeight
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeCofactor

private def shiftMatrix (w t : ℂ) (i j : ℕ) : ℂ :=
  -sourceMatrix w i j+t*MayerPole.projectionMatrix i j

private theorem shift_geometric {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    GeomFredholm.GeomDecay (shiftMatrix w t) (constantBound w+‖t‖) rate := by
  have hS : GeomFredholm.GeomDecay (sourceMatrix w) (constantBound w) rate := by
    rw [sourceMatrix_eq hw]
    exact geomDecay_matrix hw
  refine ⟨add_nonneg hS.const_nonneg (norm_nonneg _),rate_bounds.1,rate_bounds.2,?_⟩
  intro i j
  have hP : ‖MayerPole.projectionMatrix i j‖ ≤ rate^i*rate^j := by
    simpa only [one_mul] using MayerPole.geomDecay_projection.bound i j
  calc
    ‖shiftMatrix w t i j‖ ≤ ‖sourceMatrix w i j‖+‖t‖*‖MayerPole.projectionMatrix i j‖ := by
      simpa only [shiftMatrix,norm_neg,norm_mul] using
        norm_add_le (-sourceMatrix w i j) (t*MayerPole.projectionMatrix i j)
    _ ≤ constantBound w*rate^i*rate^j+‖t‖*(rate^i*rate^j) :=
      add_le_add (hS.bound i j) (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
    _ = _ := by ring

private theorem shift_matrix {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    HilbertSchmidt.matrixOf (-hilbertOperator w hw+t • hilbertProjection)=
      fun p => shiftMatrix w t p.1 p.2 := by
  funext p
  change -HilbertSchmidt.matrixOf (hilbertOperator w hw) p+
    t*HilbertSchmidt.matrixOf hilbertProjection p=_
  rw [matrixOf_hilbertOperator,matrixOf_hilbertProjection,← sourceMatrix_eq hw]
  rfl

private theorem shift_diagonal {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    (∑' i,shiftMatrix w t i i)=-(∑' i,sourceMatrix w i i)+t := by
  have hS : Summable (fun i => sourceMatrix w i i) := by
    rw [sourceMatrix_eq hw]
    exact (diagonal_norm_summable hw).of_norm
  have hP := geometric_diagonal_summable MayerPole.geomDecay_projection
  have hp : (∑' i,MayerPole.projectionMatrix i i)=1 := by
    rw [tsum_eq_single 0]
    · simp only [MayerPole.projectionMatrix_eq,ite_true,pow_zero,inv_one,one_mul]
    · intro i hi
      rw [MayerPole.projectionMatrix_eq,if_neg hi]
  change (∑' i,(-sourceMatrix w i i+t*MayerPole.projectionMatrix i i))=_
  rw [hS.neg.tsum_add (hP.mul_left t),tsum_neg,tsum_mul_left,hp,mul_one]

/-- Exact finite sections identify the positive spectral parameter with the negative matrix. -/
private theorem perturbed_eq_shift {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    MayerPole.perturbedDeterminant w (riemannZeta w-t) 1=
      GeomFredholm.fdet (shiftMatrix w t) (-1) := by
  have hm : MayerPole.perturbedMatrix w (riemannZeta w-t)=fun i j => -shiftMatrix w t i j := by
    funext i j
    rw [shiftMatrix,MayerPole.sourceMatrix_decomposition]
    unfold MayerPole.perturbedMatrix
    ring
  have hg : GeomFredholm.GeomDecay (MayerPole.perturbedMatrix w (riemannZeta w-t))
      (constantBound w+‖t‖) rate := by
    refine ⟨(shift_geometric hw t).const_nonneg,rate_bounds.1,rate_bounds.2,?_⟩
    intro i j
    rw [hm,norm_neg]
    exact (shift_geometric hw t).bound i j
  have he : GeomFredholm.truncDet (MayerPole.perturbedMatrix w (riemannZeta w-t)) 1=
      GeomFredholm.truncDet (shiftMatrix w t) (-1) := by
    funext N
    unfold GeomFredholm.truncDet
    congr 1
    ext i j
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,GeomFredholm.trunc,Matrix.of_apply]
    rw [hm]
    ring
  apply tendsto_nhds_unique (GeomFredholm.tendsto_truncDet hg 1)
  rw [he]
  exact GeomFredholm.tendsto_truncDet (shift_geometric hw t) (-1)

private theorem perturbed_eq_det2 {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    MayerPole.perturbedDeterminant w (riemannZeta w-t) 1=
      _root_.RHTower.det2Op (HilbertSchmidt.lpBasis ℕ) (-hilbertOperator w hw+t • hilbertProjection)*
        Complex.exp (-(∑' i,sourceMatrix w i i)+t) := by
  rw [perturbed_eq_shift hw t,fdet_negative_one_eq_entireDet2 (shift_geometric hw t),
    _root_.RHTower.det2Op,coordMatrix_canonical,shift_matrix hw,shift_diagonal hw]

/-- A supplied disc response transports to the actual Cauchy Hilbert realization. -/
theorem hilbert_response {w : ℂ} (hw : 0 < w.re) (f : DiscSpace)
    (hf : f-regularized w hw f=constant 1) :
    analysisMap f+(-hilbertOperator w hw) (analysisMap f)=constantVector := by
  have hs := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T f)
    (synthesis_comp_analysis hw)
  change synthesisMap w hw (analysisMap f)=regularized w hw f at hs
  change analysisMap f-analysisMap (synthesisMap w hw (analysisMap f))=_
  rw [hs,← map_sub,hf]
  rfl

/-- The genuine primitive-cone response supplies the Hilbert response. -/
theorem hilbert_green {w : ℂ} (hw : 2 < w.re) :
    analysisMap (green w)+(-hilbertOperator w (by linarith only [hw])) (analysisMap (green w))=
      constantVector :=
  hilbert_response (by linarith only [hw]) (green w) (green_response hw)

private theorem det2_shift_response {w : ℂ} (hw : 0 < w.re) (f : DiscSpace)
    (hf : f-regularized w hw f=constant 1) (t : ℂ) :
    _root_.RHTower.det2Op (HilbertSchmidt.lpBasis ℕ)
      (-hilbertOperator w hw+t • hilbertProjection)=
    _root_.RHTower.det2Op (HilbertSchmidt.lpBasis ℕ) (-hilbertOperator w hw)*
      (1+t*f.1 zeroPoint)*Complex.exp (-t) := by
  have hh : ContinuousLinearMap.IsHilbertSchmidt (hilbertOperator w hw) := by
    rw [← toOperator_kernel]
    exact HilbertSchmidt.isHilbertSchmidt_toOperator _
  let y : SequenceSpace := (InnerProductSpace.toDual ℂ SequenceSpace).symm coefficientEvaluation
  have hy (x : SequenceSpace) : inner ℂ y x=coefficientEvaluation x :=
    InnerProductSpace.toDual_symm_apply
  have hu : t • analysisMap f+
      (-hilbertOperator w hw) (t • analysisMap f)=t • constantVector := by
    rw [map_smul,← smul_add,hilbert_response hw f hf]
  have he : InnerProductSpace.rankOne ℂ (t • constantVector) y=t • hilbertProjection := by
    apply ContinuousLinearMap.ext
    intro x
    rw [InnerProductSpace.rankOne_apply,hy]
    change coefficientEvaluation x • (t • constantVector)=t • (coefficientEvaluation x • constantVector)
    exact smul_comm _ _ _
  have h := det2Op_rankOne_update (HilbertSchmidt.lpBasis ℕ) hh.neg
    (t • analysisMap f) (t • constantVector) y hu
  rw [he,hy,hy,map_smul,map_smul,coefficientEvaluation_analysis,
    coefficientEvaluation_constant,smul_eq_mul,smul_eq_mul,mul_one] at h
  exact h

/-- Ordinary rank-one determinant update for any supplied actual response. -/
theorem determinant_shift_of_response {w : ℂ} (hw : 0 < w.re) (f : DiscSpace)
    (hf : f-regularized w hw f=constant 1) (t : ℂ) :
    MayerPole.perturbedDeterminant w (riemannZeta w-t) 1=
      sourceDeterminant w 1*(1+t*f.1 zeroPoint) := by
  have h0 := perturbed_eq_det2 hw 0
  simp only [sub_zero,zero_smul,add_zero] at h0
  rw [← MayerPole.sourceDeterminant_eq_perturbed] at h0
  rw [perturbed_eq_det2 hw t,det2_shift_response hw f hf t,h0]
  rw [mul_assoc _ (Complex.exp (-t)),← Complex.exp_add]
  have he : -t+(-(∑' i,sourceMatrix w i i)+t)=-(∑' i,sourceMatrix w i i) := by ring
  rw [he]
  ring

/-- Exact ordinary rank-one determinant update with the primitive-cone response. -/
theorem determinant_shift {w : ℂ} (hw : 2 < w.re) (t : ℂ) :
    MayerPole.perturbedDeterminant w (riemannZeta w-t) 1=
      sourceDeterminant w 1*(1+t*(green w).1 zeroPoint) :=
  determinant_shift_of_response (by linarith only [hw]) (green w) (green_response hw) t

/-- A supplied actual response computes the signed constant-projection cofactor. -/
theorem polePart_eq_response_of {w : ℂ} (hw : 0 < w.re) (f : DiscSpace)
    (hf : f-regularized w hw f=constant 1) :
    MayerPole.polePart w 1=-sourceDeterminant w 1*f.1 zeroPoint := by
  have h := determinant_shift_of_response hw f hf 1
  rw [MayerPole.perturbedDeterminant_affine hw,
    MayerPole.sourceDeterminant_decomposition hw] at h
  change MayerPole.regularPart w 1+(riemannZeta w-1)*MayerPole.polePart w 1=
    (MayerPole.regularPart w 1+riemannZeta w*MayerPole.polePart w 1)*(1+1*f.1 zeroPoint) at h
  rw [MayerPole.sourceDeterminant_decomposition hw]
  linear_combination -h

/-- The cofactor is the primitive-cone boundary response times the determinant. -/
theorem polePart_eq_response {w : ℂ} (hw : 2 < w.re) :
    MayerPole.polePart w 1=-sourceDeterminant w 1*(green w).1 zeroPoint :=
  polePart_eq_response_of (by linarith only [hw]) (green w) (green_response hw)

/-- The actual Mayer cofactor satisfies the shifted-zeta identity in the absolute chamber. -/
theorem zeta_cofactor_identity {w : ℂ} (hw : 2 < w.re) :
    2*riemannZeta (w-1)*sourceDeterminant w 1+riemannZeta w*MayerPole.polePart w 1=0 := by
  have hm := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (show 1 < w.re by linarith only [hw])
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by linarith only [hw])] at hm
  have hz : riemannZeta w ≠ 0 := by
    intro he
    rw [he,zero_mul] at hm
    exact zero_ne_one hm
  rw [polePart_eq_response hw,green_zero hw]
  field_simp [hz]
  ring

/-- Removing the constant zeta mode introduces an exact additional scalar factor. -/
theorem regularPart_eq_shifted_zeta_factor {w : ℂ} (hw : 2 < w.re) :
    MayerPole.regularPart w 1=(1+2*riemannZeta (w-1))*sourceDeterminant w 1 := by
  have hd := MayerPole.sourceDeterminant_decomposition (show 0 < w.re by linarith only [hw]) 1
  have hz := zeta_cofactor_identity hw
  linear_combination -hd-hz

#print axioms regularPart_eq_shifted_zeta_factor
#print axioms hilbert_response
#print axioms determinant_shift_of_response
#print axioms polePart_eq_response_of
#print axioms hilbert_green
#print axioms determinant_shift
#print axioms polePart_eq_response
#print axioms zeta_cofactor_identity

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeCofactor
