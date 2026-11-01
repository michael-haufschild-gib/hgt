import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerDerivativeCone
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerRawDeterminantFinitePart
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantScaling

/-!
# Positive real nonvanishing of the Mayer pole coefficient

The actual compressed remainder factors through the rescaled Cauchy
Hilbert space. Its zero constant column identifies the full Fredholm
determinant with the complementary determinant. Exact eigenvector
transport combines this identity with the source derivative cone.

For real `w>0`, the coefficient `B(w,λ)` in `D=A+ζ B` is nonzero
throughout `0<λ<(3/2)^w`. In particular, `D(w,1)` has a genuine
simple pole at `w=1`. All operators and matrices are those of the
actual Gauss branches; complex source parameters are not restricted
by this real positivity argument.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDerivative
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPositive
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPositivePole

open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFinitePart
open GeomFredholm

private theorem geometric_neg_scale {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomDecay M C rate) (lam : ℂ) :
    GeomDecay (fun i j => -lam*M i j) (‖lam‖*C) rate := by
  refine ⟨mul_nonneg (norm_nonneg _) hM.const_nonneg,hM.rate_nonneg,hM.rate_lt_one,fun i j => ?_⟩
  rw [norm_mul,norm_neg]
  exact (mul_le_mul_of_nonneg_left (hM.bound i j) (norm_nonneg lam)).trans_eq (by ring)

private theorem fdet_scale_negative_one {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomDecay M C rate) (lam : ℂ) :
    fdet M lam = fdet (fun i j => -lam*M i j) (-1) := by
  have he : truncDet M lam = truncDet (fun i j => -lam*M i j) (-1) := by
    funext N
    unfold truncDet
    congr 1
    ext i j
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,GeomFredholm.trunc,Matrix.of_apply]
    ring
  apply tendsto_nhds_unique (tendsto_truncDet hM lam)
  rw [he]
  exact tendsto_truncDet (geometric_neg_scale hM lam) (-1)

/-- The geometric determinant detects Hilbert eigenvectors through the exact diagonal correction. -/
theorem fdet_zero_iff_hilbert_eigenvector {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomDecay M C rate) {lam : ℂ} (hlam : lam ≠ 0) :
    fdet M lam = 0 ↔ ∃ x : SequenceSpace, x ≠ 0 ∧
      HilbertSchmidt.toOperator (MayerCancellation.geometric_isHS hM) x = lam⁻¹ • x := by
  have he := congrFun
    (entireDet2_smul (MayerCancellation.geometric_isHS hM) (-lam)) (-1)
  change entireDet2 (fun p : ℕ × ℕ => -lam*M p.1 p.2) (-1) =
    entireDet2 (fun p : ℕ × ℕ => M p.1 p.2) ((-lam)*(-1)) at he
  simp only [neg_mul_neg,mul_one] at he
  rw [fdet_scale_negative_one hM lam,
    MayerCancellation.fdet_negative_one_eq_entireDet2 (geometric_neg_scale hM lam),he,
    mul_eq_zero,or_iff_left (Complex.exp_ne_zero _),
    entireDet2_eq_zero_iff_exists_eigenvector (MayerCancellation.geometric_isHS hM) hlam]

private theorem truncDet_zero_column (M : ℕ → ℕ → ℂ)
    (hzero : ∀ i, M i 0 = 0) (lam : ℂ) (N : ℕ) :
    truncDet M lam (N+1) = truncDet (fun i j => M (i+1) (j+1)) lam N := by
  let A : Matrix (Fin (N+1)) (Fin (N+1)) ℂ := 1-lam • GeomFredholm.trunc M (N+1)
  have hrow (j : Fin (N+1)) : A.transpose 0 j = if j = 0 then 1 else 0 := by
    simp only [A,Matrix.transpose_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      GeomFredholm.trunc,Matrix.of_apply,Fin.val_zero,hzero,mul_zero,sub_zero,Matrix.one_apply]
  have hminor : A.transpose.submatrix Fin.succ Fin.succ =
      (1-lam • GeomFredholm.trunc (fun i j => M (i+1) (j+1)) N).transpose := by
    ext i j
    simp only [A,Matrix.submatrix_apply,Matrix.transpose_apply,Matrix.sub_apply,
      Matrix.smul_apply,smul_eq_mul,GeomFredholm.trunc,Matrix.of_apply,Matrix.one_apply,Fin.succ_inj]
    rfl
  change A.det = (1-lam • GeomFredholm.trunc (fun i j => M (i+1) (j+1)) N).det
  rw [← Matrix.det_transpose A,Matrix.det_succ_row_zero,Finset.sum_eq_single 0]
  · rw [hrow]
    simp only [Fin.val_zero,pow_zero,if_true,one_mul,Fin.succAbove_zero]
    rw [hminor,Matrix.det_transpose]
  · intro j hj hj0
    rw [hrow,if_neg hj0,mul_zero,zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ 0) hj

private theorem geometric_shift {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomDecay M C rate) :
    GeomDecay (fun i j => M (i+1) (j+1)) (C*rate^2) rate := by
  refine ⟨mul_nonneg hM.const_nonneg (sq_nonneg _),hM.rate_nonneg,hM.rate_lt_one,fun i j => ?_⟩
  exact (hM.bound (i+1) (j+1)).trans_eq (by rw [pow_succ,pow_succ];ring)

/-- A zero first column removes the constant mode from every finite section and its Fredholm limit. -/
private theorem fdet_zero_column {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomDecay M C rate) (hzero : ∀ i, M i 0 = 0) (lam : ℂ) :
    fdet M lam = fdet (fun i j => M (i+1) (j+1)) lam := by
  have hn : Tendsto (fun N : ℕ => N+1) atTop atTop := tendsto_add_atTop_nat 1
  have hl := (tendsto_truncDet hM lam).comp hn
  have he : (fun N : ℕ => truncDet M lam (N+1)) =
      truncDet (fun i j => M (i+1) (j+1)) lam :=
    funext (truncDet_zero_column M hzero lam)
  change Tendsto (fun N : ℕ => truncDet M lam (N+1)) atTop _ at hl
  rw [he] at hl
  exact tendsto_nhds_unique hl (tendsto_truncDet (geometric_shift hM) lam)

private theorem centering_constant (c : ℂ) : centering (constant c) = 0 := by
  apply Subtype.ext
  ext z
  change c-c = 0
  exact sub_self c

private theorem centering_eq_self (f : DiscSpace) (hf : f.1 zeroPoint = 0) :
    centering f = f := by
  apply Subtype.ext
  ext z
  rw [centering_apply,hf,sub_zero]

private theorem derivative_centering (f : DiscSpace) {z : ℂ}
    (hz : z ∈ closedBall (1 : ℂ) 1) :
    derivativeEvaluation z hz (centering f) = derivativeEvaluation z hz f := by
  change derivativeEvaluation z hz (f-constant (f.1 zeroPoint)) = _
  rw [map_sub,derivativeEvaluation_constant,sub_zero]

/-- Positive eigenvalues of the actual compressed remainder lie below the source contraction bound. -/
theorem compressed_eigen_eq_zero {w μ : ℝ} (hw : 0 < w)
    (hμ : contraction w < μ) (f : DiscSpace)
    (heig : compressed (remainder (w : ℂ)) f = (μ : ℂ) • f) : f = 0 := by
  have hm : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    ((contraction_pos w).trans hμ).ne'
  have hf : f.1 zeroPoint = 0 := by
    have h := congrArg (fun g : DiscSpace => g.1 zeroPoint) heig
    change ((remainder (w : ℂ) (centering f)).1 zeroPoint-
      (remainder (w : ℂ) (centering f)).1 zeroPoint) = (μ : ℂ)*f.1 zeroPoint at h
    rw [sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hm
  apply derivative_eigen_eq_zero hw hμ f hf
  intro x hx
  have h := congrArg (derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx)) heig
  change derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx)
    (centering (remainder (w : ℂ) (centering f))) = _ at h
  rw [derivative_centering,centering_eq_self f hf,map_smul] at h
  exact h

private theorem centering_regularized {w : ℂ} (hw : 0 < w.re) (f : DiscSpace) :
    centering (regularized w hw f) = centering (remainder w f) := by
  rw [← source_eq hw,source,_root_.add_apply,_root_.smul_apply,map_add,map_smul]
  change riemannZeta w • centering (constant (f.1 zeroPoint))+_ = _
  rw [centering_constant,smul_zero,zero_add]

private theorem centering_monomial (j : ℕ) :
    centering (monomial j) = monomial j-(-1 : ℂ)^j • constant 1 := by
  apply Subtype.ext
  ext z
  change (z.1-1)^j-(0-1 : ℂ)^j = (z.1-1)^j-(-1 : ℂ)^j*1
  rw [zero_sub,mul_one]

/-- Synthesis compressed on the actual disc algebra and the coefficient Hilbert space. -/
def compressedSynthesis (w : ℂ) (hw : 0 < w.re) : SequenceSpace →L[ℂ] DiscSpace :=
  centering ∘L synthesisMap w hw ∘L
    (ContinuousLinearMap.id ℂ SequenceSpace-MayerCancellation.hilbertProjection)

/-- The reverse product representing the compressed source on Hilbert space. -/
def compressedHilbert (w : ℂ) (hw : 0 < w.re) : SequenceSpace →L[ℂ] SequenceSpace :=
  analysisMap ∘L compressedSynthesis w hw

/-- The constructed factorization is exactly double centering of the actual remainder. -/
theorem compressedSynthesis_analysis {w : ℂ} (hw : 0 < w.re) (f : DiscSpace) :
    compressedSynthesis w hw (analysisMap f) = compressed (remainder w) f := by
  have hs := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T (centering f))
    (synthesis_comp_analysis hw)
  change synthesisMap w hw (analysisMap (centering f)) = regularized w hw (centering f) at hs
  change centering (synthesisMap w hw (analysisMap f-
    MayerCancellation.hilbertProjection (analysisMap f))) = _
  rw [MayerCancellation.hilbertProjection_analysis,← map_sub]
  change centering (synthesisMap w hw (analysisMap (centering f))) = _
  rw [hs,centering_regularized]
  rfl

private theorem compressedSynthesis_single {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    compressedSynthesis w hw (lp.single 2 j 1) =
      ((balanceRadius : ℂ)^j)⁻¹ • compressed (remainder w) (monomial j) := by
  have hm : synthesisMap w hw (lp.single 2 j 1) = vector w hw j := synthesis_mode hw j
  have hc : synthesisMap w hw MayerCancellation.constantVector = regularized w hw (constant 1) :=
    congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T (constant 1)) (synthesis_comp_analysis hw)
  change centering (synthesisMap w hw (lp.single 2 j 1-
    MayerCancellation.hilbertProjection (lp.single 2 j 1))) = _
  rw [MayerCancellation.hilbertProjection,ContinuousLinearMap.smulRight_apply,
    MayerCancellation.coefficientEvaluation_single,map_sub,map_smul,hm,hc,vector,
    map_sub,map_smul,centering_regularized hw,map_smul,centering_regularized hw]
  change ((balanceRadius : ℂ)^j)⁻¹ • centering (remainder w (monomial j))-
    MayerCancellation.evaluationWeight j • centering (remainder w (constant 1)) =
    ((balanceRadius : ℂ)^j)⁻¹ • centering (remainder w (centering (monomial j)))
  rw [centering_monomial,map_sub,map_smul,map_sub,map_smul,smul_sub,smul_smul]
  rfl

/-- The compressed Hilbert operator has the actual doubly centered Cauchy matrix. -/
theorem matrixOf_compressedHilbert {w : ℂ} (hw : 0 < w.re) :
    HilbertSchmidt.matrixOf (compressedHilbert w hw) =
      fun p => MayerPole.operatorMatrix (compressed (remainder w)) p.1 p.2 := by
  funext p
  change (analysisMap (compressedSynthesis w hw (lp.single 2 p.2 1)) : ℕ → ℂ) p.1 = _
  rw [analysis_coordinate,compressedSynthesis_single]
  rfl

/-- Reconstruction from the geometric kernel recovers the constructed bounded operator. -/
theorem toOperator_compressed {w : ℂ} (hw : 0 < w.re) :
    HilbertSchmidt.toOperator (MayerCancellation.geometric_isHS
      (compressed_remainder_geometric hw)) = compressedHilbert w hw := by
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (HilbertSchmidt.lpBasis ℕ).dense_span) ?_
  rintro x ⟨j,rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  apply lp.ext
  funext i
  rw [HilbertSchmidt.toOperator_single]
  exact (congrFun (matrixOf_compressedHilbert hw) (i,j)).symm

private theorem compressed_zero_column (w : ℂ) (i : ℕ) :
    MayerPole.operatorMatrix (compressed (remainder w)) i 0 = 0 := by
  have hm : monomial 0 = constant 1 := by
    apply Subtype.ext
    ext z
    change (z.1-1)^0 = 1
    exact pow_zero _
  change functional i (((balanceRadius : ℂ)^0)⁻¹ •
    centering (remainder w (centering (monomial 0)))) = 0
  rw [hm,centering_constant,map_zero,map_zero,smul_zero,map_zero]

/-- Removing the zero constant column identifies the full compressed determinant with its complement. -/
theorem fdet_compressed_eq_complement {w : ℂ} (hw : 0 < w.re) (lam : ℂ) :
    fdet (MayerPole.operatorMatrix (compressed (remainder w))) lam =
      fdet (complementaryMatrix (remainder w)) lam := by
  rw [fdet_zero_column (compressed_remainder_geometric hw) (compressed_zero_column w)]
  congr 1
  funext i j
  exact (complementaryMatrix_eq_compressed _ i j).symm

/-- Every nonzero compressed Hilbert eigenvector synthesizes to a nonzero source eigenfunction. -/
theorem compressed_eigenvector_transfer {w μ : ℂ} (hw : 0 < w.re) (hμ : μ ≠ 0)
    (x : SequenceSpace) (hx0 : x ≠ 0) (hx : compressedHilbert w hw x = μ • x) :
    ∃ f : DiscSpace, f ≠ 0 ∧ compressed (remainder w) f = μ • f := by
  refine ⟨compressedSynthesis w hw x,?_,?_⟩
  · intro hzero
    have h : μ • x = 0 := by
      rw [← hx]
      change analysisMap (compressedSynthesis w hw x) = 0
      rw [hzero,map_zero]
    exact hx0 ((smul_eq_zero.mp h).resolve_left hμ)
  · rw [← compressedSynthesis_analysis hw]
    change compressedSynthesis w hw (compressedHilbert w hw x) = _
    rw [hx,map_smul]

private theorem contraction_lt_inv {w lam : ℝ} (hlam : 0 < lam)
    (hupper : lam < (3/2 : ℝ)^w) : contraction w < lam⁻¹ := by
  have hp : (3/2 : ℝ)^w ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) w).ne'
  have h := mul_lt_mul_of_pos_left hupper (contraction_pos w)
  have he : contraction w*(3/2 : ℝ)^w = 1 := by
    rw [contraction,Real.rpow_neg (by norm_num),inv_mul_cancel₀ hp]
  rw [he] at h
  rw [← one_div,lt_div_iff₀ hlam]
  exact h

/-- The actual pole coefficient never vanishes in the positive source-controlled spectral interval. -/
theorem polePart_ne_zero {w lam : ℝ} (hw : 0 < w) (hlam : 0 < lam)
    (hupper : lam < (3/2 : ℝ)^w) : MayerPole.polePart (w : ℂ) (lam : ℂ) ≠ 0 := by
  have hwc : 0 < (w : ℂ).re := hw
  have hlc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  intro hzero
  rw [polePart_eq_complement hwc, mul_eq_zero] at hzero
  have hdet := hzero.resolve_left (neg_ne_zero.mpr hlc)
  rw [← fdet_compressed_eq_complement hwc] at hdet
  obtain ⟨x,hx0,hx⟩ := (fdet_zero_iff_hilbert_eigenvector
    (compressed_remainder_geometric hwc) hlc).mp hdet
  rw [toOperator_compressed hwc] at hx
  obtain ⟨f,hf0,hf⟩ := compressed_eigenvector_transfer hwc (inv_ne_zero hlc) x hx0 hx
  have heig : compressed (remainder (w : ℂ)) f = ((lam⁻¹ : ℝ) : ℂ) • f := by
    simpa only [Complex.ofReal_inv] using hf
  exact hf0 (compressed_eigen_eq_zero hw (contraction_lt_inv hlam hupper) f heig)

/-- At the positive unit spectral parameter, the actual source pole has nonzero residue. -/
theorem polePart_one_one_ne_zero : MayerPole.polePart 1 1 ≠ 0 := by
  simpa only [Complex.ofReal_one] using
    (polePart_ne_zero (w := 1) (lam := 1) (by norm_num) (by norm_num) (by norm_num))

/-- The actual positive-unit Mayer determinant has a genuine simple pole at the source parameter one. -/
theorem sourceDeterminant_one_simple_pole :
    meromorphicOrderAt (fun w => sourceDeterminant w 1) 1 = -1 :=
  MayerPole.sourceDeterminant_order_of_residue_ne_zero polePart_one_one_ne_zero

#print axioms fdet_zero_iff_hilbert_eigenvector
#print axioms compressed_eigen_eq_zero
#print axioms compressedSynthesis_analysis
#print axioms matrixOf_compressedHilbert
#print axioms toOperator_compressed
#print axioms fdet_compressed_eq_complement
#print axioms compressed_eigenvector_transfer
#print axioms polePart_ne_zero
#print axioms polePart_one_one_ne_zero
#print axioms sourceDeterminant_one_simple_pole

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPositivePole
