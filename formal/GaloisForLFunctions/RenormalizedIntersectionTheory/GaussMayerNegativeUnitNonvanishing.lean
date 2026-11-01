import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerNegativeUnitRigidity

/-!
# Nonvanishing of the actual negative-unit Mayer determinant

Subtracting the actual zeta constant mode from synthesis factors the
remainder through its existing Hilbert realization. Its geometric
Cauchy matrix gives the exact Fredholm/Carleman identity, and synthesis
transports every nonzero eigenvalue back to the source disc algebra.

Negative-unit source rigidity therefore makes the remainder determinant
nonzero for every real `w>0`. Exact scalar-mode cancellation gives the
same conclusion for every complex constant-mode perturbation and for
the actual source determinant, including its analytic value at one.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCancellation
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNegativePole

/-- Synthesis with only the actual zeta constant mode removed. -/
def remainderSynthesis (w : ℂ) (hw : 0 < w.re) : SequenceSpace →L[ℂ] DiscSpace :=
  synthesisMap w hw-riemannZeta w • coefficientEvaluation.smulRight (constant 1)

private theorem constant_smul_one (c : ℂ) : c • constant 1 = constant c := by
  apply Subtype.ext
  ext z
  change c*1 = c
  exact mul_one c

/-- The constructed remainder synthesis recovers the actual source remainder on Cauchy coefficients. -/
theorem remainderSynthesis_analysis {w : ℂ} (hw : 0 < w.re) (f : DiscSpace) :
    remainderSynthesis w hw (analysisMap f) = remainder w f := by
  have hs := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T f) (synthesis_comp_analysis hw)
  change synthesisMap w hw (analysisMap f) = regularized w hw f at hs
  rw [remainderSynthesis,_root_.sub_apply,_root_.smul_apply,ContinuousLinearMap.smulRight_apply,
    coefficientEvaluation_analysis,hs,constant_smul_one]
  rw [← source_eq hw,source,_root_.add_apply,_root_.smul_apply]
  change riemannZeta w • constant (f.1 zeroPoint)+remainder w f-
    riemannZeta w • constant (f.1 zeroPoint) = remainder w f
  exact add_sub_cancel_left _ _

/-- The reverse product is precisely the existing Hilbert remainder operator. -/
theorem analysis_remainderSynthesis {w : ℂ} (hw : 0 < w.re) (x : SequenceSpace) :
    analysisMap (remainderSynthesis w hw x) = remainderOperator w hw x := by
  rw [remainderSynthesis,_root_.sub_apply,_root_.smul_apply,ContinuousLinearMap.smulRight_apply,
    map_sub,map_smul,map_smul]
  rfl

private theorem matrixOf_remainder {w : ℂ} (hw : 0 < w.re) :
    HilbertSchmidt.matrixOf (remainderOperator w hw) =
      fun p => MayerPole.remainderMatrix w p.1 p.2 := by
  funext p
  change HilbertSchmidt.matrixOf (hilbertOperator w hw) p-
    riemannZeta w*HilbertSchmidt.matrixOf hilbertProjection p = _
  rw [matrixOf_hilbertOperator,matrixOf_hilbertProjection,← sourceMatrix_eq hw]
  change sourceMatrix w p.1 p.2-riemannZeta w*MayerPole.projectionMatrix p.1 p.2 = _
  rw [MayerPole.sourceMatrix_decomposition]
  ring

private theorem toOperator_remainder {w : ℂ} (hw : 0 < w.re) {C : ℝ}
    (hM : GeomFredholm.GeomDecay (MayerPole.remainderMatrix w) C rate) :
    HilbertSchmidt.toOperator (geometric_isHS hM) = remainderOperator w hw := by
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (HilbertSchmidt.lpBasis ℕ).dense_span) ?_
  rintro x ⟨j,rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  apply lp.ext
  funext i
  rw [HilbertSchmidt.toOperator_single]
  exact (congrFun (matrixOf_remainder hw) (i,j)).symm

/-- Every nonzero Hilbert remainder eigenvector synthesizes to an actual source eigenfunction. -/
theorem remainder_eigenvector_transfer {w μ : ℂ} (hw : 0 < w.re) (hμ : μ ≠ 0)
    (x : SequenceSpace) (hx0 : x ≠ 0) (hx : remainderOperator w hw x = μ • x) :
    ∃ f : DiscSpace, f ≠ 0 ∧ remainder w f = μ • f := by
  refine ⟨remainderSynthesis w hw x,?_,?_⟩
  · intro hzero
    have h : μ • x = 0 := by
      rw [← hx,← analysis_remainderSynthesis hw,hzero,map_zero]
    exact hx0 ((smul_eq_zero.mp h).resolve_left hμ)
  · rw [← remainderSynthesis_analysis hw,analysis_remainderSynthesis hw,hx,map_smul]

/-- The holomorphic remainder determinant is nonzero at the negative unit for every positive real source. -/
theorem regularPart_negative_one_ne_zero {w : ℝ} (hw : 0 < w) :
    MayerPole.regularPart (w : ℂ) (-1) ≠ 0 := by
  have hwc : 0 < (w : ℂ).re := hw
  obtain ⟨r,C,hr,_,hC⟩ := MayerPole.remainderMatrix_local_bound hwc
  have hM := hC (w : ℂ) (mem_closedBall_self hr.le)
  have he : MayerPole.perturbedMatrix (w : ℂ) 0 = MayerPole.remainderMatrix (w : ℂ) := by
    funext i j
    simp only [MayerPole.perturbedMatrix,zero_mul,add_zero]
  change GeomFredholm.fdet (MayerPole.perturbedMatrix (w : ℂ) 0) (-1) ≠ 0
  rw [he]
  intro hz
  rw [fdet_negative_one_eq_entireDet2 hM,mul_eq_zero,
    or_iff_left (Complex.exp_ne_zero _)] at hz
  obtain ⟨x,hx0,hx⟩ := (entireDet2_eq_zero_iff_exists_eigenvector (geometric_isHS hM)
    (by norm_num : (-1 : ℂ) ≠ 0)).mp hz
  rw [toOperator_remainder hwc hM] at hx
  obtain ⟨f,hf0,hf⟩ := remainder_eigenvector_transfer hwc
    (by norm_num : (-1 : ℂ)⁻¹ ≠ 0) x hx0 hx
  have hf' : remainder (w : ℂ) f = -f := by
    simpa only [inv_neg,inv_one,neg_smul,one_smul] using hf
  exact hf0 (remainder_negative_eigen_eq_zero hw f hf')

/-- Every scalar constant-mode perturbation has nonzero negative-unit determinant at a positive real source. -/
theorem perturbedDeterminant_negative_one_ne_zero {w : ℝ} (hw : 0 < w) (t : ℂ) :
    MayerPole.perturbedDeterminant (w : ℂ) t (-1) ≠ 0 := by
  rw [perturbedDeterminant_negative_one (w := (w : ℂ)) hw t]
  exact regularPart_negative_one_ne_zero hw

/-- The actual negative-unit source determinant is nonzero on the whole positive real axis, including one. -/
theorem sourceDeterminant_negative_one_ne_zero {w : ℝ} (hw : 0 < w) :
    sourceDeterminant (w : ℂ) (-1) ≠ 0 := by
  rw [sourceDeterminant_negative_one (w := (w : ℂ)) hw]
  exact regularPart_negative_one_ne_zero hw

#print axioms remainderSynthesis_analysis
#print axioms analysis_remainderSynthesis
#print axioms remainder_eigenvector_transfer
#print axioms regularPart_negative_one_ne_zero
#print axioms perturbedDeterminant_negative_one_ne_zero
#print axioms sourceDeterminant_negative_one_ne_zero
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNegativePole
