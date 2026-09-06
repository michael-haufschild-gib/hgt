import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHilbertBasis
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspHeat
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

/-!
# The basis-independent analytic heat trace of the physical Hilbert flow

For every strict contraction parameter the proved physical Hilbert flow is
Hilbert–Schmidt. Its square-root parameter factors it into two such operators.
The corpus's analytic product trace is therefore summable and independent of
Hilbert basis. Its value is q/(1-q), and physical heat time recovers exactly
the previously derived normalization-defect heat.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete


def cubicHilbertStrictFlow (q : Ico (0:ℝ) 1) : cubicDefectHilbert →L[ℝ] cubicDefectHilbert :=
  cubicHilbertFlow ⟨q.val,⟨q.property.1,q.property.2.le⟩⟩

theorem cubicHilbertStrictFlow_basis (q : Ico (0:ℝ) 1) (k : ℕ) :
    cubicHilbertStrictFlow q (cubicHilbertBasis k)=q.val^(k+1) • cubicHilbertBasis k :=
  cubicHilbertFlow_basis ⟨q.val,⟨q.property.1,q.property.2.le⟩⟩ k

theorem cubicHilbertStrictFlow_hilbertSchmidt (q : Ico (0:ℝ) 1) :
    ContinuousLinearMap.IsHilbertSchmidt (cubicHilbertStrictFlow q) := by
  apply ContinuousLinearMap.isHilbertSchmidt_of_summable cubicHilbertBasis
  have hq : q.val^2 < 1 := by nlinarith [q.property.1,q.property.2]
  have hs := (hasSum_geometric_of_lt_one (sq_nonneg q.val) hq).summable.mul_left (q.val^2)
  apply hs.congr
  intro k
  rw [cubicHilbertStrictFlow_basis,norm_smul,cubicHilbertBasis.orthonormal.1 k,mul_one,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg q.property.1 _)]
  rw [pow_right_comm q.val (k+1) 2,pow_succ (q.val^2) k]
  ring

def cubicHilbertStrictRoot (q : Ico (0:ℝ) 1) : Ico (0:ℝ) 1 :=
  ⟨Real.sqrt q.val,⟨Real.sqrt_nonneg _,by
    have h := Real.sq_sqrt q.property.1
    have hn := Real.sqrt_nonneg q.val
    nlinarith [q.property.2]⟩⟩

theorem cubicHilbertStrictRoot_square (q : Ico (0:ℝ) 1) :
    (cubicHilbertStrictRoot q).val*(cubicHilbertStrictRoot q).val=q.val := by
  change Real.sqrt q.val*Real.sqrt q.val=q.val
  nlinarith [Real.sq_sqrt q.property.1]

theorem cubicHilbertStrictFlow_factor (q : Ico (0:ℝ) 1) :
    cubicHilbertStrictFlow q=(cubicHilbertStrictFlow (cubicHilbertStrictRoot q)).comp
      (cubicHilbertStrictFlow (cubicHilbertStrictRoot q)) := by
  unfold cubicHilbertStrictFlow
  rw [cubicHilbertFlow_mul]
  congr 1
  apply Subtype.ext
  exact (cubicHilbertStrictRoot_square q).symm

theorem cubicHilbertStrictFlow_diagonal (q : Ico (0:ℝ) 1) (k : ℕ) :
    inner ℝ (cubicHilbertBasis k) (cubicHilbertStrictFlow q (cubicHilbertBasis k))=q.val^(k+1) := by
  rw [cubicHilbertStrictFlow_basis,inner_smul_right,real_inner_self_eq_norm_sq,
    cubicHilbertBasis.orthonormal.1 k,one_pow,mul_one]

theorem cubicHilbertStrictFlow_diagonal_hasSum (q : Ico (0:ℝ) 1) :
    HasSum (fun k => inner ℝ (cubicHilbertBasis k)
      (cubicHilbertStrictFlow q (cubicHilbertBasis k))) (q.val/(1-q.val)) := by
  have hs := (hasSum_geometric_of_lt_one q.property.1 q.property.2).mul_left q.val
  have ht : (fun k => inner ℝ (cubicHilbertBasis k)
      (cubicHilbertStrictFlow q (cubicHilbertBasis k)))=(fun k => q.val*q.val^k) := by
    funext k
    rw [cubicHilbertStrictFlow_diagonal,pow_succ,mul_comm]
  rw [ht]
  simpa only [div_eq_mul_inv] using hs

theorem cubicHilbertStrictFlow_trace (q : Ico (0:ℝ) 1) :
    ContinuousLinearMap.opTrace (cubicHilbertStrictFlow q)=q.val/(1-q.val) := by
  calc
    _ = ∑' k, inner ℝ (cubicHilbertBasis k)
        (cubicHilbertStrictFlow q (cubicHilbertBasis k)) := by
      rw [cubicHilbertStrictFlow_factor q]
      exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis
        (cubicHilbertStrictFlow_hilbertSchmidt (cubicHilbertStrictRoot q))
        (cubicHilbertStrictFlow_hilbertSchmidt (cubicHilbertStrictRoot q)) cubicHilbertBasis
    _ = _ := (cubicHilbertStrictFlow_diagonal_hasSum q).tsum_eq

theorem cubicHilbertStrictFlow_trace_hasSum (q : Ico (0:ℝ) 1)
    {ι : Type*} (b : HilbertBasis ι ℝ cubicDefectHilbert) :
    HasSum (fun i => inner ℝ (b i) (cubicHilbertStrictFlow q (b i))) (q.val/(1-q.val)) := by
  have hs := ContinuousLinearMap.summable_inner_diag_comp
    (cubicHilbertStrictFlow_hilbertSchmidt (cubicHilbertStrictRoot q))
    (cubicHilbertStrictFlow_hilbertSchmidt (cubicHilbertStrictRoot q)) b
  have ht := ContinuousLinearMap.opTrace_comp_eq_tsum_basis
    (cubicHilbertStrictFlow_hilbertSchmidt (cubicHilbertStrictRoot q))
    (cubicHilbertStrictFlow_hilbertSchmidt (cubicHilbertStrictRoot q)) b
  rw [← cubicHilbertStrictFlow_factor q] at hs ht
  rw [cubicHilbertStrictFlow_trace q] at ht
  exact ht.symm ▸ hs.hasSum

def cubicHilbertHeatOperator (u : ℝ) : cubicDefectHilbert →L[ℝ] cubicDefectHilbert :=
  cubicHilbertStrictFlow ⟨Real.exp (-Real.exp u),
    ⟨(cubicCuspHeat_parameter u).1.le,(cubicCuspHeat_parameter u).2⟩⟩

theorem cubicHilbertHeatOperator_trace (u : ℝ) :
    ContinuousLinearMap.opTrace (cubicHilbertHeatOperator u)=cubicCuspHeat u := by
  rw [cubicHilbertHeatOperator,cubicHilbertStrictFlow_trace,cubicCuspHeat_eq]
  change Real.exp (-Real.exp u)/(1-Real.exp (-Real.exp u))=1/(Real.exp (Real.exp u)-1)
  have hd : Real.exp (Real.exp u)-1≠0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (Real.exp_pos u)))
  rw [Real.exp_neg]
  field_simp

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
