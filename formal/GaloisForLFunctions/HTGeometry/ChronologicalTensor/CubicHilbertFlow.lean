import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicDefectCompletion
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspFlow

/-!
# Retraction dynamics on the graded physical Hilbert space

The actual quotient line of weight k+1 is multiplied by q^(k+1). Pointwise
norm domination constructs a bounded map on the Hilbert sum, with exact
operator norm q. The maps are positive and symmetric, act diagonally on every
actual grade, and satisfy the multiplication law and both endpoint identities.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete


theorem cubicHilbertFlow_weightBound (q : Icc (0:ℝ) 1) (k : ℕ) :
    ‖q.val^(k+1)‖≤q.val := by
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg q.property.1 _),pow_succ]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (pow_le_one₀ q.property.1 q.property.2 : q.val^k≤1) q.property.1

theorem cubicHilbertFlow_gradeBound (q : Icc (0:ℝ) 1) (k : ℕ) (x : cubicGradedDefect k) :
    ‖q.val^(k+1) • x‖≤q.val*‖x‖ := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (cubicHilbertFlow_weightBound q k) (norm_nonneg x)

def cubicHilbertFlowLinear (q : Icc (0:ℝ) 1) : cubicDefectHilbert →ₗ[ℝ] cubicDefectHilbert where
  toFun x := ⟨fun k => q.val^(k+1) • x k, (lp.memℓp (q.val • x)).mono' (fun k => by
    change ‖q.val^(k+1) • x k‖≤‖q.val • x k‖
    rw [norm_smul q.val (x k),Real.norm_eq_abs,abs_of_nonneg q.property.1]
    exact cubicHilbertFlow_gradeBound q k (x k))⟩
  map_add' x y := by
    apply lp.ext
    funext k
    exact smul_add _ _ _
  map_smul' r x := by
    apply lp.ext
    funext k
    exact smul_comm (q.val^(k+1)) r (x k)

theorem cubicHilbertFlowLinear_bound (q : Icc (0:ℝ) 1) (x : cubicDefectHilbert) :
    ‖cubicHilbertFlowLinear q x‖≤q.val*‖x‖ := by
  have h : ‖cubicHilbertFlowLinear q x‖≤‖q.val • x‖ :=
    lp.norm_mono (by simp) (fun k => by
      change ‖q.val^(k+1) • x k‖≤‖q.val • x k‖
      rw [norm_smul q.val (x k),Real.norm_eq_abs,abs_of_nonneg q.property.1]
      exact cubicHilbertFlow_gradeBound q k (x k))
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg q.property.1] using h

def cubicHilbertFlow (q : Icc (0:ℝ) 1) : cubicDefectHilbert →L[ℝ] cubicDefectHilbert :=
  (cubicHilbertFlowLinear q).mkContinuous q.val (cubicHilbertFlowLinear_bound q)

theorem cubicHilbertFlow_apply (q : Icc (0:ℝ) 1) (x : cubicDefectHilbert) (k : ℕ) :
    cubicHilbertFlow q x k=q.val^(k+1) • x k := rfl

theorem cubicHilbertFlow_norm_le (q : Icc (0:ℝ) 1) : ‖cubicHilbertFlow q‖≤q.val :=
  (cubicHilbertFlowLinear q).mkContinuous_norm_le q.property.1 (cubicHilbertFlowLinear_bound q)

theorem cubicHilbertFlow_inner (q : Icc (0:ℝ) 1) (x y : cubicDefectHilbert) :
    inner ℝ (cubicHilbertFlow q x) y=inner ℝ x (cubicHilbertFlow q y) := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [cubicHilbertFlow_apply,cubicHilbertFlow_apply,inner_smul_left,inner_smul_right]
  rfl

theorem cubicHilbertFlow_single (q : Icc (0:ℝ) 1) (k : ℕ) (x : cubicGradedDefect k) :
    cubicHilbertFlow q (cubicDefectHilbertSingle k x)=
      q.val^(k+1) • cubicDefectHilbertSingle k x := by
  apply lp.ext
  funext i
  rw [cubicHilbertFlow_apply]
  change q.val^(i+1) • (lp.single 2 k x i)=q.val^(k+1) • (lp.single 2 k x i)
  by_cases h : i=k
  · subst i; rfl
  · rw [lp.single_apply_ne 2 k x h,smul_zero,smul_zero]


theorem cubicHilbertFlow_norm (q : Icc (0:ℝ) 1) : ‖cubicHilbertFlow q‖=q.val := by
  apply le_antisymm (cubicHilbertFlow_norm_le q)
  let x := cubicDefectHilbertSingle 0 (cubicGradedDefectMk 0 (cubicHomogeneousMissing 0))
  have hx : ‖x‖=cubicGradedRecoveryGap 0 := by
    rw [cubicDefectHilbertSingle_observation,cubicGradedCoefficient_missing,abs_one,one_mul]
  have h := (cubicHilbertFlow q).le_opNorm x
  change ‖cubicHilbertFlow q (cubicDefectHilbertSingle 0 _)‖≤_ at h
  rw [cubicHilbertFlow_single,norm_smul,zero_add,pow_one,
    Real.norm_eq_abs,abs_of_nonneg q.property.1] at h
  change q.val*‖x‖≤‖cubicHilbertFlow q‖*‖x‖ at h
  rw [hx] at h
  nlinarith [cubicGradedRecoveryGap_positive 0]

theorem cubicHilbertFlow_one : cubicHilbertFlow ⟨1,by constructor <;> simp⟩=
    ContinuousLinearMap.id ℝ cubicDefectHilbert := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  change (1:ℝ)^(k+1) • x k=x k
  rw [one_pow,one_smul]

theorem cubicHilbertFlow_zero : cubicHilbertFlow ⟨0,by constructor <;> simp⟩=0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  change (0:ℝ)^(k+1) • x k=0
  rw [pow_succ,mul_zero,zero_smul]

theorem cubicHilbertFlow_mul (q r : Icc (0:ℝ) 1) :
    (cubicHilbertFlow q).comp (cubicHilbertFlow r)=cubicHilbertFlow
      ⟨q.val*r.val,⟨mul_nonneg q.property.1 r.property.1,by
        calc
          q.val*r.val≤1*r.val := mul_le_mul_of_nonneg_right q.property.2 r.property.1
          _≤1 := by simpa only [one_mul] using r.property.2⟩⟩ := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  change q.val^(k+1) • (r.val^(k+1) • x k)=(q.val*r.val)^(k+1) • x k
  rw [mul_pow,mul_smul]


theorem cubicHilbertFlow_positive (q : Icc (0:ℝ) 1) (x : cubicDefectHilbert) :
    0 ≤ inner ℝ x (cubicHilbertFlow q x) := by
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro k
  rw [cubicHilbertFlow_apply,inner_smul_right]
  exact mul_nonneg (pow_nonneg q.property.1 _) real_inner_self_nonneg

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
