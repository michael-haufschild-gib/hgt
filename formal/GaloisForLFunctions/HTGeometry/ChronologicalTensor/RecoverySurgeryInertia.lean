import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryObstruction
import GaloisForLFunctions.HTGeometry.MomentFiniteCoordinateValue
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Exact inertia of the first failing geometric Hankel matrix

The protected polynomial subspace gives d positive directions. The exact
negative square gives one negative direction. Sylvester's dimension identity
then forces positive index d, negative index one, and zero-dimensional radical.
The quadratic form is the literal finite Hankel matrix of geometric moments.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set MeasureTheory
open _root_.HTGeometry

def recoveryHankelForm (n d : ℕ) : QuadraticForm ℝ (Fin (d+1) → ℝ) :=
  (momentHankelMatrix (recoverySurgeryMoment n) (d+1)).toQuadraticForm'

theorem recoveryHankelForm_value (n d : ℕ) (v : Fin (d+1) → ℝ) :
    recoveryHankelForm n d v = momentFunctional (recoverySurgeryMoment n) ((ofFn (d+1) v)^2) := by
  rw [recoveryHankelForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct_mulVec_momentHankelMatrix]

def recoveryZeroExtend (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin (d+1) → ℝ) where
  toFun v := Fin.snoc v 0
  map_add' v w := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' r v := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem recoveryZeroExtend_injective (d : ℕ) : Function.Injective (recoveryZeroExtend d) := by
  intro v w he
  funext i
  have h := congrFun he i.castSucc
  simpa only [recoveryZeroExtend, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc] using h

theorem recoveryZeroExtend_polynomial (d : ℕ) (v : Fin d → ℝ) :
    ofFn (d+1) (recoveryZeroExtend d v) = ofFn d v := by
  rw [ofFn_eq_sum_monomial, Fin.sum_univ_castSucc]
  simp only [recoveryZeroExtend, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last,
    map_zero, add_zero]
  exact (ofFn_eq_sum_monomial v).symm

theorem recoveryHankelForm_positive_index (n d : ℕ) (hd : 0 < d) (hn : 2*(d-1) ≤ n) :
    d ≤ sigPos (recoveryHankelForm n d) := by
  let V := (recoveryZeroExtend d).range
  have hdim : Module.finrank ℝ V=d := by
    rw [LinearMap.finrank_range_of_inj (recoveryZeroExtend_injective d)]
    simp
  have hpos : ((recoveryHankelForm n d).restrict V).PosDef := by
    intro x hx
    obtain ⟨v,hv⟩ := x.property
    have hvne : v ≠ 0 := by
      intro he
      apply hx
      apply Subtype.ext
      rw [← hv, he, map_zero]
      rfl
    have hp : ofFn d v ≠ 0 := by
      intro he
      apply hvne
      apply injective_ofFn d
      rw [he, ofFn_zero]
    change 0 < recoveryHankelForm n d x.val
    rw [← hv, recoveryHankelForm_value, recoveryZeroExtend_polynomial]
    apply recoverySurgeryMoment_square_prefix_positive n _ hp
    have hdeg := ofFn_natDegree_lt hd v
    omega
  have h := le_sigPos_of_posDef (recoveryHankelForm n d) hpos
  rwa [hdim] at h

theorem recoveryQuadraticForm_negative_index (d : ℕ) (Q : QuadraticForm ℝ (Fin d → ℝ))
    (v : Fin d → ℝ) (hv : Q v < 0) : 1 ≤ sigNeg Q := by
  have hvne : v ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    linarith
  have hpos : ((-Q).restrict (ℝ ∙ v)).PosDef := by
    intro x hx
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp x.property
    have hrne : r ≠ 0 := by
      intro h
      apply hx
      apply Subtype.ext
      rw [← hr, h, zero_smul]
      rfl
    change 0 < -Q x.val
    rw [← hr, Q.map_smul, smul_eq_mul]
    have h := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hrne) hv
    nlinarith
  have h := le_sigNeg_of_negDef Q hpos
  rwa [finrank_span_singleton hvne] at h

theorem recoverySurgery_dyadic_inertia (j : ℕ) :
    sigPos (recoveryHankelForm ((2 : ℕ)^(j+4)-1) ((2 : ℕ)^(j+3))) = (2 : ℕ)^(j+3) ∧
    sigNeg (recoveryHankelForm ((2 : ℕ)^(j+4)-1) ((2 : ℕ)^(j+3))) = 1 ∧
    Module.finrank ℝ (recoveryHankelForm ((2 : ℕ)^(j+4)-1) ((2 : ℕ)^(j+3))).radical = 0 := by
  let d := (2 : ℕ)^(j+3)
  let n := (2 : ℕ)^(j+4)-1
  have hd : 0 < d := by dsimp [d]; positivity
  have hn : n = 2*d-1 := by
    dsimp [n,d]
    rw [show j+4=(j+3)+1 by omega, pow_succ]
    omega
  have hp := recoveryHankelForm_positive_index n d hd (by omega)
  let w := toFn (d+1) (recoveryMomentWitness (d-1))
  have hw : recoveryHankelForm n d w < 0 := by
    rw [recoveryHankelForm_value, show ofFn (d+1) w=recoveryMomentWitness (d-1) from
      ofFn_comp_toFn_eq_id_of_natDegree_lt (by rw [recoveryMomentWitness_degree]; omega)]
    exact recoverySurgery_dyadic_negative j
  have hm := recoveryQuadraticForm_negative_index (d+1) (recoveryHankelForm n d) w hw
  have hs := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := recoveryHankelForm n d)
  have hdim : Module.finrank ℝ (Fin (d+1) → ℝ) = d+1 := by simp
  rw [hdim] at hs
  change sigPos (recoveryHankelForm n d)=d ∧ sigNeg (recoveryHankelForm n d)=1 ∧
    Module.finrank ℝ (recoveryHankelForm n d).radical=0
  omega

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
