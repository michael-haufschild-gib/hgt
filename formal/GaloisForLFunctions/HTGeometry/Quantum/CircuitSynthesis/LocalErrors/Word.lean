import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Commutator
import GaloisForLFunctions.HTGeometry.QuantitativeLieProductFormula

/-! # Lie product error summed over the commutators of a finite interaction word -/
open NormedSpace
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {A : Type*} [CStarAlgebra A]
local instance lieWordRationalAlgebra : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

private theorem commutator_list_sum_norm_le (x : A) (w : List A) :
    ‖x*w.sum-w.sum*x‖ ≤ (w.map fun y => ‖x*y-y*x‖).sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.sum_cons,List.map_cons]
    rw [mul_add,add_mul,add_sub_add_comm]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

private theorem commutator_subword_error (z w : List A) (hw : w.Sublist z)
    (hz : ∀ x ∈ z, x ∈ skewAdjoint A) (t : ℝ) (ht : 0 ≤ t) :
    ‖(w.map fun x => exp (t • x)).prod-exp (t • w.sum)‖ ≤
      t^2*(w.map fun x => (z.map fun y => ‖x*y-y*x‖).sum).sum := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have htail : w.Sublist z := (List.sublist_cons_self x w).trans hw
    have hx := hz x (hw.subset List.mem_cons_self)
    have hs := list_sum_mem_addSubgroup (skewAdjoint A) w (fun a ha => hz a (htail.subset ha))
    let U := exp (t • x)
    let P := (w.map fun y => exp (t • y)).prod
    let V := exp (t • w.sum)
    have hu : U ∈ unitary A := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hx)
    have hdist : ‖U*P-U*V‖ = ‖P-V‖ := by
      rw [← mul_sub,CStarRing.norm_mem_unitary_mul _ hu]
    have hrow := (htail.map (fun y => ‖x*y-y*x‖)).sum_le_sum (by
      intro a ha
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp ha
      exact norm_nonneg _)
    have hpair := (norm_lie_pair_error_le_commutator x w.sum hx hs t ht).trans
      (mul_le_mul_of_nonneg_left ((commutator_list_sum_norm_le x w).trans hrow) (sq_nonneg t))
    change ‖U*P-exp (t • (x+w.sum))‖ ≤ t^2*(_+_)
    rw [mul_add,add_comm (t^2*_)]
    exact (norm_sub_le_norm_sub_add_norm_sub (U*P) (U*V) _).trans
      (add_le_add (hdist.le.trans (ih htail)) hpair)

/-- Repeating the ordered product r times bounds its error by the full
commutator sum times t²/r. Disjoint terms have zero contribution. -/
theorem lie_word_repeated_commutator_error (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    ‖(z.map fun x => exp ((t/(r:ℝ)) • x)).prod^r-exp (t • z.sum)‖ ≤
      t^2/(r:ℝ)*(z.map fun x => (z.map fun y => ‖x*y-y*x‖).sum).sum := by
  let h := t/(r:ℝ)
  let U := (z.map fun x => exp (h • x)).prod
  let V := exp (h • z.sum)
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hU : U ∈ unitary A := list_exp_product_mem_unitary z hz h
  have hV : V ∈ unitary A := exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem h (list_sum_mem_addSubgroup (skewAdjoint A) z hz))
  have he : V^r = exp (t • z.sum) := by
    dsimp [V,h]; rw [exp_real_smul_pow]; congr 2; field_simp
  rw [← he]
  calc
    _ ≤ (r:ℝ)*‖U-V‖ := unitary_pow_norm_sub_pow_le U V hU hV r
    _ ≤ (r:ℝ)*(h^2*_) := mul_le_mul_of_nonneg_left
      (commutator_subword_error z z (List.Sublist.refl _) hz h (div_nonneg ht hr'.le)) hr'.le
    _ = _ := by dsimp [h]; field_simp

#print axioms lie_word_repeated_commutator_error
end
end GaloisForLFunctions.HTGeometry

