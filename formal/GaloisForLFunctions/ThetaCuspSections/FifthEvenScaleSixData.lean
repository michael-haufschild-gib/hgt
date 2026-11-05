import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightData

/-!
# A negative comparison matrix at theta scale six

The rational leading-pair model with cross-load coefficient `−100` and
quadratic allowance `1/20` has a negative direction. Exact Schur elimination
identifies that direction without discarding the positive leading block.
-/
noncomputable section
open Matrix
namespace GaloisForLFunctions.ThetaCuspSections.QuarticSixUpper
open FifthLeadingPair EightCrossData
open scoped EightCrossData

private def model : Matrix (Fin 5) (Fin 5) ℝ := polyModel 6 (1522998/100000000000000) (-100) (1/20)

private def cell00 : {v : ℝ // model 0 0 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell01 : {v : ℝ // model 0 1 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell02 : {v : ℝ // model 0 2 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell03 : {v : ℝ // model 0 3 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell04 : {v : ℝ // model 0 4 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell11 : {v : ℝ // model 1 1 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell12 : {v : ℝ // model 1 2 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell13 : {v : ℝ // model 1 3 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell14 : {v : ℝ // model 1 4 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell22 : {v : ℝ // model 2 2 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell23 : {v : ℝ // model 2 3 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell24 : {v : ℝ // model 2 4 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell33 : {v : ℝ // model 3 3 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell34 : {v : ℝ // model 3 4 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def cell44 : {v : ℝ // model 4 4 = v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      dsimp only [model]
      tactic => norm_cross_model
      norm_num [Fin.ext_iff]

private def matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![cell00.val,cell01.val,cell02.val,cell03.val,cell04.val],
    ![cell01.val,cell11.val,cell12.val,cell13.val,cell14.val],
    ![cell02.val,cell12.val,cell22.val,cell23.val,cell24.val],
    ![cell03.val,cell13.val,cell23.val,cell33.val,cell34.val],
    ![cell04.val,cell14.val,cell24.val,cell34.val,cell44.val]]

private theorem cons5_two {α : Type*} (a : α) (f : Fin 4 → α) :
    Matrix.vecCons a f (2 : Fin 5) = f 1 := rfl
private theorem cons5_three {α : Type*} (a : α) (f : Fin 4 → α) :
    Matrix.vecCons a f (3 : Fin 5) = f 2 := rfl
private theorem cons5_four {α : Type*} (a : α) (f : Fin 4 → α) :
    Matrix.vecCons a f (4 : Fin 5) = f 3 := rfl
private theorem cons4_two {α : Type*} (a : α) (f : Fin 3 → α) :
    Matrix.vecCons a f (2 : Fin 4) = f 1 := rfl
private theorem cons4_three {α : Type*} (a : α) (f : Fin 3 → α) :
    Matrix.vecCons a f (3 : Fin 4) = f 2 := rfl
private theorem cons3_two {α : Type*} (a : α) (f : Fin 2 → α) :
    Matrix.vecCons a f (2 : Fin 3) = f 1 := rfl
private theorem tailIndex_zero : tailIndex (0 : Fin 3) = (2 : Fin 5) := rfl
private theorem tailIndex_one : tailIndex (1 : Fin 3) = (3 : Fin 5) := rfl
private theorem tailIndex_two : tailIndex (2 : Fin 3) = (4 : Fin 5) := rfl

private theorem first_pos : 0 < matrix 0 0 := by
  dsimp only [matrix,cell00,cell01,cell02,cell03,cell04,cell11,cell12,cell13,cell14,cell22,cell23,cell24,cell33,cell34,cell44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem delta_pos : 0 < delta matrix := by
  dsimp only [matrix,cell00,cell01,cell02,cell03,cell04,cell11,cell12,cell13,cell14,cell22,cell23,cell24,cell33,cell34,cell44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem schur_pos : 0 < schur matrix 0 0 := by
  dsimp only [matrix,cell00,cell01,cell02,cell03,cell04,cell11,cell12,cell13,cell14,cell22,cell23,cell24,cell33,cell34,cell44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem minor_pos : 0 < minor matrix := by
  dsimp only [matrix,cell00,cell01,cell02,cell03,cell04,cell11,cell12,cell13,cell14,cell22,cell23,cell24,cell33,cell34,cell44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem det_neg : determinant matrix < 0 := by
  dsimp only [matrix,cell00,cell01,cell02,cell03,cell04,cell11,cell12,cell13,cell14,cell22,cell23,cell24,cell33,cell34,cell44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,
    cons4_two,cons4_three,cons3_two]
  norm_num1



private theorem model_symmetric (i j : Fin 5) : model i j=model j i := by
  have hg : gaussianGram (leadingMatrix 6 (1522998/100000000000000)) i j=
      gaussianGram (leadingMatrix 6 (1522998/100000000000000)) j i := by
    simp only [gaussianGram]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    simp only [leadingMatrix,Nat.add_comm]
    ring
  have hl := congrFun (congrFun (loadGram_posSemidef 6).isHermitian j) i
  simp only [Matrix.conjTranspose_apply,star_trivial] at hl
  unfold model
  rw [polyModel_eq (by norm_num : (6 : ℝ) ≠ 0)]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hg,hl,
    eq_comm (a := i) (b := j)]

private theorem model_eq_matrix : model=matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact cell00.property
  · exact cell01.property
  · exact cell02.property
  · exact cell03.property
  · exact cell04.property
  · exact (model_symmetric 1 0).trans cell01.property
  · exact cell11.property
  · exact cell12.property
  · exact cell13.property
  · exact cell14.property
  · exact (model_symmetric 2 0).trans cell02.property
  · exact (model_symmetric 2 1).trans cell12.property
  · exact cell22.property
  · exact cell23.property
  · exact cell24.property
  · exact (model_symmetric 3 0).trans cell03.property
  · exact (model_symmetric 3 1).trans cell13.property
  · exact (model_symmetric 3 2).trans cell23.property
  · exact cell33.property
  · exact cell34.property
  · exact (model_symmetric 4 0).trans cell04.property
  · exact (model_symmetric 4 1).trans cell14.property
  · exact (model_symmetric 4 2).trans cell24.property
  · exact (model_symmetric 4 3).trans cell34.property
  · exact cell44.property

/-- A negative last Schur determinant lifts to a negative full quadratic direction. -/
private theorem negative_of_schur_determinant {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : ∀ i j, A i j=A j i) (hr : 0 < A 0 0) (hd : 0 < delta A)
    (hm : 0 < minor A) (ht : determinant A < 0) :
    ∃ v : Fin 5 → ℝ, v ⬝ᵥ (A *ᵥ v) < 0 := by
  let u := schur A 0 1*schur A 1 2-schur A 1 1*schur A 0 2
  let v := schur A 0 1*schur A 0 2-schur A 0 0*schur A 1 2
  let w := minor A
  let p := A 0 2*u+A 0 3*v+A 0 4*w
  let r := A 1 2*u+A 1 3*v+A 1 4*w
  let x0 := A 0 1*r-A 1 1*p
  let x1 := A 0 1*p-A 0 0*r
  have hfirst : firstCoordinate A x0 x1 (delta A*u) (delta A*v) (delta A*w)=0 := by
    dsimp only [firstCoordinate,x0,x1,p,r,delta]
    ring
  have hsecond : secondCoordinate A x1 (delta A*u) (delta A*v) (delta A*w)=0 := by
    dsimp only [secondCoordinate,x1,p,r]
    ring
  have htail : tailQuadratic A (delta A*u) (delta A*v) (delta A*w)=
      (delta A)^2*minor A*determinant A := by
    dsimp only [tailQuadratic,u,v,w,determinant,minor]
    ring
  have he := quadratic_square_completion A x0 x1 (delta A*u) (delta A*v) (delta A*w)
  rw [hfirst,hsecond,htail] at he
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,zero_add] at he
  have hn : quadratic A x0 x1 (delta A*u) (delta A*v) (delta A*w) < 0 := by
    apply neg_of_mul_neg_left _ (mul_pos hr hd).le
    rw [mul_comm,he]
    exact mul_neg_of_pos_of_neg hr
      (mul_neg_of_pos_of_neg (mul_pos (sq_pos_of_pos hd) hm) ht)
  refine ⟨![x0,x1,delta A*u,delta A*v,delta A*w],?_⟩
  rw [matrix_energy hA]
  change quadratic A x0 x1 (delta A*u) (delta A*v) (delta A*w) < 0
  exact hn

/-- The rational upper comparison at scale six has a negative quadratic direction. -/
theorem model_negative : ∃ v : Fin 5 → ℝ,
    v ⬝ᵥ (polyModel 6 (1522998/100000000000000) (-100) (1/20) *ᵥ v) < 0 := by
  change ∃ v : Fin 5 → ℝ, v ⬝ᵥ (model *ᵥ v) < 0
  apply negative_of_schur_determinant model_symmetric
  · rw [model_eq_matrix]; exact first_pos
  · rw [model_eq_matrix]; exact delta_pos
  · rw [model_eq_matrix]; exact minor_pos
  · rw [model_eq_matrix]; exact det_neg

end GaloisForLFunctions.ThetaCuspSections.QuarticSixUpper

