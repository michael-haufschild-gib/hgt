import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Star.Real

open Matrix

/-!
# The generalized upper half-space `h³ = GL₃(ℝ)/(O(3)·ℝ^×)`

A point is given by Iwasawa coordinates `z = x·y`,
`x = [[1, x₂, x₃], [0, 1, x₁], [0, 0, 1]]`, `y = diag(y₁y₂, y₁, 1)`, `y₁, y₂ > 0`, i.e. by the
upper-triangular matrix `mat z = [[y₁y₂, y₁x₂, x₃], [0, y₁, x₁], [0, 0, 1]]`.

The coset `z·O(3)·ℝ^×` is determined by the positive definite Gram matrix `gram z = z zᵀ` up to
scaling. Conversely every positive definite `S` has a unique Iwasawa point `ofPD S` with
`gram (ofPD S) = S / S₂₂` (`gram_ofPD`, `ofPD_gram`); the coordinates are rational functions of the
normalised entries, and positivity of `y₁², (y₁y₂)²` comes from evaluating the quadratic form on
explicit vectors (`qa_pos`, `qe_pos`).

`GL₃(ℝ)` acts by `g • z = ofMat (g · gram z · gᵀ)`, and the action laws follow from scale invariance
(`ofMat_smul`). The recognition principle `smul_eq_of_mul` (`g·z = r·w·k`, `k` orthogonal ⇒ `g • z = w`)
gives the unipotent action as a Heisenberg translation (`nGL_smul`) and the diagonal action as a
dilation (`dGL_smul`). `SL₃(ℤ)` acts through `slToGL`.
-/

namespace GaloisForLFunctions.RHTower.GL3

/-- A point of `h³` in Iwasawa coordinates `(x₁, x₂, x₃, y₁, y₂)`, `y₁, y₂ > 0`. -/
@[ext] structure H3 where
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  y1 : ℝ
  y2 : ℝ
  y1_pos : 0 < y1
  y2_pos : 0 < y2

namespace H3

/-- The Iwasawa matrix `x·y`. -/
def mat (z : H3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![z.y1 * z.y2, z.y1 * z.x2, z.x3; 0, z.y1, z.x1; 0, 0, 1]

/-- The Gram matrix `z zᵀ`, a complete invariant of the coset `z·O(3)`. -/
def gram (z : H3) : Matrix (Fin 3) (Fin 3) ℝ := z.mat * z.matᵀ

theorem gram_apply (z : H3) :
    z.gram = !![(z.y1 * z.y2) ^ 2 + (z.y1 * z.x2) ^ 2 + z.x3 ^ 2, z.y1 ^ 2 * z.x2 + z.x3 * z.x1, z.x3;
      z.y1 ^ 2 * z.x2 + z.x3 * z.x1, z.y1 ^ 2 + z.x1 ^ 2, z.x1; z.x3, z.x1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram, mat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_mat (z : H3) : z.mat.det = z.y1 ^ 2 * z.y2 := by
  simp [mat, Matrix.det_fin_three]; ring

theorem isUnit_mat (z : H3) : IsUnit z.mat := by
  rw [Matrix.isUnit_iff_isUnit_det, det_mat]
  exact (mul_pos (pow_pos z.y1_pos 2) z.y2_pos).ne'.isUnit

theorem posDef_gram (z : H3) : z.gram.PosDef := by
  have h := (PosDef.one (n := Fin 3) (R := ℝ)).mul_mul_conjTranspose_same
    (vecMul_injective_of_isUnit z.isUnit_mat)
  simpa [gram, conjTranspose_eq_transpose_of_trivial] using h

/-! ### Iwasawa coordinates of a positive definite matrix -/

section Recon
variable (S : Matrix (Fin 3) (Fin 3) ℝ)

/-- Normalised entries `T = S / S₂₂`. -/
noncomputable def nt (i j : Fin 3) : ℝ := S i j / S 2 2

/-- `y₁²` of the Iwasawa point of `S`. -/
noncomputable def qa : ℝ := nt S 1 1 - nt S 1 2 ^ 2
/-- `y₁² x₂`. -/
noncomputable def qb : ℝ := nt S 0 1 - nt S 1 2 * nt S 0 2
/-- `(y₁ y₂)²`. -/
noncomputable def qe : ℝ := nt S 0 0 - nt S 0 2 ^ 2 - qb S ^ 2 / qa S

variable {S}

theorem symm_of_posDef (hS : S.PosDef) (i j : Fin 3) : S j i = S i j := by
  have := hS.isHermitian.apply i j
  simpa using this

theorem s22_pos (hS : S.PosDef) : 0 < S 2 2 := hS.diag_pos

theorem qa_pos (hS : S.PosDef) : 0 < qa S := by
  have hc := s22_pos hS
  have h := hS.dotProduct_mulVec_pos (x := ![0, 1, -nt S 1 2]) (by
    intro h; have := congrFun h 1; simp at this)
  have e : star ![0, 1, -nt S 1 2] ⬝ᵥ S *ᵥ ![0, 1, -nt S 1 2] = S 2 2 * qa S := by
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [symm_of_posDef hS 1 2]
    simp only [qa, nt]
    field_simp
    ring
  rw [e] at h
  exact pos_of_mul_pos_right h hc.le

theorem qe_pos (hS : S.PosDef) : 0 < qe S := by
  have hc := s22_pos hS
  have ha := qa_pos hS
  set x2 := qb S / qa S with hx2
  have h := hS.dotProduct_mulVec_pos (x := ![1, -x2, nt S 1 2 * x2 - nt S 0 2]) (by
    intro h; have := congrFun h 0; simp at this)
  have e : star ![1, -x2, nt S 1 2 * x2 - nt S 0 2] ⬝ᵥ S *ᵥ ![1, -x2, nt S 1 2 * x2 - nt S 0 2] =
      S 2 2 * qe S := by
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [symm_of_posDef hS 1 2, symm_of_posDef hS 0 1, symm_of_posDef hS 0 2]
    rw [hx2]
    simp only [qe, qa, qb, nt]
    have hD : S 2 2 * S 1 1 - S 1 2 ^ 2 ≠ 0 := by
      have : qa S = (S 2 2 * S 1 1 - S 1 2 ^ 2) / S 2 2 ^ 2 := by
        simp only [qa, nt]; field_simp
      intro h0; rw [h0, zero_div] at this; exact ha.ne' this
    field_simp
    ring
  rw [e] at h
  exact pos_of_mul_pos_right h hc.le

/-- The Iwasawa point of a positive definite matrix `S`, normalised by `S₂₂`. -/
noncomputable def ofPD (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosDef) : H3 where
  x1 := nt S 1 2
  x2 := qb S / qa S
  x3 := nt S 0 2
  y1 := √(qa S)
  y2 := √(qe S) / √(qa S)
  y1_pos := Real.sqrt_pos.2 (qa_pos hS)
  y2_pos := div_pos (Real.sqrt_pos.2 (qe_pos hS)) (Real.sqrt_pos.2 (qa_pos hS))

theorem ofPD_y1_sq (hS : S.PosDef) : (ofPD S hS).y1 ^ 2 = qa S :=
  Real.sq_sqrt (qa_pos hS).le

theorem ofPD_y1_mul_y2 (hS : S.PosDef) : (ofPD S hS).y1 * (ofPD S hS).y2 = √(qe S) := by
  simp only [ofPD]
  exact mul_div_cancel₀ _ (Real.sqrt_pos.2 (qa_pos hS)).ne'

theorem nt_symm (hS : S.PosDef) (i j : Fin 3) : nt S j i = nt S i j := by
  simp only [nt, symm_of_posDef hS i j]

theorem gram_ofPD (hS : S.PosDef) : (ofPD S hS).gram = (S 2 2)⁻¹ • S := by
  have hc := (s22_pos hS).ne'
  have ha := (qa_pos hS).ne'
  have h1 := ofPD_y1_sq hS
  have h2 : ((ofPD S hS).y1 * (ofPD S hS).y2) ^ 2 = qe S := by
    rw [ofPD_y1_mul_y2, Real.sq_sqrt (qe_pos hS).le]
  have hr : ∀ i j, ((S 2 2)⁻¹ • S) i j = nt S i j := by
    intro i j; simp only [Matrix.smul_apply, smul_eq_mul, nt]; rw [inv_mul_eq_div]
  have h22 : nt S 2 2 = 1 := by simp only [nt]; exact div_self hc
  have hx1 : (ofPD S hS).x1 = nt S 1 2 := rfl
  have hx2 : (ofPD S hS).x2 = qb S / qa S := rfl
  have hx3 : (ofPD S hS).x3 = nt S 0 2 := rfl
  rw [gram_apply]
  ext i j
  rw [hr]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, of_apply, cons_val',
      cons_val_zero, cons_val_one, cons_val_two, empty_val', cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Nat.succ_eq_add_one, Nat.reduceAdd]
  · rw [h2, mul_pow, h1, hx2, hx3]; simp only [qe]; field_simp; ring
  · rw [h1, hx1, hx2, hx3]; simp only [qb]; field_simp; ring
  · rw [hx3]
  · rw [h1, hx1, hx2, hx3, nt_symm hS 0 1]; simp only [qb]; field_simp; ring
  · rw [h1, hx1]; simp only [qa]; ring
  · rw [hx1]
  · simp only [Matrix.vecHead]; rw [hx3, nt_symm hS 0 2]
  · simp only [Matrix.vecHead]; rw [hx1, nt_symm hS 1 2]
  · simp only [Matrix.vecHead]; rw [h22]

theorem ofPD_gram (z : H3) : ofPD z.gram z.posDef_gram = z := by
  have g22 : z.gram 2 2 = 1 := by rw [gram_apply]; simp
  have hnt : ∀ i j, nt z.gram i j = z.gram i j := by intro i j; simp [nt, g22]
  have hqa : qa z.gram = z.y1 ^ 2 := by
    simp only [qa, hnt]; rw [gram_apply]; simp
  have hqb : qb z.gram = z.y1 ^ 2 * z.x2 := by
    simp only [qb, hnt]; rw [gram_apply]; simp; ring
  have hy1 := z.y1_pos
  have hqe : qe z.gram = (z.y1 * z.y2) ^ 2 := by
    simp only [qe, hnt, hqb, hqa]; rw [gram_apply]; simp; field_simp; ring
  ext
  · simp only [ofPD, hnt]; rw [gram_apply]; simp
  · simp only [ofPD, hqb, hqa]; field_simp
  · simp only [ofPD, hnt]; rw [gram_apply]; simp
  · simp only [ofPD, hqa]; exact Real.sqrt_sq hy1.le
  · simp only [ofPD, hqa, hqe]
    rw [Real.sqrt_sq (mul_pos hy1 z.y2_pos).le, Real.sqrt_sq hy1.le]
    field_simp

theorem nt_smul {r : ℝ} (hr : r ≠ 0) (i j : Fin 3) : nt (r • S) i j = nt S i j := by
  simp only [nt, Matrix.smul_apply, smul_eq_mul]; rw [mul_div_mul_left _ _ hr]

theorem ofPD_smul (hS : S.PosDef) {r : ℝ} (hr : 0 < r) :
    ofPD (r • S) (hS.smul hr) = ofPD S hS := by
  have h := nt_smul (S := S) hr.ne'
  have ha : qa (r • S) = qa S := by simp only [qa, h]
  have hb : qb (r • S) = qb S := by simp only [qb, h]
  have he : qe (r • S) = qe S := by simp only [qe, h, ha, hb]
  ext <;> simp only [ofPD, h, ha, hb, he]

/-- Total Iwasawa point: `ofPD` on positive definite matrices, a base point otherwise. -/
noncomputable def ofMat (S : Matrix (Fin 3) (Fin 3) ℝ) : H3 := by
  classical
  exact if h : S.PosDef then ofPD S h else ⟨0, 0, 0, 1, 1, one_pos, one_pos⟩

theorem ofMat_eq (hS : S.PosDef) : ofMat S = ofPD S hS := by
  classical
  simp only [ofMat, dif_pos hS]

theorem ofMat_smul (hS : S.PosDef) {r : ℝ} (hr : 0 < r) : ofMat (r • S) = ofMat S := by
  rw [ofMat_eq hS, ofMat_eq (hS.smul hr), ofPD_smul hS hr]

theorem ofMat_gram (z : H3) : ofMat z.gram = z := by
  rw [ofMat_eq z.posDef_gram, ofPD_gram]

end Recon

/-! ### The action of `GL₃(ℝ)` -/

theorem posDef_conj (g : GL (Fin 3) ℝ) (z : H3) :
    ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ).PosDef := by
  have := (IsUnit.posDef_star_right_conjugate_iff (x := z.gram) (Units.isUnit g)).2 z.posDef_gram
  simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

theorem gram_ofMat_of_posDef {S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.PosDef) :
    (ofMat S).gram = (S 2 2)⁻¹ • S := by
  rw [ofMat_eq hS, gram_ofPD]

/-- `GL₃(ℝ)` acts on `h³` by `z ↦ gz` modulo `O(3)·ℝ^×`, computed on Gram matrices. -/
noncomputable instance : MulAction (GL (Fin 3) ℝ) H3 where
  smul g z := ofMat ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ)
  one_smul z := by
    show ofMat (((1 : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * _) = z
    simp [ofMat_gram]
  mul_smul g h z := by
    show ofMat _ = ofMat (_ * (ofMat _).gram * _)
    set G := z.gram
    set M := (h : Matrix (Fin 3) (Fin 3) ℝ) * G * (h : Matrix (Fin 3) (Fin 3) ℝ)ᵀ
    have hM : M.PosDef := posDef_conj h z
    rw [gram_ofMat_of_posDef hM, Matrix.mul_smul, Matrix.smul_mul]
    have hc : 0 < (M 2 2)⁻¹ := inv_pos.2 hM.diag_pos
    have e : (g : Matrix (Fin 3) (Fin 3) ℝ) * M * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
        ((g * h : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) * G *
          ((g * h : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
      simp only [M, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, ofMat_smul (posDef_conj (g * h) z) hc]

theorem smul_def (g : GL (Fin 3) ℝ) (z : H3) :
    g • z = ofMat ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) := rfl

/-- **Recognition principle.** If `g·z = r·w·k` with `k` orthogonal and `r ≠ 0`, then `g • z = w`. -/
theorem smul_eq_of_mul {g : GL (Fin 3) ℝ} {z w : H3} {k : Matrix (Fin 3) (Fin 3) ℝ}
    (hk : k * kᵀ = 1) {r : ℝ} (hr : r ≠ 0)
    (h : (g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat = r • (w.mat * k)) : g • z = w := by
  rw [smul_def]
  have e : (g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
      (r ^ 2) • w.gram := by
    have : (g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
        ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) * ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat)ᵀ := by
      simp only [gram, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, h, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.transpose_mul, gram]
    congr 1
    · ring
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc k, hk, Matrix.one_mul]
  rw [e, ofMat_smul w.posDef_gram (pow_pos (abs_pos.2 hr) 2 |>.trans_eq (by rw [sq_abs])),
    ofMat_gram]

/-! ### Unipotent and diagonal elements -/

/-- The upper unipotent matrix `n(a₁,a₂,a₃)`. -/
def nmat (a1 a2 a3 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, a2, a3; 0, 1, a1; 0, 0, 1]

theorem nmat_mul (a1 a2 a3 b1 b2 b3 : ℝ) :
    nmat a1 a2 a3 * nmat b1 b2 b3 = nmat (a1 + b1) (a2 + b2) (a3 + b3 + a2 * b1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nmat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem nmat_zero : nmat 0 0 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nmat]

/-- `n(a₁,a₂,a₃)` as an element of `GL₃(ℝ)`. -/
noncomputable def nGL (a1 a2 a3 : ℝ) : GL (Fin 3) ℝ where
  val := nmat a1 a2 a3
  inv := nmat (-a1) (-a2) (a2 * a1 - a3)
  val_inv := by rw [nmat_mul, ← nmat_zero]; congr 1 <;> ring
  inv_val := by rw [nmat_mul, ← nmat_zero]; congr 1 <;> ring

/-- The Heisenberg translate of `z` by `(a₁,a₂,a₃)`. -/
def translate (z : H3) (a1 a2 a3 : ℝ) : H3 :=
  ⟨z.x1 + a1, z.x2 + a2, z.x3 + a3 + a2 * z.x1, z.y1, z.y2, z.y1_pos, z.y2_pos⟩

/-- **Unipotent action.** `n(a₁,a₂,a₃)` acts on Iwasawa coordinates as a Heisenberg translation. -/
theorem nGL_smul (a1 a2 a3 : ℝ) (z : H3) : nGL a1 a2 a3 • z = z.translate a1 a2 a3 := by
  apply smul_eq_of_mul (k := 1) (by simp) one_ne_zero
  rw [one_smul, Matrix.mul_one]
  show nmat a1 a2 a3 * z.mat = (z.translate a1 a2 a3).mat
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [nmat, mat, translate, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- `diag(a,b,1)` as an element of `GL₃(ℝ)`. -/
noncomputable def dGL {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : GL (Fin 3) ℝ where
  val := !![a, 0, 0; 0, b, 0; 0, 0, 1]
  inv := !![a⁻¹, 0, 0; 0, b⁻¹, 0; 0, 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, ha, hb]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, ha, hb]

/-- The diagonally rescaled point. -/
noncomputable def dilate (z : H3) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : H3 :=
  ⟨b * z.x1, a / b * z.x2, a * z.x3, b * z.y1, a / b * z.y2, mul_pos hb z.y1_pos,
    mul_pos (div_pos ha hb) z.y2_pos⟩

/-- **Diagonal action.** `diag(a,b,1)` (`a, b > 0`) rescales the Iwasawa coordinates. -/
theorem dGL_smul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : H3) :
    dGL ha.ne' hb.ne' • z = z.dilate ha hb := by
  apply smul_eq_of_mul (k := 1) (by simp) one_ne_zero
  rw [one_smul, Matrix.mul_one]
  show !![a, 0, 0; 0, b, 0; 0, 0, 1] * z.mat = (z.dilate ha hb).mat
  have hb' := hb.ne'
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [mat, dilate, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

/-! ### The arithmetic subgroup -/

/-- The embedding `SL₃(ℤ) → GL₃(ℝ)`. -/
noncomputable def slToGL : Matrix.SpecialLinearGroup (Fin 3) ℤ →* GL (Fin 3) ℝ :=
  Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))

noncomputable instance : MulAction (Matrix.SpecialLinearGroup (Fin 3) ℤ) H3 :=
  MulAction.compHom H3 slToGL

theorem sl_smul_def (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) : γ • z = slToGL γ • z := rfl

end H3
end GaloisForLFunctions.RHTower.GL3
