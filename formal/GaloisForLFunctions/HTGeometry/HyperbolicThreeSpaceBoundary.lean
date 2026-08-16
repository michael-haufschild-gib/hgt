import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic

/-!
# Hyperbolic three-space, its unimodular symmetry group, and its visual boundary

Hyperbolic three-space is realized here as the set of positive-definite Hermitian complex
`2 × 2` matrices of determinant one, with `SL(2, ℂ)` acting by `A ↦ g A gᴴ`.  The action is
transitive, by an explicit Cholesky factorization, and the stabilizer of the identity matrix is
exactly the unitary part of `SL(2, ℂ)`.  So the model is the symmetric space `SL(2, ℂ) / SU(2)`.

The visual boundary is the set of future light rays: nonzero positive-semidefinite Hermitian
matrices of vanishing determinant, taken up to positive scale.  Each such matrix is the rank-one
form `v vᴴ` of a nonzero vector, two such forms are positive multiples of each other exactly when
the vectors span the same complex line, and the symmetry action on light forms is the
tautological action on lines.  Hence the visual boundary is the complex projective line carrying
its fractional-linear action.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder LinearAlgebra.Projectivization

noncomputable section

/-! ## Real points of the complex order -/

theorem complex_nonneg_iff {z : ℂ} : (0 : ℂ) ≤ z ↔ 0 ≤ z.re ∧ z.im = 0 := by
  rw [Complex.le_def]
  simp [eq_comm]

theorem complex_pos_iff {z : ℂ} : (0 : ℂ) < z ↔ 0 < z.re ∧ z.im = 0 := by
  rw [Complex.lt_def]
  simp [eq_comm]

theorem ofReal_re_eq_self {z : ℂ} (h : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext (by simp) (by simp [h])

theorem sqrt_re_mul_self {z : ℂ} (h : (0 : ℂ) ≤ z) :
    ((Real.sqrt z.re : ℝ) : ℂ) * ((Real.sqrt z.re : ℝ) : ℂ) = z := by
  obtain ⟨hre, him⟩ := complex_nonneg_iff.mp h
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hre]
  exact ofReal_re_eq_self him

theorem sqrt_re_ne_zero {z : ℂ} (h : (0 : ℂ) ≤ z) (hz : z ≠ 0) :
    ((Real.sqrt z.re : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨hre, him⟩ := complex_nonneg_iff.mp h
  have hrepos : 0 < z.re := by
    rcases lt_or_eq_of_le hre with h' | h'
    · exact h'
    · exact absurd (Complex.ext (by simpa using h'.symm) (by simpa using him)) hz
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hrepos)

theorem star_sqrt_re {z : ℂ} : star ((Real.sqrt z.re : ℝ) : ℂ) = ((Real.sqrt z.re : ℝ) : ℂ) :=
  Complex.conj_ofReal _

theorem matrix_fin_two_eq {a b c d a' b' c' d' : ℂ} (h00 : a = a') (h01 : b = b')
    (h10 : c = c') (h11 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h00, h01, h10, h11]

/-! ## The space -/

/-- Hyperbolic three-space in the Hermitian model: unimodular positive-definite Hermitian
complex `2 × 2` matrices. -/
structure HyperbolicThreeSpace where
  /-- The underlying Hermitian matrix. -/
  mat : Matrix (Fin 2) (Fin 2) ℂ
  /-- It is positive definite. -/
  posDef : mat.PosDef
  /-- It is unimodular. -/
  det_eq_one : mat.det = 1

namespace HyperbolicThreeSpace

theorem mat_injective : Function.Injective HyperbolicThreeSpace.mat := by
  rintro ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩ h
  simp only at h
  subst h
  rfl

/-- The base point of the model. -/
def base : HyperbolicThreeSpace where
  mat := 1
  posDef := Matrix.PosDef.one
  det_eq_one := Matrix.det_one

@[simp]
theorem base_mat : base.mat = 1 := rfl

theorem specialLinearGroup_vecMul_injective (g : SpecialLinearGroup (Fin 2) ℂ) :
    Function.Injective fun v : Fin 2 → ℂ => v ᵥ* (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine Matrix.vecMul_injective_of_isUnit ?_
  rw [Matrix.isUnit_iff_isUnit_det, g.det_coe]
  exact isUnit_one

/-- The unimodular symmetry action `A ↦ g A gᴴ`. -/
instance : SMul (SpecialLinearGroup (Fin 2) ℂ) HyperbolicThreeSpace where
  smul g A :=
    { mat := (g : Matrix (Fin 2) (Fin 2) ℂ) * A.mat * (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      posDef := A.posDef.mul_mul_conjTranspose_same (specialLinearGroup_vecMul_injective g)
      det_eq_one := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, A.det_eq_one, g.det_coe]
        simp }

@[simp]
theorem smul_mat (g : SpecialLinearGroup (Fin 2) ℂ) (A : HyperbolicThreeSpace) :
    (g • A).mat = (g : Matrix (Fin 2) (Fin 2) ℂ) * A.mat * (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ :=
  rfl

instance : MulAction (SpecialLinearGroup (Fin 2) ℂ) HyperbolicThreeSpace where
  one_smul A := mat_injective (by simp)
  mul_smul g h A := mat_injective (by
    simp only [smul_mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.conjTranspose_mul]
    simp [Matrix.mul_assoc])

/-! ## Transitivity by explicit Cholesky factorization -/

/-- The positive square root of the leading diagonal entry. -/
def choleskyDiag (A : HyperbolicThreeSpace) : ℂ := ((Real.sqrt (A.mat 0 0).re : ℝ) : ℂ)

theorem diag_pos (A : HyperbolicThreeSpace) : (0 : ℂ) < A.mat 0 0 := A.posDef.diag_pos

theorem choleskyDiag_ne_zero (A : HyperbolicThreeSpace) : choleskyDiag A ≠ 0 :=
  sqrt_re_ne_zero (diag_pos A).le (ne_of_gt (diag_pos A))

theorem choleskyDiag_mul_self (A : HyperbolicThreeSpace) :
    choleskyDiag A * choleskyDiag A = A.mat 0 0 :=
  sqrt_re_mul_self (diag_pos A).le

theorem star_choleskyDiag (A : HyperbolicThreeSpace) : star (choleskyDiag A) = choleskyDiag A :=
  star_sqrt_re

theorem mat_one_zero (A : HyperbolicThreeSpace) : A.mat 1 0 = star (A.mat 0 1) := by
  have h := congrFun (congrFun A.posDef.isHermitian.eq 1) 0
  simpa [Matrix.conjTranspose_apply] using h.symm

theorem mat_det_expand (A : HyperbolicThreeSpace) :
    A.mat 0 0 * A.mat 1 1 - A.mat 0 1 * A.mat 1 0 = 1 := by
  have h := A.det_eq_one
  rwa [Matrix.det_fin_two] at h

/-- Explicit Cholesky factor of a unimodular positive-definite Hermitian `2 × 2` matrix. -/
def choleskyFactor (A : HyperbolicThreeSpace) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![choleskyDiag A, 0;
     star (A.mat 0 1) / choleskyDiag A, (choleskyDiag A)⁻¹]

theorem det_choleskyFactor (A : HyperbolicThreeSpace) : (choleskyFactor A).det = 1 := by
  rw [choleskyFactor, Matrix.det_fin_two_of, zero_mul, sub_zero,
    mul_inv_cancel₀ (choleskyDiag_ne_zero A)]

/-- The Cholesky factor as a unimodular matrix. -/
def choleskySL (A : HyperbolicThreeSpace) : SpecialLinearGroup (Fin 2) ℂ :=
  ⟨choleskyFactor A, det_choleskyFactor A⟩

theorem choleskyFactor_conjTranspose (A : HyperbolicThreeSpace) :
    (choleskyFactor A)ᴴ =
      !![choleskyDiag A, A.mat 0 1 / choleskyDiag A; 0, (choleskyDiag A)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [choleskyFactor, Matrix.conjTranspose_apply, star_choleskyDiag, star_div₀,
      star_inv₀]

theorem choleskyFactor_mul_conjTranspose (A : HyperbolicThreeSpace) :
    choleskyFactor A * (choleskyFactor A)ᴴ = A.mat := by
  have hp := choleskyDiag_ne_zero A
  have hsq := choleskyDiag_mul_self A
  have h10 := mat_one_zero A
  have hdet := mat_det_expand A
  rw [h10] at hdet
  have hA11 : A.mat 1 1 * (choleskyDiag A * choleskyDiag A)
      = star (A.mat 0 1) * A.mat 0 1 + 1 := by
    rw [hsq]
    linear_combination hdet
  have e00 : choleskyDiag A * choleskyDiag A + 0 * 0 = A.mat 0 0 := by simpa using hsq
  have e01 : choleskyDiag A * (A.mat 0 1 / choleskyDiag A) + 0 * (choleskyDiag A)⁻¹
      = A.mat 0 1 := by field_simp; ring
  have e10 : star (A.mat 0 1) / choleskyDiag A * choleskyDiag A + (choleskyDiag A)⁻¹ * 0
      = A.mat 1 0 := by rw [h10]; field_simp; ring
  have e11 : star (A.mat 0 1) / choleskyDiag A * (A.mat 0 1 / choleskyDiag A)
      + (choleskyDiag A)⁻¹ * (choleskyDiag A)⁻¹ = A.mat 1 1 := by
    field_simp
    linear_combination -hA11
  rw [choleskyFactor_conjTranspose, choleskyFactor, Matrix.mul_fin_two]
  conv_rhs => rw [Matrix.eta_fin_two A.mat]
  exact matrix_fin_two_eq e00 e01 e10 e11

/-- **Transitivity.**  The unimodular group acts transitively on hyperbolic three-space. -/
theorem exists_smul_base_eq (A : HyperbolicThreeSpace) :
    ∃ g : SpecialLinearGroup (Fin 2) ℂ, g • base = A := by
  refine ⟨choleskySL A, mat_injective ?_⟩
  show (choleskyFactor A) * (1 : Matrix (Fin 2) (Fin 2) ℂ) * (choleskyFactor A)ᴴ = A.mat
  rw [Matrix.mul_one]
  exact choleskyFactor_mul_conjTranspose A

/-- **Isotropy.**  The stabilizer of the base point is exactly the unitary part of the unimodular
group, that is the special unitary group. -/
theorem smul_base_eq_base_iff (g : SpecialLinearGroup (Fin 2) ℂ) :
    g • base = base ↔ (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  constructor
  · intro h
    have h2 := congrArg HyperbolicThreeSpace.mat h
    simpa using h2
  · intro h
    refine mat_injective ?_
    simpa using h

/-- **The symmetric-space model.**  Hyperbolic three-space is a transitive `SL(2, ℂ)`-space whose
point stabilizer at the base is the special unitary group. -/
theorem symmetricSpace_model :
    (∀ A : HyperbolicThreeSpace, ∃ g : SpecialLinearGroup (Fin 2) ℂ, g • base = A) ∧
      (∀ g : SpecialLinearGroup (Fin 2) ℂ,
        g • base = base ↔ (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :=
  ⟨exists_smul_base_eq, smul_base_eq_base_iff⟩

end HyperbolicThreeSpace

/-! ## The visual boundary -/

/-- The rank-one light form of a vector: the Hermitian matrix `v vᴴ`. -/
def lightMatrix (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec v (star v)

@[simp]
theorem lightMatrix_apply (v : Fin 2 → ℂ) (i j : Fin 2) :
    lightMatrix v i j = v i * star (v j) := rfl

theorem lightMatrix_posSemidef (v : Fin 2 → ℂ) : (lightMatrix v).PosSemidef := by
  have hEq : lightMatrix v =
      (Matrix.replicateRow (Fin 1) (star v))ᴴ * Matrix.replicateRow (Fin 1) (star v) := by
    ext i j
    simp [Matrix.mul_apply, lightMatrix, Matrix.vecMulVec_apply]
  rw [hEq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem lightMatrix_det (v : Fin 2 → ℂ) : (lightMatrix v).det = 0 := by
  rw [Matrix.det_fin_two]
  simp only [lightMatrix_apply]
  ring

theorem exists_ne_zero_of_ne_zero {v : Fin 2 → ℂ} (hv : v ≠ 0) : ∃ i, v i ≠ 0 := by
  by_contra h
  exact hv (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)

theorem lightMatrix_ne_zero {v : Fin 2 → ℂ} (hv : v ≠ 0) : lightMatrix v ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hv
  intro hzero
  have h := congrFun (congrFun hzero i) i
  simp only [lightMatrix_apply, Matrix.zero_apply] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact hi h'
  · exact hi (star_eq_zero.mp h')

/-- The symmetry action on light forms is the tautological action on vectors. -/
theorem lightMatrix_mulVec (g : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    lightMatrix (g *ᵥ v) = g * lightMatrix v * gᴴ := by
  ext i j
  simp only [lightMatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp only [star_add, star_mul]
  ring

/-- **Every boundary point is a light form.**  A nonzero positive-semidefinite Hermitian `2 × 2`
matrix of vanishing determinant is the rank-one form of a nonzero vector. -/
theorem exists_eq_lightMatrix {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef)
    (hdet : A.det = 0) (hne : A ≠ 0) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ A = lightMatrix v := by
  have h10 : A 1 0 = star (A 0 1) := by
    have h := congrFun (congrFun hA.isHermitian.eq 1) 0
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 0 := by
    rwa [Matrix.det_fin_two] at hdet
  rw [h10] at hdet'
  by_cases h00 : A 0 0 = 0
  · have hb : A 0 1 = 0 := by
      have hz : A 0 1 * star (A 0 1) = 0 := by
        linear_combination -hdet' + A 1 1 * h00
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact star_eq_zero.mp h
    have h11nonneg : (0 : ℂ) ≤ A 1 1 := hA.diag_nonneg
    have h11ne : A 1 1 ≠ 0 := by
      intro hz
      refine hne ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, hb, hz, h10]
    refine ⟨![0, ((Real.sqrt (A 1 1).re : ℝ) : ℂ)], ?_, ?_⟩
    · intro hzero
      exact sqrt_re_ne_zero h11nonneg h11ne (by simpa using congrFun hzero 1)
    · have hsq := sqrt_re_mul_self h11nonneg
      have hlm : lightMatrix ![0, ((Real.sqrt (A 1 1).re : ℝ) : ℂ)]
          = !![0, 0; 0, A 1 1] := by
        conv_lhs => rw [Matrix.eta_fin_two (lightMatrix ![0, ((Real.sqrt (A 1 1).re : ℝ) : ℂ)])]
        simp [star_sqrt_re, hsq]
      rw [hlm]
      conv_lhs => rw [Matrix.eta_fin_two A]
      exact matrix_fin_two_eq h00 hb (by rw [h10, hb, star_zero]) rfl
  · have h00nonneg : (0 : ℂ) ≤ A 0 0 := hA.diag_nonneg
    have hsne := sqrt_re_ne_zero h00nonneg h00
    have hsq := sqrt_re_mul_self h00nonneg
    refine ⟨![((Real.sqrt (A 0 0).re : ℝ) : ℂ),
      star (A 0 1) / ((Real.sqrt (A 0 0).re : ℝ) : ℂ)], ?_, ?_⟩
    · intro hzero
      exact hsne (by simpa using congrFun hzero 0)
    · have hA11 : A 1 1 * (((Real.sqrt (A 0 0).re : ℝ) : ℂ) *
          ((Real.sqrt (A 0 0).re : ℝ) : ℂ)) = A 0 1 * star (A 0 1) := by
        rw [hsq]
        linear_combination hdet'
      have hlm : lightMatrix ![((Real.sqrt (A 0 0).re : ℝ) : ℂ),
            star (A 0 1) / ((Real.sqrt (A 0 0).re : ℝ) : ℂ)]
          = !![A 0 0, A 0 1; star (A 0 1), A 1 1] := by
        conv_lhs => rw [Matrix.eta_fin_two (lightMatrix
          ![((Real.sqrt (A 0 0).re : ℝ) : ℂ), star (A 0 1) / ((Real.sqrt (A 0 0).re : ℝ) : ℂ)])]
        refine matrix_fin_two_eq ?_ ?_ ?_ ?_
        · simpa [star_sqrt_re] using hsq
        · simp only [lightMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            star_div₀, star_star, star_sqrt_re]
          field_simp
        · simp only [lightMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            star_sqrt_re]
          field_simp
        · simp only [lightMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            star_div₀, star_star, star_sqrt_re]
          field_simp
          linear_combination -hA11
      rw [hlm]
      conv_lhs => rw [Matrix.eta_fin_two A]
      exact matrix_fin_two_eq rfl rfl h10 rfl

/-- **The visual boundary is the projective line.**  Two light forms are positive multiples of
each other exactly when their vectors span the same complex line. -/
theorem lightMatrix_smul_iff {v w : Fin 2 → ℂ} (hv : v ≠ 0) (hw : w ≠ 0) :
    (∃ t : ℝ, 0 < t ∧ lightMatrix v = (t : ℂ) • lightMatrix w) ↔
      Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw := by
  constructor
  · rintro ⟨t, ht, hEq⟩
    obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hv
    have hvi : star (v i) ≠ 0 := star_ne_zero.mpr hi
    refine (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr
      ⟨(t : ℂ) * star (w i) / star (v i), ?_⟩
    funext j
    have hij := congrFun (congrFun hEq i) j
    simp only [lightMatrix_apply, Matrix.smul_apply, smul_eq_mul] at hij
    have hstar : star (v i) * v j = (t : ℂ) * (star (w i) * w j) := by
      have h2 := congrArg star hij
      simp only [star_mul, Complex.star_def, Complex.conj_conj, Complex.conj_ofReal] at h2
      linear_combination h2
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination -hstar
  · intro h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mp h
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hv (by rw [← ha]; simp)
    refine ⟨Complex.normSq a, Complex.normSq_pos.mpr ha0, ?_⟩
    ext i j
    have hvi : v i = a * w i := by rw [← ha]; simp
    have hvj : v j = a * w j := by rw [← ha]; simp
    simp only [lightMatrix_apply, Matrix.smul_apply, smul_eq_mul, hvi, hvj]
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [star_mul, Complex.star_def]
    ring

end

end GaloisForLFunctions.HTGeometry
