import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import GaloisForLFunctions.HTGeometry.HermitianLocalSpectralObserverLaw
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Escaping nonlocal chiral polarizations of finite source matrices

Every finite complex source matrix `C` has a coefficient-faithful Hermitian chiral dilation

`D(C) = [[0, C], [Cᴴ, 0]]`.

The positive root used below is not a scalar gauge.  It adds the global row and column Grams
`C Cᴴ` and `Cᴴ C` to an asymmetric chiral floor whose positive-chirality coefficient is `k+1`.
Conjugating `D(C)` by this root gives a generally non-Hermitian operator with an exact positive
metric-adjoint relation.  Similarity preserves its ordinary characteristic determinant, so every
finite divisor remains real.

This construction is source-defined and makes the polarization genuinely nonlocal.  It does not
identify the resulting singular-value divisor with any preassigned source divisor; that separate
fidelity problem is addressed by route-specific modules.
-/

open Complex Matrix Polynomial
open scoped ComplexOrder Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Coefficient-faithful Hermitian chiral dilation of a finite source matrix. -/
def sourceHermitianDilation (C : Matrix m m ℂ) : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  Matrix.fromBlocks 0 C Cᴴ 0

omit [Fintype m] [DecidableEq m] in
@[simp] theorem sourceHermitianDilation_inl_inr (C : Matrix m m ℂ) (i j : m) :
    sourceHermitianDilation C (Sum.inl i) (Sum.inr j) = C i j := rfl

omit [Fintype m] [DecidableEq m] in
/-- Chiral dilation is Hermitian without any condition on the source matrix. -/
theorem sourceHermitianDilation_isHermitian (C : Matrix m m ℂ) :
    (sourceHermitianDilation C).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [sourceHermitianDilation, Matrix.fromBlocks_conjTranspose]

omit [DecidableEq m] in
/-- Squaring the dilation produces the two global source Gram matrices. -/
theorem sourceHermitianDilation_sq_eq (C : Matrix m m ℂ) :
    sourceHermitianDilation C * sourceHermitianDilation C =
      Matrix.fromBlocks (C * Cᴴ) 0 0 (Cᴴ * C) := by
  ext i j
  cases i <;> cases j <;> simp [sourceHermitianDilation, Matrix.mul_apply]

omit [DecidableEq m] in
/-- The dilation square is positive semidefinite. -/
theorem sourceHermitianDilation_sq_posSemidef (C : Matrix m m ℂ) :
    (sourceHermitianDilation C * sourceHermitianDilation C).PosSemidef := by
  simpa only [(sourceHermitianDilation_isHermitian C).eq] using
    (Matrix.posSemidef_conjTranspose_mul_self (sourceHermitianDilation C))

/-- Ordinary Fredholm-coordinate divisor of the Hermitian source dilation. -/
def sourceHermitianDilationDivisor (C : Matrix m m ℂ) (z : ℂ) : ℂ :=
  ((1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) - z • sourceHermitianDilation C).det

/-- Exact divisor classification: chiral Hermitianization replaces the source eigenvalue divisor
by the squared singular-value divisor.  This is the precise cost of unconditional positivity. -/
theorem sourceHermitianDilationDivisor_eq_gramDet (C : Matrix m m ℂ) (z : ℂ) :
    sourceHermitianDilationDivisor C z =
      ((1 : Matrix m m ℂ) - (z * z) • (Cᴴ * C)).det := by
  have hblock :
      (1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) - z • sourceHermitianDilation C =
        Matrix.fromBlocks 1 (-z • C) (-z • Cᴴ) 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [sourceHermitianDilation, Matrix.one_apply]
  rw [sourceHermitianDilationDivisor, hblock, Matrix.det_fromBlocks_one₁₁]
  congr 1
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ring_nf

/-- Asymmetric chiral floor.  Its positive-chirality coefficient grows as `k+1`, while the
negative-chirality coefficient stays at one. -/
def sourceChiralFloor (k : ℕ) : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  Matrix.diagonal
    (Sum.elim (fun _ : m => (((k : ℝ) + 1 : ℝ) : ℂ)) (fun _ : m => 1))

omit [Fintype m] in
theorem sourceChiralFloor_posDef (k : ℕ) : (sourceChiralFloor (m := m) k).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  cases i with
  | inl i =>
      simp only [Sum.elim_inl]
      exact_mod_cast (show (0 : ℝ) < (k : ℝ) + 1 by positivity)
  | inr i => norm_num

/-- Positive, escaping, nonlocal polarization root: chiral floor plus full source Gram. -/
def sourceEscapingNonlocalRoot (k : ℕ) (C : Matrix m m ℂ) :
    Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  sourceChiralFloor k + sourceHermitianDilation C * sourceHermitianDilation C

/-- Exact nonlocal block content of the escaping root. -/
theorem sourceEscapingNonlocalRoot_eq_sourceGramBlocks (k : ℕ) (C : Matrix m m ℂ) :
    sourceEscapingNonlocalRoot k C = sourceChiralFloor k +
      Matrix.fromBlocks (C * Cᴴ) 0 0 (Cᴴ * C) := by
  rw [sourceEscapingNonlocalRoot, sourceHermitianDilation_sq_eq]

/-- Source-Gram excess above the escaping chiral floor is positive semidefinite. -/
theorem sourceEscapingNonlocalRoot_sub_chiralFloor_posSemidef
    (k : ℕ) (C : Matrix m m ℂ) :
    (sourceEscapingNonlocalRoot k C - sourceChiralFloor k).PosSemidef := by
  simpa [sourceEscapingNonlocalRoot] using sourceHermitianDilation_sq_posSemidef C

/-- Escaping nonlocal root is strictly positive. -/
theorem sourceEscapingNonlocalRoot_posDef (k : ℕ) (C : Matrix m m ℂ) :
    (sourceEscapingNonlocalRoot k C).PosDef :=
  (sourceChiralFloor_posDef k).add_posSemidef
    (sourceHermitianDilation_sq_posSemidef C)

theorem sourceEscapingNonlocalRoot_isHermitian (k : ℕ) (C : Matrix m m ℂ) :
    (sourceEscapingNonlocalRoot k C).IsHermitian :=
  (sourceEscapingNonlocalRoot_posDef k C).isHermitian

/-- Non-Hermitian chiral operator obtained by positive source-Gram similarity. -/
def sourceEscapingChiralOperator (k : ℕ) (C : Matrix m m ℂ) :
    Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  (sourceEscapingNonlocalRoot k C)⁻¹ * sourceHermitianDilation C *
    sourceEscapingNonlocalRoot k C

/-- Positive metric carried by the escaping root. -/
def sourceEscapingNonlocalMetric (k : ℕ) (C : Matrix m m ℂ) :
    Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  sourceEscapingNonlocalRoot k C * sourceEscapingNonlocalRoot k C

/-- Escaping nonlocal metric remains strictly positive. -/
theorem sourceEscapingNonlocalMetric_posDef (k : ℕ) (C : Matrix m m ℂ) :
    (sourceEscapingNonlocalMetric k C).PosDef := by
  unfold sourceEscapingNonlocalMetric
  have h := Matrix.PosDef.one.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (sourceEscapingNonlocalRoot_posDef k C).isUnit)
  simpa only [Matrix.mul_one, (sourceEscapingNonlocalRoot_isHermitian k C).eq] using h

/-- Exact positive metric-adjoint relation for the escaped chiral operator. -/
theorem sourceEscapingChiralOperator_metricAdjoint (k : ℕ) (C : Matrix m m ℂ) :
    sourceEscapingNonlocalMetric k C * sourceEscapingChiralOperator k C =
      (sourceEscapingChiralOperator k C)ᴴ * sourceEscapingNonlocalMetric k C := by
  let Q := sourceEscapingNonlocalRoot k C
  have hQunit : IsUnit Q := (sourceEscapingNonlocalRoot_posDef k C).isUnit
  letI : Invertible Q := hQunit.nonempty_invertible.some
  have hQ : Qᴴ = Q := (sourceEscapingNonlocalRoot_isHermitian k C).eq
  have hQi : Q⁻¹ᴴ = Q⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hQ]
  unfold sourceEscapingNonlocalMetric sourceEscapingChiralOperator
  change Q * Q * (Q⁻¹ * sourceHermitianDilation C * Q) =
    (Q⁻¹ * sourceHermitianDilation C * Q)ᴴ * (Q * Q)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ, hQi,
    (sourceHermitianDilation_isHermitian C).eq]
  simp [Matrix.mul_assoc]

/-- Positive similarity leaves the ordinary source-dilation divisor exactly unchanged. -/
theorem sourceEscapingChiralOperator_divisor_eq
    (k : ℕ) (C : Matrix m m ℂ) (z : ℂ) :
    ((1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) -
      z • sourceEscapingChiralOperator k C).det =
        sourceHermitianDilationDivisor C z := by
  let Q := sourceEscapingNonlocalRoot k C
  have hQunit : IsUnit Q := (sourceEscapingNonlocalRoot_posDef k C).isUnit
  letI : Invertible Q := hQunit.nonempty_invertible.some
  have hleft : Q⁻¹ * Q = 1 := Matrix.inv_mul_of_invertible Q
  have hmatrix :
      (1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) -
          z • sourceEscapingChiralOperator k C =
        Q⁻¹ * ((1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) -
          z • sourceHermitianDilation C) * Q := by
    unfold sourceEscapingChiralOperator
    change 1 - z • (Q⁻¹ * sourceHermitianDilation C * Q) =
      Q⁻¹ * (1 - z • sourceHermitianDilation C) * Q
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [hleft]
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul, sourceHermitianDilationDivisor]
  calc
    Q⁻¹.det * (1 - z • sourceHermitianDilation C).det * Q.det =
        (1 - z • sourceHermitianDilation C).det * (Q⁻¹.det * Q.det) := by ring
    _ = (1 - z • sourceHermitianDilation C).det * (Q⁻¹ * Q).det := by
      rw [Matrix.det_mul]
    _ = (1 - z • sourceHermitianDilation C).det := by
      rw [hleft, Matrix.det_one, mul_one]

omit [DecidableEq m] in
theorem trace_sourceHermitianDilation (C : Matrix m m ℂ) :
    (sourceHermitianDilation C).trace = 0 := by
  simp [Matrix.trace, sourceHermitianDilation]

/-- Dilation divisor is a finite regularized determinant because its trace vanishes. -/
theorem sourceHermitianDilationDivisor_eq_finiteDet2 (C : Matrix m m ℂ) :
    sourceHermitianDilationDivisor C = finiteDet2 (-sourceHermitianDilation C) := by
  funext z
  simp [sourceHermitianDilationDivisor, finiteDet2, trace_sourceHermitianDilation,
    sub_eq_add_neg]

theorem differentiable_sourceHermitianDilationDivisor (C : Matrix m m ℂ) :
    Differentiable ℂ (sourceHermitianDilationDivisor C) := by
  rw [sourceHermitianDilationDivisor_eq_finiteDet2]
  exact differentiable_finiteDet2 _

/-- Every zero of the ordinary Fredholm-coordinate dilation divisor is real. -/
theorem sourceHermitianDilationDivisor_zero_im_eq_zero
    (C : Matrix m m ℂ) {z : ℂ} (hz : sourceHermitianDilationDivisor C z = 0) :
    z.im = 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp [sourceHermitianDilationDivisor] at hz
  have hmatrix :
      (Matrix.scalar (m ⊕ m) z⁻¹ - sourceHermitianDilation C) =
        z⁻¹ • ((1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) -
          z • sourceHermitianDilation C) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply]
      field_simp
    · simp [Matrix.scalar_apply, hij, hz0]
  have hchar : (sourceHermitianDilation C).charpoly.eval z⁻¹ = 0 := by
    change ((1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) -
      z • sourceHermitianDilation C).det = 0 at hz
    rw [Matrix.eval_charpoly, hmatrix, Matrix.det_smul, hz]
    simp
  have hrelation :
      matrixCharpolyRelation (sourceHermitianDilation C, z⁻¹) = 0 := by
    simpa [matrixCharpolyRelation, Matrix.eval_charpoly] using hchar
  have hinvIm : z⁻¹.im = 0 :=
    matrixCharpolyRelation_im_eq_zero_of_isHermitian
      (sourceHermitianDilation C) (sourceHermitianDilation_isHermitian C) z⁻¹ hrelation
  rw [Complex.inv_im] at hinvIm
  have hnorm : Complex.normSq z ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hz0)
  exact neg_eq_zero.mp (div_eq_zero_iff.mp hinvIm |>.resolve_right hnorm)

/-- The escaped non-Hermitian representative has the same real finite divisor. -/
theorem sourceEscapingChiralOperator_divisor_zero_im_eq_zero
    (k : ℕ) (C : Matrix m m ℂ) {z : ℂ}
    (hz : ((1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) -
      z • sourceEscapingChiralOperator k C).det = 0) : z.im = 0 := by
  apply sourceHermitianDilationDivisor_zero_im_eq_zero C
  rwa [← sourceEscapingChiralOperator_divisor_eq k C z]

end

end GaloisForLFunctions.HTGeometry
