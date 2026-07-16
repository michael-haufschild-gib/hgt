import GaloisForLFunctions.Core
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# Reciprocal Hankel multiplicity sensitivity

A fixed reciprocal support can pass or fail the first two Hankel tests solely because the
conjugate-pair multiplicity changes.  The construction uses the real atom `1` with weight `2` and
the conjugate pair `-1/2 ± i` with common weight `c`.
-/

open scoped BigOperators Matrix ComplexConjugate

namespace RHTower

noncomputable section

/-- The nonreal reciprocal atom in the multiplicity counterexample. -/
def reciprocalMultiplicityAtom : ℂ := -(1 / 2 : ℂ) + Complex.I

/-- Real moments of the fixed support consisting of `1` and one conjugate pair. -/
def reciprocalMultiplicityMoment (c : ℝ) (n : ℕ) : ℝ :=
  2 + c * ((reciprocalMultiplicityAtom ^ n + star reciprocalMultiplicityAtom ^ n).re)

/-- The first four moments when the conjugate-pair weight is one. -/
theorem reciprocalMultiplicityMoment_one_values :
    reciprocalMultiplicityMoment 1 0 = 4 ∧
      reciprocalMultiplicityMoment 1 1 = 1 ∧
      reciprocalMultiplicityMoment 1 2 = 1 / 2 ∧
      reciprocalMultiplicityMoment 1 3 = 19 / 4 := by
  norm_num [reciprocalMultiplicityMoment, reciprocalMultiplicityAtom, pow_succ,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im]

/-- The first four moments when the conjugate-pair weight is two. -/
theorem reciprocalMultiplicityMoment_two_values :
    reciprocalMultiplicityMoment 2 0 = 6 ∧
      reciprocalMultiplicityMoment 2 1 = 0 ∧
      reciprocalMultiplicityMoment 2 2 = -1 ∧
      reciprocalMultiplicityMoment 2 3 = 15 / 2 := by
  norm_num [reciprocalMultiplicityMoment, reciprocalMultiplicityAtom, pow_succ,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im]

/-- Unshifted leading Hankel block for conjugate-pair weight `c`. -/
def reciprocalMultiplicityHankelZero (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![reciprocalMultiplicityMoment c 0, reciprocalMultiplicityMoment c 1;
     reciprocalMultiplicityMoment c 1, reciprocalMultiplicityMoment c 2]

/-- Shifted leading Hankel block for conjugate-pair weight `c`. -/
def reciprocalMultiplicityHankelOne (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![reciprocalMultiplicityMoment c 1, reciprocalMultiplicityMoment c 2;
     reciprocalMultiplicityMoment c 2, reciprocalMultiplicityMoment c 3]

def reciprocalMultiplicityFactorZero : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 4; 0, 1]

def reciprocalMultiplicityDiagonalZero : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![4, 1 / 4]

theorem reciprocalMultiplicityFactorZero_mulVec_injective :
    Function.Injective reciprocalMultiplicityFactorZero.mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
  norm_num [reciprocalMultiplicityFactorZero, Matrix.det_fin_two]

/-- An exact positive `LDLᴴ` factorization of the unshifted weight-one block. -/
theorem reciprocalMultiplicityHankelZero_one_factorization :
    reciprocalMultiplicityHankelZero 1 =
      reciprocalMultiplicityFactorZeroᴴ * reciprocalMultiplicityDiagonalZero *
        reciprocalMultiplicityFactorZero := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reciprocalMultiplicityHankelZero, reciprocalMultiplicityMoment,
      reciprocalMultiplicityAtom, reciprocalMultiplicityFactorZero,
      reciprocalMultiplicityDiagonalZero, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal, pow_succ, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

/-- The unshifted weight-one block is positive definite. -/
theorem reciprocalMultiplicityHankelZero_one_posDef :
    (reciprocalMultiplicityHankelZero 1).PosDef := by
  have hdiag : reciprocalMultiplicityDiagonalZero.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num
  rw [reciprocalMultiplicityHankelZero_one_factorization]
  exact hdiag.conjTranspose_mul_mul_same reciprocalMultiplicityFactorZero_mulVec_injective

def reciprocalMultiplicityFactorOne : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 0, 1]

def reciprocalMultiplicityDiagonalOne : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![1, 9 / 2]

theorem reciprocalMultiplicityFactorOne_mulVec_injective :
    Function.Injective reciprocalMultiplicityFactorOne.mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
  norm_num [reciprocalMultiplicityFactorOne, Matrix.det_fin_two]

/-- An exact positive `LDLᴴ` factorization of the shifted weight-one block. -/
theorem reciprocalMultiplicityHankelOne_one_factorization :
    reciprocalMultiplicityHankelOne 1 =
      reciprocalMultiplicityFactorOneᴴ * reciprocalMultiplicityDiagonalOne *
        reciprocalMultiplicityFactorOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reciprocalMultiplicityHankelOne, reciprocalMultiplicityMoment,
      reciprocalMultiplicityAtom, reciprocalMultiplicityFactorOne,
      reciprocalMultiplicityDiagonalOne, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal, pow_succ, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

/-- The shifted weight-one block is positive definite. -/
theorem reciprocalMultiplicityHankelOne_one_posDef :
    (reciprocalMultiplicityHankelOne 1).PosDef := by
  have hdiag : reciprocalMultiplicityDiagonalOne.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num
  rw [reciprocalMultiplicityHankelOne_one_factorization]
  exact hdiag.conjTranspose_mul_mul_same reciprocalMultiplicityFactorOne_mulVec_injective

/-- The unshifted weight-two determinant is negative. -/
theorem reciprocalMultiplicityHankelZero_two_det :
    (reciprocalMultiplicityHankelZero 2).det = -6 := by
  norm_num [reciprocalMultiplicityHankelZero, reciprocalMultiplicityMoment,
    reciprocalMultiplicityAtom, Matrix.det_fin_two, pow_succ, Complex.ext_iff,
    Complex.mul_re, Complex.mul_im]

/-- The unshifted weight-two block is not positive semidefinite. -/
theorem reciprocalMultiplicityHankelZero_two_not_posSemidef :
    ¬ (reciprocalMultiplicityHankelZero 2).PosSemidef := by
  intro h
  have hdet := h.det_nonneg
  rw [reciprocalMultiplicityHankelZero_two_det] at hdet
  norm_num at hdet

/-- The shifted weight-two determinant is negative. -/
theorem reciprocalMultiplicityHankelOne_two_det :
    (reciprocalMultiplicityHankelOne 2).det = -1 := by
  norm_num [reciprocalMultiplicityHankelOne, reciprocalMultiplicityMoment,
    reciprocalMultiplicityAtom, Matrix.det_fin_two, pow_succ, Complex.ext_iff,
    Complex.mul_re, Complex.mul_im]

/-- The shifted weight-two block is not positive semidefinite. -/
theorem reciprocalMultiplicityHankelOne_two_not_posSemidef :
    ¬ (reciprocalMultiplicityHankelOne 2).PosSemidef := by
  intro h
  have hdet := h.det_nonneg
  rw [reciprocalMultiplicityHankelOne_two_det] at hdet
  norm_num at hdet

/-- The support is fixed, but changing only the conjugate-pair multiplicity changes both leading
Hankel tests from positive definite to indefinite. -/
theorem reciprocalMultiplicity_sameSupport_changes_hankelPositivity :
    (reciprocalMultiplicityHankelZero 1).PosDef ∧
      (reciprocalMultiplicityHankelOne 1).PosDef ∧
      ¬ (reciprocalMultiplicityHankelZero 2).PosSemidef ∧
      ¬ (reciprocalMultiplicityHankelOne 2).PosSemidef :=
  ⟨reciprocalMultiplicityHankelZero_one_posDef,
    reciprocalMultiplicityHankelOne_one_posDef,
    reciprocalMultiplicityHankelZero_two_not_posSemidef,
    reciprocalMultiplicityHankelOne_two_not_posSemidef⟩

end

end RHTower
