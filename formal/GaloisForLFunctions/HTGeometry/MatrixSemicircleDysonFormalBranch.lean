import GaloisForLFunctions.HTGeometry.MatrixSemicircleDysonCoordinateRing
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal branch of the rescaled matrix Dyson equation

This module constructs the unique coefficientwise formal solution of
`H = I + u · η(H)H`, proves the equation exactly, and factors evaluation through the rescaled
Dyson coordinate ring.  Its constant term is the identity point on the infinity fibre.
-/

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

/-- Coefficient matrix of a matrix-valued power series. -/
def matrixPowerSeriesCoeff (H : Matrix I I (PowerSeries ℂ)) (n : ℕ) : Matrix I I ℂ :=
  fun i j => PowerSeries.coeff n (H i j)

/-- Entrywise constant embedding of a complex matrix into power series. -/
def constantPowerSeriesMatrix (M : Matrix I I ℂ) : Matrix I I (PowerSeries ℂ) :=
  fun i j => PowerSeries.C (M i j)

/-- Matrix-semicircle covariance acting coefficientwise on power-series matrices. -/
def matrixSemicircleCovariancePowerSeries
    (A : K → Matrix I I ℂ) (H : Matrix I I (PowerSeries ℂ)) :
    Matrix I I (PowerSeries ℂ) :=
  ∑ k, constantPowerSeriesMatrix (A k) * H * constantPowerSeriesMatrix (A k)ᴴ

omit [DecidableEq I] in
theorem matrixPowerSeriesCoeff_covariance
    (A : K → Matrix I I ℂ) (H : Matrix I I (PowerSeries ℂ)) (n : ℕ) :
    matrixPowerSeriesCoeff (matrixSemicircleCovariancePowerSeries A H) n =
      matrixSemicircleCovariance A (matrixPowerSeriesCoeff H n) := by
  ext i j
  simp only [matrixPowerSeriesCoeff, matrixSemicircleCovariancePowerSeries,
    matrixSemicircleCovariance, Matrix.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [constantPowerSeriesMatrix, Matrix.mul_apply, matrixPowerSeriesCoeff]

omit [DecidableEq I] in
theorem powerSeriesCoeff_covariance_mul
    (A : K → Matrix I I ℂ) (H : Matrix I I (PowerSeries ℂ)) (n : ℕ) (i j : I) :
    PowerSeries.coeff n ((matrixSemicircleCovariancePowerSeries A H * H) i j) =
      ∑ p : Fin (n + 1),
        (matrixSemicircleCovariance A (matrixPowerSeriesCoeff H p) *
          matrixPowerSeriesCoeff H (n - p)) i j := by
  simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul]
  rw [Finset.sum_comm, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l hl
  rw [show PowerSeries.coeff p (matrixSemicircleCovariancePowerSeries A H i l) =
      matrixSemicircleCovariance A (matrixPowerSeriesCoeff H p) i l by
    exact congr_fun (congr_fun (matrixPowerSeriesCoeff_covariance A H p) i) l]
  rfl

/-- Recursive coefficients of the formal branch based at `H(0)=I`. -/
def matrixDysonFormalCoeff (A : K → Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | n + 1 => ∑ p : Fin (n + 1),
      matrixSemicircleCovariance A (matrixDysonFormalCoeff A p) *
        matrixDysonFormalCoeff A (n - p)
termination_by n => n
decreasing_by
  all_goals omega

/-- Formal matrix solution of the rescaled matrix Dyson equation at infinity. -/
def matrixDysonFormalSeries (A : K → Matrix I I ℂ) : Matrix I I (PowerSeries ℂ) :=
  fun i j => PowerSeries.mk fun n => matrixDysonFormalCoeff A n i j

@[simp]
theorem coeff_matrixDysonFormalSeries
    (A : K → Matrix I I ℂ) (n : ℕ) (i j : I) :
    PowerSeries.coeff n (matrixDysonFormalSeries A i j) = matrixDysonFormalCoeff A n i j := by
  simp [matrixDysonFormalSeries]

@[simp]
theorem matrixPowerSeriesCoeff_matrixDysonFormalSeries
    (A : K → Matrix I I ℂ) (n : ℕ) :
    matrixPowerSeriesCoeff (matrixDysonFormalSeries A) n = matrixDysonFormalCoeff A n := by
  ext i j
  simp [matrixPowerSeriesCoeff]

/-- The recursive formal branch satisfies `H = I + u · η(H)H` coefficientwise. -/
theorem matrixDysonFormalSeries_eq (A : K → Matrix I I ℂ) :
    matrixDysonFormalSeries A = 1 + (PowerSeries.X : PowerSeries ℂ) •
      (matrixSemicircleCovariancePowerSeries A (matrixDysonFormalSeries A) *
        matrixDysonFormalSeries A) := by
  ext i j n
  cases n with
  | zero => simp [matrixDysonFormalCoeff, Matrix.one_apply]
  | succ n =>
      simp only [matrixDysonFormalSeries, PowerSeries.coeff_mk, matrixDysonFormalCoeff,
        Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, map_add, smul_eq_mul,
        PowerSeries.coeff_succ_X_mul]
      rw [powerSeriesCoeff_covariance_mul]
      have hconst : PowerSeries.coeff (n + 1)
          (if i = j then (1 : PowerSeries ℂ) else 0) = 0 := by
        split <;> simp
      rw [hconst, zero_add, Matrix.sum_apply]
      simp

/-- Ambient polynomial evaluation at the formal Dyson branch. -/
def matrixDysonFormalAmbientEval (A : K → Matrix I I ℂ) :
    MvPolynomial (I × I) (Polynomial ℂ) →+* PowerSeries ℂ :=
  MvPolynomial.eval₂Hom Polynomial.coeToPowerSeries.ringHom
    (fun ij => matrixDysonFormalSeries A ij.1 ij.2)

theorem matrixDysonFormalAmbientEval_baseQuadratic
    (A : K → Matrix I I ℂ) (ij : I × I) :
    matrixDysonFormalAmbientEval A (matrixDysonInfinityBaseQuadratic A ij) =
      (matrixSemicircleCovariancePowerSeries A (matrixDysonFormalSeries A) *
        matrixDysonFormalSeries A) ij.1 ij.2 := by
  simp only [matrixDysonFormalAmbientEval, matrixDysonInfinityBaseQuadratic,
    matrixDysonQuadraticPolynomial_eq_sum, map_sum, map_mul, matrixDysonEntry,
    MvPolynomial.optionEquivRight_C, MvPolynomial.optionEquivRight_X_some,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
  simp only [matrixSemicircleCovariancePowerSeries, Matrix.sum_apply, Matrix.mul_apply,
    constantPowerSeriesMatrix, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_mul]
  have hsum :
      (∑ q : I, ∑ k : K, ∑ m : I, ∑ l : I,
          PowerSeries.C (A k ij.1 l) * matrixDysonFormalSeries A l m *
            PowerSeries.C (star (A k q m)) * matrixDysonFormalSeries A q ij.2) =
        ∑ k : K, ∑ l : I, ∑ m : I, ∑ q : I,
          PowerSeries.C (A k ij.1 l) * matrixDysonFormalSeries A l m *
            PowerSeries.C (star (A k q m)) * matrixDysonFormalSeries A q ij.2 := by
    calc
      _ = ∑ k : K, ∑ q : I, ∑ m : I, ∑ l : I,
          PowerSeries.C (A k ij.1 l) * matrixDysonFormalSeries A l m *
            PowerSeries.C (star (A k q m)) * matrixDysonFormalSeries A q ij.2 := Finset.sum_comm
      _ = ∑ k : K, ∑ l : I, ∑ m : I, ∑ q : I,
          PowerSeries.C (A k ij.1 l) * matrixDysonFormalSeries A l m *
            PowerSeries.C (star (A k q m)) * matrixDysonFormalSeries A q ij.2 := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          _ = ∑ q : I, ∑ l : I, ∑ m : I,
              PowerSeries.C (A k ij.1 l) * matrixDysonFormalSeries A l m *
                PowerSeries.C (star (A k q m)) * matrixDysonFormalSeries A q ij.2 := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.sum_comm]
          _ = ∑ l : I, ∑ q : I, ∑ m : I,
              PowerSeries.C (A k ij.1 l) * matrixDysonFormalSeries A l m *
                PowerSeries.C (star (A k q m)) * matrixDysonFormalSeries A q ij.2 := Finset.sum_comm
          _ = ∑ l : I, ∑ m : I, ∑ q : I,
              PowerSeries.C (A k ij.1 l) * matrixDysonFormalSeries A l m *
                PowerSeries.C (star (A k q m)) * matrixDysonFormalSeries A q ij.2 := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [Finset.sum_comm]
  rw [hsum]

@[simp]
theorem matrixDysonFormalAmbientEval_relation
    (A : K → Matrix I I ℂ) (ij : I × I) :
    matrixDysonFormalAmbientEval A (matrixDysonInfinityBaseRelation A ij) = 0 := by
  rw [matrixDysonInfinityBaseRelation, map_sub, map_sub, map_mul,
    matrixDysonFormalAmbientEval_baseQuadratic]
  simp only [matrixDysonFormalAmbientEval, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C]
  have h := congr_fun (congr_fun (matrixDysonFormalSeries_eq A) ij.1) ij.2
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at h
  change (matrixDysonFormalSeries A ij.1 ij.2 -
      PowerSeries.C (matrixDysonIdentityEntry ij)) -
        PowerSeries.X *
          (matrixSemicircleCovariancePowerSeries A (matrixDysonFormalSeries A) *
            matrixDysonFormalSeries A) ij.1 ij.2 = 0
  by_cases hij : ij.1 = ij.2 <;>
    simp [matrixDysonIdentityEntry, hij] at h ⊢ <;>
    linear_combination h

/-- Evaluation of the rescaled Dyson coordinate ring at its formal infinity branch. -/
def matrixDysonFormalBranchHom (A : K → Matrix I I ℂ) :
    MatrixDysonInfinityCoordinateRing A →+* PowerSeries ℂ :=
  Ideal.Quotient.lift (matrixDysonInfinityRelationIdeal A)
    (matrixDysonFormalAmbientEval A) (by
      intro f hf
      change f ∈ RingHom.ker (matrixDysonFormalAmbientEval A)
      apply (Ideal.span_le.2 ?_) hf
      rintro _ ⟨ij, rfl⟩
      exact matrixDysonFormalAmbientEval_relation A ij)

theorem constantCoeff_matrixDysonFormalAmbientEval
    (A : K → Matrix I I ℂ) (f : MvPolynomial (I × I) (Polynomial ℂ)) :
    PowerSeries.constantCoeff (matrixDysonFormalAmbientEval A f) =
      matrixDysonInfinityAmbientAugmentation f := by
  let lhs : MvPolynomial (I × I) (Polynomial ℂ) →+* ℂ :=
    PowerSeries.constantCoeff.comp (matrixDysonFormalAmbientEval A)
  have hhom : lhs = matrixDysonInfinityAmbientAugmentation := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, matrixDysonFormalAmbientEval, matrixDysonInfinityAmbientAugmentation,
        mvPolynomialBaseZeroPointEval]
      exact Polynomial.coeff_zero_eq_eval_zero r
    · intro ij
      simp [lhs, matrixDysonFormalAmbientEval, matrixDysonFormalSeries,
        matrixDysonFormalCoeff, matrixDysonInfinityAmbientAugmentation,
        mvPolynomialBaseZeroPointEval, matrixDysonIdentityEntry, Matrix.one_apply]
  exact DFunLike.congr_fun hhom f

/-- The formal branch specializes at `u=0` to the unique identity point of the infinity fibre. -/
theorem constantCoeff_matrixDysonFormalBranchHom
    (A : K → Matrix I I ℂ) (x : MatrixDysonInfinityCoordinateRing A) :
    PowerSeries.constantCoeff (matrixDysonFormalBranchHom A x) =
      matrixDysonInfinityAugmentation A x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [matrixDysonFormalBranchHom, Ideal.Quotient.lift_mk,
    matrixDysonInfinityAugmentation, Ideal.Quotient.lift_mk]
  exact constantCoeff_matrixDysonFormalAmbientEval A f

end

end GaloisForLFunctions.HTGeometry
