import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Polynomial form of the matrix-semicircle Dyson equation

The matrix Cauchy transform of a finite matrix semicircle obeys a square quadratic system. This
file defines that system literally, proves its evaluation is exactly Speicher's Dyson equation,
and certifies the uniform total-degree bound two needed by elimination.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

/-- Covariance map of a finite matrix pencil. For a Hermitian family this is
`X ↦ ∑ₖ Aₖ X Aₖ`. -/
def matrixSemicircleCovariance (A : K → Matrix I I ℂ) (X : Matrix I I ℂ) :
    Matrix I I ℂ :=
  ∑ k, A k * X * (A k)ᴴ

/-- Coordinate set for one spectral variable and all entries of the matrix Cauchy transform. -/
abbrev MatrixDysonVariable (I : Type*) := Option (I × I)

/-- Spectral coordinate of the universal Dyson system. -/
def matrixDysonZ (I : Type*) : MvPolynomial (MatrixDysonVariable I) ℂ :=
  MvPolynomial.X none

/-- Matrix-entry coordinate of the universal Dyson system. -/
def matrixDysonEntry (i j : I) : MvPolynomial (MatrixDysonVariable I) ℂ :=
  MvPolynomial.X (some (i, j))

/-- Entry `(i,j)` of the cleared matrix-semicircle Dyson equation
`zG = I + η(G)G`. -/
def matrixDysonPolynomial (A : K → Matrix I I ℂ) (i j : I) :
    MvPolynomial (MatrixDysonVariable I) ℂ :=
  matrixDysonZ I * matrixDysonEntry i j - MvPolynomial.C (if i = j then 1 else 0) -
    ∑ k, ∑ l, ∑ m, ∑ q, MvPolynomial.C (A k i l) * matrixDysonEntry l m *
      MvPolynomial.C (star (A k q m)) * matrixDysonEntry q j

/-- Evaluation point consisting of a spectral parameter and a candidate matrix Cauchy transform. -/
def matrixDysonPoint (z : ℂ) (G : Matrix I I ℂ) : MatrixDysonVariable I → ℂ
  | none => z
  | some ij => G ij.1 ij.2

omit [Fintype I] [DecidableEq I] in
@[simp] theorem eval_matrixDysonZ (z : ℂ) (G : Matrix I I ℂ) :
    MvPolynomial.eval (matrixDysonPoint z G) (matrixDysonZ I) = z := by
  simp [matrixDysonZ, matrixDysonPoint]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem eval_matrixDysonEntry (z : ℂ) (G : Matrix I I ℂ) (i j : I) :
    MvPolynomial.eval (matrixDysonPoint z G) (matrixDysonEntry i j) = G i j := by
  simp [matrixDysonEntry, matrixDysonPoint]

/-- The coordinate polynomial evaluates to the corresponding entry of the literal Dyson defect. -/
theorem eval_matrixDysonPolynomial (A : K → Matrix I I ℂ) (z : ℂ)
    (G : Matrix I I ℂ) (i j : I) :
    MvPolynomial.eval (matrixDysonPoint z G) (matrixDysonPolynomial A i j) =
      (z • G - 1 - matrixSemicircleCovariance A G * G) i j := by
  simp only [matrixDysonPolynomial, map_sub, map_mul, MvPolynomial.eval_C, map_sum,
    eval_matrixDysonZ, eval_matrixDysonEntry, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, matrixSemicircleCovariance, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_mul]
  have hsum :
      (∑ q : I, ∑ k : K, ∑ m : I, ∑ l : I,
          A k i l * G l m * star (A k q m) * G q j) =
        ∑ k : K, ∑ l : I, ∑ m : I, ∑ q : I,
          A k i l * G l m * star (A k q m) * G q j := by
    calc
      (∑ q : I, ∑ k : K, ∑ m : I, ∑ l : I,
          A k i l * G l m * star (A k q m) * G q j) =
          ∑ k : K, ∑ q : I, ∑ m : I, ∑ l : I,
            A k i l * G l m * star (A k q m) * G q j := Finset.sum_comm
      _ = ∑ k : K, ∑ l : I, ∑ m : I, ∑ q : I,
          A k i l * G l m * star (A k q m) * G q j := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          (∑ q : I, ∑ m : I, ∑ l : I,
              A k i l * G l m * star (A k q m) * G q j) =
              ∑ q : I, ∑ l : I, ∑ m : I,
                A k i l * G l m * star (A k q m) * G q j := by
            apply Finset.sum_congr rfl
            intro q _
            rw [Finset.sum_comm]
          _ = ∑ l : I, ∑ q : I, ∑ m : I,
              A k i l * G l m * star (A k q m) * G q j := Finset.sum_comm
          _ = ∑ l : I, ∑ m : I, ∑ q : I,
              A k i l * G l m * star (A k q m) * G q j := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_comm]
  rw [hsum]

/-- Simultaneous vanishing of the square polynomial system is exactly Speicher's matrix Dyson
equation, with no discarded coordinate or denominator. -/
theorem matrixDysonPolynomial_vanishes_iff (A : K → Matrix I I ℂ) (z : ℂ)
    (G : Matrix I I ℂ) :
    (∀ i j, MvPolynomial.eval (matrixDysonPoint z G) (matrixDysonPolynomial A i j) = 0) ↔
      z • G = 1 + matrixSemicircleCovariance A G * G := by
  constructor
  · intro h
    ext i j
    have hij := h i j
    simp only [eval_matrixDysonPolynomial, Matrix.sub_apply] at hij
    rw [Matrix.add_apply]
    linear_combination hij
  · intro h i j
    have hij := congr_fun (congr_fun h i) j
    simp only [eval_matrixDysonPolynomial, Matrix.add_apply, Matrix.sub_apply] at hij ⊢
    linear_combination hij

/-- Every member of the matrix Dyson system has total degree at most two. -/
theorem matrixDysonPolynomial_totalDegree_le_two
    (A : K → Matrix I I ℂ) (i j : I) :
    (matrixDysonPolynomial A i j).totalDegree ≤ 2 := by
  have hzg :
      (matrixDysonZ I * matrixDysonEntry i j).totalDegree ≤ 2 := by
    calc
      (matrixDysonZ I * matrixDysonEntry i j).totalDegree ≤
          (matrixDysonZ I).totalDegree + (matrixDysonEntry i j).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = 2 := by simp [matrixDysonZ, matrixDysonEntry]
  have hterm : ∀ k : K, ∀ l m q : I,
      (MvPolynomial.C (A k i l) * matrixDysonEntry l m *
        MvPolynomial.C (star (A k q m)) * matrixDysonEntry q j).totalDegree ≤ 2 := by
    intro k l m q
    calc
      (MvPolynomial.C (A k i l) * matrixDysonEntry l m *
          MvPolynomial.C (star (A k q m)) * matrixDysonEntry q j).totalDegree ≤
          (MvPolynomial.C (A k i l) * matrixDysonEntry l m *
            MvPolynomial.C (star (A k q m))).totalDegree +
              (matrixDysonEntry q j).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C (A k i l) * matrixDysonEntry l m).totalDegree +
            (MvPolynomial.C (star (A k q m))).totalDegree) +
              (matrixDysonEntry q j).totalDegree := by
        gcongr
        exact MvPolynomial.totalDegree_mul _ _
      _ ≤ (((MvPolynomial.C (A k i l)).totalDegree +
              (matrixDysonEntry l m).totalDegree) +
            (MvPolynomial.C (star (A k q m))).totalDegree) +
              (matrixDysonEntry q j).totalDegree := by
        gcongr
        exact MvPolynomial.totalDegree_mul _ _
      _ = 2 := by simp [matrixDysonEntry]
  have hsum :
      (∑ k, ∑ l, ∑ m, ∑ q, MvPolynomial.C (A k i l) * matrixDysonEntry l m *
        MvPolynomial.C (star (A k q m)) * matrixDysonEntry q j).totalDegree ≤ 2 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k _
    apply MvPolynomial.totalDegree_finsetSum_le
    intro l _
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m _
    apply MvPolynomial.totalDegree_finsetSum_le
    intro q _
    exact hterm k l m q
  unfold matrixDysonPolynomial
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  apply max_le
  · refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    exact max_le hzg (by split <;> simp)
  · exact hsum

end

end GaloisForLFunctions.HTGeometry
