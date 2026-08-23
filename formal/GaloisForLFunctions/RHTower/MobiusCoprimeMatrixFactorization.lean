import GaloisForLFunctions.RHTower.MobiusCoprimeIncidence
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Block

open scoped ArithmeticFunction.Moebius

namespace RHTower

noncomputable section

/-- The `(a,b)` entry of a finite Möbius incidence product, on coordinates `1` through `N`. -/
def finiteMobiusCoprimeIncidenceEntry (N a b : ℕ) : ℤ :=
  ∑ d ∈ Finset.Icc 1 N,
    (if d ∣ a then 1 else 0) * μ d * (if d ∣ b then 1 else 0)

/-- The natural positive coordinates of a finite coprimality matrix. -/
abbrev finiteMobiusCoprimeCoordinate (N : ℕ) := {a : ℕ // a ∈ Finset.Icc 1 N}

/-- A finite interval containing `a` contains every common divisor of `a` and `b`. -/
theorem finiteMobiusCoprimeIncidenceEntry_eq_coprimeIndicator
    (N : ℕ) (a : finiteMobiusCoprimeCoordinate N) (b : ℕ) :
    finiteMobiusCoprimeIncidenceEntry N a.1 b = if a.1.Coprime b then 1 else 0 := by
  unfold finiteMobiusCoprimeIncidenceEntry
  have ha : 0 < a.1 := (Finset.mem_Icc.mp a.2).1
  have haN : a.1 ≤ N := (Finset.mem_Icc.mp a.2).2
  have hterm (d : ℕ) :
      (if d ∣ a.1 then (1 : ℤ) else 0) * μ d * (if d ∣ b then 1 else 0) =
        if d ∣ a.1 ∧ d ∣ b then μ d else 0 := by
    split_ifs with hda hdb <;> simp_all
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  have hgpos : 0 < a.1.gcd b := Nat.gcd_pos_of_pos_left b ha
  have hset : (Finset.Icc 1 N).filter (fun d => d ∣ a.1 ∧ d ∣ b) = (a.1.gcd b).divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdpos, hdN⟩, hda, hdb⟩
      exact ⟨Nat.dvd_gcd hda hdb, ne_of_gt hgpos⟩
    · rintro ⟨hdg, _⟩
      refine ⟨?_, (Nat.dvd_gcd_iff.mp hdg).1, (Nat.dvd_gcd_iff.mp hdg).2⟩
      exact ⟨Nat.pos_of_dvd_of_pos hdg hgpos,
        (Nat.le_of_dvd hgpos hdg).trans ((Nat.gcd_le_left b ha).trans haN)⟩
  rw [hset]
  exact mobiusCommonDivisorKernel_eq_coprimeIndicator a.1 b

/-- The finite coprimality matrix on positive coordinates through `N`. -/
def finiteMobiusCoprimeMatrix (N : ℕ) :
    Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℤ :=
  fun a b => if a.1.Coprime b.1 then 1 else 0

/-- Divisor incidence matrix on the same finite positive coordinates. -/
def finiteMobiusDivisorIncidenceMatrix (N : ℕ) :
    Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℤ :=
  fun a d => if d.1 ∣ a.1 then 1 else 0

/-- Möbius diagonal on finite positive coordinates. -/
def finiteMobiusDiagonalMatrix (N : ℕ) :
    Matrix (finiteMobiusCoprimeCoordinate N) (finiteMobiusCoprimeCoordinate N) ℤ :=
  Matrix.diagonal fun d => μ d.1

/-- The entry of the incidence product is the finite common-divisor Möbius sum. -/
theorem finiteMobiusIncidenceProduct_apply (N : ℕ)
    (a b : finiteMobiusCoprimeCoordinate N) :
    (finiteMobiusDivisorIncidenceMatrix N * finiteMobiusDiagonalMatrix N *
        (finiteMobiusDivisorIncidenceMatrix N).transpose) a b =
      finiteMobiusCoprimeIncidenceEntry N a.1 b.1 := by
  rw [Matrix.mul_apply]
  simp only [finiteMobiusDiagonalMatrix, finiteMobiusDivisorIncidenceMatrix,
    Matrix.mul_diagonal, Matrix.transpose_apply]
  symm
  unfold finiteMobiusCoprimeIncidenceEntry
  rw [Finset.sum_subtype (Finset.Icc 1 N) (by intro x; rfl)]

/-- Exact finite Möbius incidence factorization of the coprimality matrix. -/
theorem finiteMobiusCoprimeMatrix_factorization (N : ℕ) :
    finiteMobiusCoprimeMatrix N = finiteMobiusDivisorIncidenceMatrix N *
      finiteMobiusDiagonalMatrix N * (finiteMobiusDivisorIncidenceMatrix N).transpose := by
  ext a b
  rw [finiteMobiusIncidenceProduct_apply]
  exact (finiteMobiusCoprimeIncidenceEntry_eq_coprimeIndicator N a b.1).symm

/-- The divisor-incidence matrix is lower triangular in the natural coordinate order. -/
theorem finiteMobiusDivisorIncidenceMatrix_blockTriangular (N : ℕ) :
    (finiteMobiusDivisorIncidenceMatrix N).BlockTriangular (OrderDual.toDual) := by
  intro a d had
  unfold finiteMobiusDivisorIncidenceMatrix
  apply if_neg
  intro hda
  have ha : 0 < a.1 := (Finset.mem_Icc.mp a.2).1
  have hle : d.1 ≤ a.1 := Nat.le_of_dvd ha hda
  have hlt : a.1 < d.1 := had
  exact (Nat.not_le_of_gt hlt) hle

/-- Every diagonal entry of the divisor-incidence matrix is one. -/
theorem finiteMobiusDivisorIncidenceMatrix_diag (N : ℕ)
    (a : finiteMobiusCoprimeCoordinate N) :
    finiteMobiusDivisorIncidenceMatrix N a a = 1 := by
  unfold finiteMobiusDivisorIncidenceMatrix
  exact if_pos dvd_rfl

/-- The finite divisor-incidence matrix has determinant one. -/
theorem det_finiteMobiusDivisorIncidenceMatrix (N : ℕ) :
    (finiteMobiusDivisorIncidenceMatrix N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (finiteMobiusDivisorIncidenceMatrix_blockTriangular N)]
  simp only [finiteMobiusDivisorIncidenceMatrix_diag, Finset.prod_const_one]

/-- The finite divisor-incidence matrix is invertible over the integers. -/
theorem isUnit_finiteMobiusDivisorIncidenceMatrix (N : ℕ) :
    IsUnit (finiteMobiusDivisorIncidenceMatrix N) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_finiteMobiusDivisorIncidenceMatrix]
  exact isUnit_one

end

end RHTower
