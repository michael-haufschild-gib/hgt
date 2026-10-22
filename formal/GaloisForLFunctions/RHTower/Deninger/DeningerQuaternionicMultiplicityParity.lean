import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Quaternionic multiplicity parity

This is the finite-dimensional representation-theoretic parity step in
Deninger's global-real-cohomology obstruction.  If an anti-linear operator on
an `n`-dimensional complex space squares to `-1`, its coordinate matrix `A`
satisfies `A * conj(A) = -1`; taking determinants forces `n` to be even.

It deliberately does not assert Deninger's arithmetic input: the `Q₈` Artin
representation, its root number, and the identification of its central order
with the relevant cohomological multiplicity remain separate hypotheses.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Entrywise complex conjugation.  This is distinct from the matrix `star`,
which also transposes indices. -/
def deningerEntrywiseConjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (starRingEnd ℂ).mapMatrix A

theorem det_deningerEntrywiseConjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (deningerEntrywiseConjugate A).det = star A.det := by
  simpa [deningerEntrywiseConjugate] using ((starRingEnd ℂ).map_det A).symm

/-- A complex vector space carrying a quaternionic anti-linear structure has
even complex dimension.  The matrix condition is the coordinate form of
`C² = -1` for `C(v) = A * conj(v)`. -/
theorem deningerQuaternionicMultiplicity_even
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A * deningerEntrywiseConjugate A = -1) :
    Even n := by
  by_contra hne
  have hodd : Odd n := Nat.not_even_iff_odd.mp hne
  have hdet := congrArg Matrix.det hA
  rw [Matrix.det_mul, det_deningerEntrywiseConjugate, Matrix.det_neg,
    Matrix.det_one, mul_one, Fintype.card_fin, hodd.neg_one_pow] at hdet
  have hnorm : ((Complex.normSq A.det : ℝ) : ℂ) = -1 := by
    calc
      ((Complex.normSq A.det : ℝ) : ℂ) = star A.det * A.det := by
        change ((Complex.normSq A.det : ℝ) : ℂ) =
          (starRingEnd ℂ) A.det * A.det
        rw [Complex.normSq_eq_conj_mul_self]
      _ = A.det * star A.det := by ring
      _ = -1 := hdet
  have hre := congrArg Complex.re hnorm
  have hnonneg := Complex.normSq_nonneg A.det
  norm_num at hre
  linarith

/-- The no-go form of the finite-dimensional parity obstruction: no odd-dimensional
complex multiplicity space can carry the quaternionic anti-linear structure forced
by a real symplectic isotypic summand. -/
theorem not_exists_deningerQuaternionicStructure_of_odd
    (n : ℕ) (hn : Odd n) :
    ¬ ∃ A : Matrix (Fin n) (Fin n) ℂ,
      A * deningerEntrywiseConjugate A = -1 := by
  rintro ⟨A, hA⟩
  exact (Nat.not_even_iff_odd.mpr hn)
    (deningerQuaternionicMultiplicity_even n A hA)

end

end RHTower
