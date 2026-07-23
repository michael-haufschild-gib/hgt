import Mathlib

/-!
# Radical-quotient Evans coefficients

A split quotient `B` with right inverse `R` turns an ambient operator `A` preserving `ker B`
into `C = B A R`.  If an ambient semimetric factors as `L B`, then the characteristic polynomial
of `L B (A - z)` has a forced zero of order `dim(ambient) - dim(quotient)`.  Its first surviving
coefficient is exactly the quotient determinant times the corresponding coefficient of `L B`.

The source-pencil form is the useful boundary law: whenever

`(L B) A = (L B) D + S`,

the quotient determinant can be extracted from the entirely ambient pencil
`(L B)(D-z) + S`, without choosing a kernel basis or evaluating a quotient inverse.
-/

open Polynomial
open scoped Matrix

namespace HTGeometry

variable {R m n : Type*} [CommRing R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Operator induced on a chosen split quotient. -/
def splitQuotientCompression
    (B : Matrix m n R) (A : Matrix n n R) (Rinv : Matrix n m R) : Matrix m m R :=
  B * A * Rinv

omit [DecidableEq m] in
/-- Preservation of the radical makes split compression the honest quotient operator. -/
theorem splitQuotientCompression_intertwines
    (B : Matrix m n R) (A : Matrix n n R) (Rinv : Matrix n m R)
    (hradical : B * A * (1 - Rinv * B) = 0) :
    splitQuotientCompression B A Rinv * B = B * A := by
  have hradical' : (B * A) * (1 - Rinv * B) = 0 := by
    simpa only [Matrix.mul_assoc] using hradical
  rw [Matrix.mul_sub, Matrix.mul_one] at hradical'
  have hBA : (B * A) * (Rinv * B) = B * A := (sub_eq_zero.mp hradical').symm
  rw [splitQuotientCompression]
  calc
    (B * A * Rinv) * B = (B * A) * (Rinv * B) := by simp only [Matrix.mul_assoc]
    _ = B * A := hBA

/-- **Radical-factor characteristic law.** The ambient pencil contains the quotient pencil after
the exact radical power of `X` is removed. -/
theorem splitQuotient_pencil_charpoly
    (B : Matrix m n R) (L : Matrix n m R)
    (A : Matrix n n R) (Rinv : Matrix n m R) (z : R)
    (hle : Fintype.card m ≤ Fintype.card n)
    (hradical : B * A * (1 - Rinv * B) = 0) :
    (((L * B) * (A - z • 1)).charpoly) =
      X ^ (Fintype.card n - Fintype.card m) *
        (((splitQuotientCompression B A Rinv - z • 1) * (B * L)).charpoly) := by
  have hintertwines : splitQuotientCompression B A Rinv * B = B * A :=
    splitQuotientCompression_intertwines B A Rinv hradical
  have hpencil :
      (L * B) * (A - z • 1) =
        L * ((splitQuotientCompression B A Rinv - z • 1) * B) := by
    calc
      (L * B) * (A - z • 1) = L * (B * A - z • B) := by
        simp [Matrix.mul_sub, Matrix.mul_assoc]
      _ = L * (splitQuotientCompression B A Rinv * B - z • B) := by
        rw [hintertwines]
      _ = L * ((splitQuotientCompression B A Rinv - z • 1) * B) := by
        simp [Matrix.sub_mul]
  rw [hpencil]
  calc
    (L * ((splitQuotientCompression B A Rinv - z • 1) * B)).charpoly =
        X ^ (Fintype.card n - Fintype.card m) *
          ((((splitQuotientCompression B A Rinv - z • 1) * B) * L).charpoly) :=
      Matrix.charpoly_mul_comm_of_le
        L ((splitQuotientCompression B A Rinv - z • 1) * B) hle
    _ = X ^ (Fintype.card n - Fintype.card m) *
        (((splitQuotientCompression B A Rinv - z • 1) * (B * L)).charpoly) := by
      rw [Matrix.mul_assoc]

/-- **Kernel-free Evans extraction.** The first coefficient above the forced radical power is the
quotient characteristic determinant times the first coefficient of the semimetric. -/
theorem splitQuotient_pencil_lowestCoeff
    (B : Matrix m n R) (L : Matrix n m R)
    (A : Matrix n n R) (Rinv : Matrix n m R) (z : R)
    (hle : Fintype.card m ≤ Fintype.card n)
    (hradical : B * A * (1 - Rinv * B) = 0) :
    (((L * B) * (A - z • 1)).charpoly).coeff
        (Fintype.card n - Fintype.card m) =
      Matrix.det (splitQuotientCompression B A Rinv - z • 1) *
        ((L * B).charpoly).coeff (Fintype.card n - Fintype.card m) := by
  let k := Fintype.card n - Fintype.card m
  let C := splitQuotientCompression B A Rinv
  let G := B * L
  have hpencil := splitQuotient_pencil_charpoly B L A Rinv z hle hradical
  have hbase : (L * B).charpoly = X ^ k * G.charpoly := by
    exact Matrix.charpoly_mul_comm_of_le L B hle
  have hpencilCoeff := congrArg (fun p : R[X] => p.coeff k) hpencil
  have hbaseCoeff := congrArg (fun p : R[X] => p.coeff k) hbase
  have hpencilCoeff' :
      (((L * B) * (A - z • 1)).charpoly).coeff k =
        (((C - z • 1) * G).charpoly).coeff 0 := by
    simpa [k, C, G, Polynomial.coeff_X_pow_mul'] using hpencilCoeff
  have hbaseCoeff' : ((L * B).charpoly).coeff k = G.charpoly.coeff 0 := by
    simpa [k, G, Polynomial.coeff_X_pow_mul'] using hbaseCoeff
  have coeff_zero_eq_sign_det (M : Matrix m m R) :
      M.charpoly.coeff 0 = (-1 : R) ^ Fintype.card m * M.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff]
    rw [← mul_assoc, ← pow_add]
    simp
  rw [hpencilCoeff', hbaseCoeff', coeff_zero_eq_sign_det,
    Matrix.det_mul, coeff_zero_eq_sign_det]
  ring

/-- **Source-pencil Evans law.** If the semimetric action of the quotient completion is already
the source-defined pencil `(L B)D + S`, its lowest characteristic coefficient recovers the same
quotient determinant. No radical vector, quotient basis, or inverse appears on the left. -/
theorem splitQuotient_sourcePencil_lowestCoeff
    (B : Matrix m n R) (L : Matrix n m R)
    (A D : Matrix n n R) (Rinv : Matrix n m R)
    (S : Matrix n n R) (z : R)
    (hle : Fintype.card m ≤ Fintype.card n)
    (hradical : B * A * (1 - Rinv * B) = 0)
    (hsource : (L * B) * A = (L * B) * D + S) :
    (((L * B) * (D - z • 1) + S).charpoly).coeff
        (Fintype.card n - Fintype.card m) =
      Matrix.det (splitQuotientCompression B A Rinv - z • 1) *
        ((L * B).charpoly).coeff (Fintype.card n - Fintype.card m) := by
  have hpencil : (L * B) * (D - z • 1) + S = (L * B) * (A - z • 1) := by
    calc
      (L * B) * (D - z • 1) + S = (L * B) * D - z • (L * B) + S := by
        simp [Matrix.mul_sub]
      _ = (L * B) * A - z • (L * B) := by rw [hsource]; abel
      _ = (L * B) * (A - z • 1) := by simp [Matrix.mul_sub]
  rw [hpencil]
  exact splitQuotient_pencil_lowestCoeff B L A Rinv z hle hradical

end HTGeometry
