import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic

/-!
# Row reduction of a uniformly scaled Jacobian

The jets of a logarithmically linear element `H` with `δH = U·H` are `δ^i H = H·B_i`, so a Jacobian of
those jets has rows

`∂_j(δ^i H) = H·∂_j B_i + B_i·∂_j H`,

and its first row is `∂_j H`, because `B_0 = 1`.  Subtracting `B_i` times the first row from every later
row leaves `H·∂_j B_i`, and scaling those rows out gives `H^n` times the bordered Jacobian.

Unlike the terminal-scaled case, no column is distinguished here: this is the reduction available when
the eliminated coordinate is *not* killed by the last derivation, which is the situation of a general
product law.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R]

/-- The Jacobian of the jets of a scaled element. -/
def uniformScaledMatrix {n : ℕ} (H : R) (a : Fin (n + 1) → R) (B : Fin n → R)
    (L : Fin n → Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => Fin.cases (a j) (fun r => H * L r j + B r * a j) i

/-- Its row-reduced form. -/
def uniformScaledReduced {n : ℕ} (H : R) (a : Fin (n + 1) → R)
    (L : Fin n → Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => Fin.cases (a j) (fun r => H * L r j) i

/-- The bordered Jacobian: the first row is the gradient of the element, the rest the gradients of the
Bell values. -/
def uniformBordered {n : ℕ} (a : Fin (n + 1) → R) (L : Fin n → Fin (n + 1) → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => Fin.cases (a j) (fun r => L r j) i

/-- **Row reduction against the first row.** -/
theorem uniformScaledMatrix_det_eq_reduced {n : ℕ} (H : R) (a : Fin (n + 1) → R) (B : Fin n → R)
    (L : Fin n → Fin (n + 1) → R) :
    (uniformScaledMatrix H a B L).det = (uniformScaledReduced H a L).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const (c := Fin.cases 0 B) (k := 0)
  · simp
  · intro i j
    refine Fin.cases ?_ (fun r => ?_) i
    · simp [uniformScaledMatrix, uniformScaledReduced]
    · simp [uniformScaledMatrix, uniformScaledReduced]

/-- **The scaling factors out.** -/
theorem uniformScaledReduced_det {n : ℕ} (H : R) (a : Fin (n + 1) → R)
    (L : Fin n → Fin (n + 1) → R) :
    (uniformScaledReduced H a L).det = H ^ n * (uniformBordered a L).det := by
  classical
  have hrow : uniformScaledReduced H a L
      = Matrix.of fun i j => (Fin.cases (1 : R) (fun _ => H) i) * (uniformBordered a L) i j := by
    funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · simp [uniformScaledReduced, uniformBordered]
    · simp [uniformScaledReduced, uniformBordered]
  rw [hrow, Matrix.det_mul_column]
  congr 1
  rw [Fin.prod_univ_succ]
  simp

/-- **The determinant of a uniformly scaled Jacobian.** -/
theorem uniformScaledMatrix_det {n : ℕ} (H : R) (a : Fin (n + 1) → R) (B : Fin n → R)
    (L : Fin n → Fin (n + 1) → R) :
    (uniformScaledMatrix H a B L).det = H ^ n * (uniformBordered a L).det := by
  rw [uniformScaledMatrix_det_eq_reduced, uniformScaledReduced_det]

end GaloisForLFunctions.HTGeometry
