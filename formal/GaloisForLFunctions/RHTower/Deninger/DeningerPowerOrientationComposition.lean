import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPowerOrientation
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Composition law for the monic power-map orientations

The presentation of the `n`-th power map is `x^n - y`, whose relative differential is
`n x^(n-1)`.  Composing the presentations of the `n`-th and the `m`-th power map gives the
iterated presentation with cotangent matrix `[[a, 0], [-1, b]]`, `a = n x^(n-1)`,
`b = m y^(m-1)`.

Two statements make the composition coherent at determinant-orientation level.  First, the
elementary reduction to `diag(1, a b)` is realized by an explicit pair of unimodular matrices
factored as `L(a) = D S E(a)` and `R(b) = F(b)`, so the determinant orientation is unchanged.
Second, on the locus `y = x^n` the residual entry `a b` is exactly the differential
`m n x^(mn-1)` of the direct presentation `x^(mn) - z`.  Hence the induced orientation on
`f_m ∘ f_n` is the direct monic orientation of `f_{mn}`, with no residual unit or sign.

* `deningerPowerOrientationLeft_factor` : `L(a) = D S E(a)`.
* `deningerPowerComposite_derivative` : `(n x^(n-1))(m (x^n)^(m-1)) = mn x^(mn-1)`.
* `deningerPowerIteratedCotangent_composite` : the two statements combined.
-/

namespace RHTower

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

section Elementary

/-- The upper elementary matrix `E(a)`. -/
def deningerPowerElemUpper (a : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, a; 0, 1]

/-- The coordinate swap `S`. -/
def deningerPowerSwap : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, 0]

/-- The first-coordinate reflection `D`. -/
def deningerPowerReflect : Matrix (Fin 2) (Fin 2) R :=
  !![-1, 0; 0, 1]

@[simp] theorem det_deningerPowerElemUpper (a : R) :
    (deningerPowerElemUpper a).det = 1 := by
  simp [deningerPowerElemUpper, Matrix.det_fin_two_of]

@[simp] theorem det_deningerPowerSwap :
    (deningerPowerSwap (R := R)).det = -1 := by
  simp [deningerPowerSwap, Matrix.det_fin_two_of]

@[simp] theorem det_deningerPowerReflect :
    (deningerPowerReflect (R := R)).det = -1 := by
  simp [deningerPowerReflect, Matrix.det_fin_two_of]

/-- The row change is the product of a reflection, a swap and an upper elementary matrix; the
two determinant signs cancel. -/
theorem deningerPowerOrientationLeft_factor (a : R) :
    deningerPowerReflect * deningerPowerSwap * deningerPowerElemUpper a =
      deningerPowerOrientationLeft a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deningerPowerReflect, deningerPowerSwap, deningerPowerElemUpper,
      deningerPowerOrientationLeft, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The column change is an upper elementary matrix. -/
theorem deningerPowerOrientationRight_eq (b : R) :
    deningerPowerOrientationRight b = deningerPowerElemUpper b := rfl

/-- The determinant of the iterated cotangent matrix is the composite differential. -/
@[simp] theorem det_deningerPowerIteratedCotangentMatrix (a b : R) :
    (deningerPowerIteratedCotangentMatrix a b).det = a * b := by
  simp [deningerPowerIteratedCotangentMatrix, Matrix.det_fin_two_of]

/-- The split matrix has the same determinant, so the reduction preserves the orientation. -/
@[simp] theorem det_deningerPowerSplitCotangentMatrix (a b : R) :
    (deningerPowerSplitCotangentMatrix a b).det = a * b := by
  simp [deningerPowerSplitCotangentMatrix, Matrix.det_fin_two_of]

/-- The elementary reduction leaves the determinant orientation unchanged. -/
theorem det_deningerPowerIteratedCotangent_reduction (a b : R) :
    (deningerPowerOrientationLeft a * deningerPowerIteratedCotangentMatrix a b *
        deningerPowerOrientationRight b).det =
      (deningerPowerIteratedCotangentMatrix a b).det := by
  rw [deningerPowerIteratedCotangentMatrix_reduction,
    det_deningerPowerSplitCotangentMatrix, det_deningerPowerIteratedCotangentMatrix]

end Elementary

section Presentation

/-- The monic presentation `x^k - y` of the `k`-th power map. -/
def deningerPowerPoly (k : ℕ) (y : R) : R[X] := X ^ k - C y

/-- The relative differential of the monic power presentation. -/
theorem deningerPowerPoly_derivative (k : ℕ) (y : R) :
    derivative (deningerPowerPoly k y) = C (k : R) * X ^ (k - 1) := by
  rw [deningerPowerPoly, derivative_sub, derivative_X_pow, derivative_C, sub_zero]

/-- The relative differential, evaluated at a point. -/
@[simp] theorem deningerPowerPoly_derivative_eval (k : ℕ) (y x : R) :
    (derivative (deningerPowerPoly k y)).eval x = (k : R) * x ^ (k - 1) := by
  rw [deningerPowerPoly_derivative]
  simp

/-- **The composite differential.**  On the locus `y = x^n`, the product of the two differentials
of the iterated presentation is the differential of the direct presentation of the `mn`-th power
map. -/
theorem deningerPowerComposite_derivative {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (x : R) :
    ((n : R) * x ^ (n - 1)) * ((m : R) * (x ^ n) ^ (m - 1))
      = ((m * n : ℕ) : R) * x ^ (m * n - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hdeg : (M + 1) * (N + 1) - 1 = M * N + M + N := by
    have h : (M + 1) * (N + 1) = M * N + M + N + 1 := by ring
    rw [h, Nat.add_sub_cancel]
  have hx : x ^ N * (x ^ (N + 1)) ^ M = x ^ (M * N + M + N) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, hdeg]
  calc ((N + 1 : ℕ) : R) * x ^ N * (((M + 1 : ℕ) : R) * (x ^ (N + 1)) ^ M)
      = (((N + 1 : ℕ) : R) * ((M + 1 : ℕ) : R)) * (x ^ N * (x ^ (N + 1)) ^ M) := by ring
    _ = (((N + 1 : ℕ) : R) * ((M + 1 : ℕ) : R)) * x ^ (M * N + M + N) := by rw [hx]
    _ = (((M + 1) * (N + 1) : ℕ) : R) * x ^ (M * N + M + N) := by push_cast; ring

/-- **The composition law for the monic presentations.**  The differential of the outer
presentation, evaluated on the locus `y = x^n`, times the differential of the inner presentation
is the differential of the direct presentation of the `mn`-th power map. -/
theorem deningerPowerPoly_derivative_composite {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (x z : R) :
    (derivative (deningerPowerPoly n (x ^ n))).eval x *
        (derivative (deningerPowerPoly m z)).eval (x ^ n)
      = (derivative (deningerPowerPoly (m * n) z)).eval x := by
  rw [deningerPowerPoly_derivative_eval, deningerPowerPoly_derivative_eval,
    deningerPowerPoly_derivative_eval]
  exact deningerPowerComposite_derivative hm hn x

/-- **Orientation coherence of the power correspondences.**  The unimodular elementary reduction
of the iterated cotangent matrix produces the identity block together with the differential of
the direct monic presentation of the `mn`-th power map.  Hence the orientation induced by
composition is the direct monic orientation, with no residual unit or sign. -/
theorem deningerPowerIteratedCotangent_composite {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (x z : R) :
    deningerPowerOrientationLeft ((derivative (deningerPowerPoly n (x ^ n))).eval x) *
          deningerPowerIteratedCotangentMatrix
            ((derivative (deningerPowerPoly n (x ^ n))).eval x)
            ((derivative (deningerPowerPoly m z)).eval (x ^ n)) *
        deningerPowerOrientationRight ((derivative (deningerPowerPoly m z)).eval (x ^ n)) =
      !![1, 0; 0, (derivative (deningerPowerPoly (m * n) z)).eval x] := by
  rw [deningerPowerIteratedCotangentMatrix_reduction,
    deningerPowerSplitCotangentMatrix,
    deningerPowerPoly_derivative_composite hm hn x z]

end Presentation

end

end RHTower
