import GaloisForLFunctions.HTGeometry.ColorGramMinkowskiCone

/-!
# A weak half-turn moves a genuine colour-Gram light ray

The same right `SU(2)` that acts on the two columns of a `3 × 2` event acts by conjugation on its
Hermitian Gram matrix.  This file strengthens the same-corner weak--Lorentz obstruction by using a
positive-semidefinite Gram matrix rather than an indefinite Pauli witness.

The explicit special-unitary half-turn `diag(i, -i)` sends the future-null Gram matrix

```
[1  1]        [ 1  -1]
[1  1]   to   [-1   1].
```

Both matrices arise along the right orbit of one event supported on a single colour row, so both
are Lorentz-null.  Thus this `SU(2)` acts nontrivially inside the actual colour-Gram future cone.  It
cannot simultaneously be a pointwise-internal weak kernel on that same cone.

This is a finite representation obstruction.  It does not exclude a distinct external Lorentz
action, a noninvertible weak-to-Lorentz interface, or a theory that physically identifies weak and
spatial rotations and survives experiment.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Special-unitary half-turn acting on the right two-dimensional event factor. -/
def colorGramWeakHalfTurn : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0;
     0, -Complex.I]

/-- Conjugation action on a `2 × 2` Gram matrix. -/
def colorGramConjugation
    (U G : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  U * G * Uᴴ

/-- The half-turn is unitary. -/
theorem colorGramWeakHalfTurn_conjTranspose_mul_self :
    colorGramWeakHalfTurnᴴ * colorGramWeakHalfTurn = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorGramWeakHalfTurn, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.I_mul_I]

/-- The half-turn has determinant one. -/
theorem colorGramWeakHalfTurn_det :
    colorGramWeakHalfTurn.det = 1 := by
  simp [colorGramWeakHalfTurn, Matrix.det_fin_two, Complex.I_mul_I]

/-- Right multiplication preserves support on one colour row. -/
theorem singleColorEvent_mul
    (H : Fin 2 → ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    singleColorEvent H * V =
      singleColorEvent (fun j => ∑ k, H k * V k j) := by
  ext i j
  fin_cases i <;>
    simp [singleColorEvent, Matrix.mul_apply, Fin.sum_univ_two]

/-- The entire right orbit of a one-row event remains Lorentz-null. -/
theorem singleColorEvent_right_orbit_lorentz_null
    (H : Fin 2 → ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    colorGramLorentzMassSq (singleColorEvent H * V) = 0 := by
  rw [singleColorEvent_mul]
  exact singleColorEvent_lorentz_null _

/-- Explicit one-row event whose Gram vector is the future light ray `(1, 1, 0, 0)`. -/
def weakLockedColorEvent : ColorEventMatrix :=
  singleColorEvent ![1, 1]

/-- Positive-semidefinite future-null matrix before the half-turn. -/
def colorGramFutureNullPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 1;
     1, 1]

/-- Positive-semidefinite future-null matrix after the half-turn. -/
def colorGramFutureNullMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, -1;
     -1, 1]

/-- The explicit event has the positive future-null Gram matrix with positive off-diagonal entry. -/
theorem weakLockedColorEvent_gram :
    colorGramMatrix weakLockedColorEvent = colorGramFutureNullPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorGramMatrix, weakLockedColorEvent, singleColorEvent,
      colorGramFutureNullPlus, Matrix.mul_apply]

/-- The explicit event lies on the Lorentz-null boundary. -/
theorem weakLockedColorEvent_lorentz_null :
    colorGramLorentzMassSq weakLockedColorEvent = 0 := by
  exact singleColorEvent_lorentz_null _

/-- The special-unitary half-turn reverses the light ray's first spatial coordinate. -/
theorem colorGramWeakHalfTurn_conjugates_futureNullPlus :
    colorGramConjugation colorGramWeakHalfTurn colorGramFutureNullPlus =
      colorGramFutureNullMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorGramConjugation, colorGramWeakHalfTurn, colorGramFutureNullPlus,
      colorGramFutureNullMinus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.I_mul_I]

/-- The two future-null rays are distinct. -/
theorem colorGramFutureNullMinus_ne_plus :
    colorGramFutureNullMinus ≠ colorGramFutureNullPlus := by
  intro h
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [colorGramFutureNullMinus, colorGramFutureNullPlus] at h01

/-- The half-turn acts nontrivially on a genuine positive colour-Gram matrix. -/
theorem colorGramWeakHalfTurn_moves_futureGram :
    colorGramConjugation colorGramWeakHalfTurn (colorGramMatrix weakLockedColorEvent) ≠
      colorGramMatrix weakLockedColorEvent := by
  rw [weakLockedColorEvent_gram, colorGramWeakHalfTurn_conjugates_futureNullPlus]
  exact colorGramFutureNullMinus_ne_plus

/-- The corresponding right action on the underlying event changes its Gram future. -/
theorem colorGramWeakHalfTurn_moves_futureGram_via_event :
    colorGramMatrix (weakLockedColorEvent * colorGramWeakHalfTurnᴴ) ≠
      colorGramMatrix weakLockedColorEvent := by
  rw [colorGramMatrix_right_covariant]
  exact colorGramWeakHalfTurn_moves_futureGram

/-- The special-unitary right action cannot lie in the pointwise kernel of the colour-Gram map. -/
theorem colorGramWeakHalfTurn_not_in_pointwiseKernel :
    ¬ ∀ X : ColorEventMatrix,
      colorGramMatrix (X * colorGramWeakHalfTurnᴴ) = colorGramMatrix X := by
  intro h
  exact colorGramWeakHalfTurn_moves_futureGram_via_event (h weakLockedColorEvent)

/-- The moved event is still Lorentz-null: the half-turn rotates inside the future light cone. -/
theorem colorGramWeakHalfTurn_moved_event_lorentz_null :
    colorGramLorentzMassSq
      (weakLockedColorEvent * colorGramWeakHalfTurnᴴ) = 0 := by
  exact singleColorEvent_right_orbit_lorentz_null _ _

end GaloisForLFunctions.HTGeometry
