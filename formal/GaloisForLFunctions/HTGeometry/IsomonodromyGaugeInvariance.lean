import GaloisForLFunctions.HTGeometry.MatrixLogarithmicDerivative

/-!
# Isomonodromy is a gauge invariant

A gauge transformation `σ(T) A = A' T` of a difference system carries a compatible connection
`σ(B) A = δA + A B` to a compatible connection of the transformed system, namely the `B'` with
`B' T = δT + T B`.  The identity is proved after clearing `T`, so no invertibility is needed:

`(σ(B') A' - A' B') T = δA' T`.

Solvability of the integrability equation is therefore a property of the difference module and not
of the chosen basis.
-/

open scoped Differential
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

theorem matrixDeriv_map (σ : R →+* R)
    (hσδ : ∀ x : R, σ (Differential.deriv x) = Differential.deriv (σ x))
    {m n : Type*} (M : Matrix m n R) :
    matrixDeriv (M.map σ) = (matrixDeriv M).map σ := by
  ext i j
  simp only [matrixDeriv_apply, Matrix.map_apply]
  exact (hσδ (M i j)).symm

/-- **Isomonodromy is gauge invariant**, in the form with `T` cleared. -/
theorem isomonodromy_gauge_mul {n : Type*} [Fintype n]
    (σ : R →+* R) (hσδ : ∀ x : R, σ (Differential.deriv x) = Differential.deriv (σ x))
    (A A' B B' T : Matrix n n R)
    (hgauge : T.map σ * A = A' * T)
    (hiso : B.map σ * A = matrixDeriv A + A * B)
    (hB' : B' * T = matrixDeriv T + T * B) :
    (B'.map σ * A' - A' * B') * T = matrixDeriv A' * T := by
  have hd : (matrixDeriv T).map σ * A + T.map σ * matrixDeriv A
      = matrixDeriv A' * T + A' * matrixDeriv T := by
    have h := congrArg matrixDeriv hgauge
    rw [matrixDeriv_mul, matrixDeriv_mul, matrixDeriv_map σ hσδ] at h
    exact h
  have hmapadd : ∀ a₁ a₂ : R, σ (a₁ + a₂) = σ a₁ + σ a₂ := fun a₁ a₂ => map_add σ a₁ a₂
  have step1 : (B'.map σ * A' - A' * B') * T
      = B'.map σ * (A' * T) - A' * (B' * T) := by
    rw [sub_mul, mul_assoc, mul_assoc]
  have step2 : B'.map σ * (A' * T)
      = (matrixDeriv T).map σ * A + T.map σ * (B.map σ * A) := by
    rw [← hgauge, ← mul_assoc, ← Matrix.map_mul, hB', Matrix.map_add _ hmapadd,
      Matrix.map_mul, add_mul, mul_assoc]
  have step3 : A' * (B' * T)
      = A' * matrixDeriv T + T.map σ * (A * B) := by
    rw [hB', mul_add, ← mul_assoc, ← hgauge, mul_assoc]
  have hfinal : (matrixDeriv T).map σ * A + T.map σ * matrixDeriv A - A' * matrixDeriv T
      = matrixDeriv A' * T := by
    rw [hd]
    abel
  rw [step1, step2, step3, hiso, mul_add, ← hfinal]
  abel

omit [Differential R] in
/-- A ring hom sends the identity matrix to the identity matrix. -/
theorem matrix_map_one (σ : R →+* R) {n : Type*} [DecidableEq n] :
    (1 : Matrix n n R).map σ = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split
  · exact map_one σ
  · exact map_zero σ

/-- The image of an invertible matrix under a ring hom is invertible. -/
@[reducible] def invertibleMapRingHom (σ : R →+* R) {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n R) [Invertible T] : Invertible (T.map σ) where
  invOf := (⅟T).map σ
  invOf_mul_self := by rw [← Matrix.map_mul, invOf_mul_self]; exact matrix_map_one σ
  mul_invOf_self := by rw [← Matrix.map_mul, mul_invOf_self]; exact matrix_map_one σ

omit [Differential R] in
/-- The inverse gauge. -/
theorem gauge_invOf {n : Type*} [Fintype n] [DecidableEq n] (σ : R →+* R)
    (A A' T : Matrix n n R) [Invertible T] [Invertible (T.map σ)]
    (hmapinv : (⅟T).map σ = ⅟(T.map σ))
    (hgauge : T.map σ * A = A' * T) :
    (⅟T).map σ * A' = A * ⅟T := by
  rw [hmapinv]
  have h1 : A = ⅟(T.map σ) * (A' * T) := by
    rw [← hgauge, ← mul_assoc, invOf_mul_self, one_mul]
  rw [h1, mul_assoc, mul_assoc, mul_invOf_self, mul_one]

/-- **Isomonodromy transfers back along a gauge**, when the gauge is invertible. -/
theorem isomonodromy_of_gauge {n : Type*} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (hσδ : ∀ x : R, σ (Differential.deriv x) = Differential.deriv (σ x))
    (A A' B' T : Matrix n n R) [Invertible T] [Invertible (T.map σ)]
    (hmapinv : (⅟T).map σ = ⅟(T.map σ))
    (hgauge : T.map σ * A = A' * T)
    (hiso : B'.map σ * A' = matrixDeriv A' + A' * B') :
    ∃ B : Matrix n n R, B.map σ * A = matrixDeriv A + A * B := by
  refine ⟨(matrixDeriv (⅟T) + ⅟T * B') * T, ?_⟩
  have hrev : (⅟T).map σ * A' = A * ⅟T := gauge_invOf σ A A' T hmapinv hgauge
  have hB'' : ((matrixDeriv (⅟T) + ⅟T * B') * T) * ⅟T = matrixDeriv (⅟T) + ⅟T * B' := by
    rw [mul_assoc, mul_invOf_self, mul_one]
  have hkey := isomonodromy_gauge_mul σ hσδ A' A B' ((matrixDeriv (⅟T) + ⅟T * B') * T) (⅟T)
    hrev hiso hB''
  have hcancel : ∀ X Y : Matrix n n R, X * ⅟T = Y * ⅟T → X = Y := by
    intro X Y h
    have := congrArg (fun Z : Matrix n n R => Z * T) h
    simpa only [mul_assoc, invOf_mul_self, mul_one] using this
  have := hcancel _ _ hkey
  rw [sub_eq_iff_eq_add] at this
  rw [this]

end

end GaloisForLFunctions.HTGeometry
