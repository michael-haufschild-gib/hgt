import GaloisForLFunctions.HTGeometry.DifferentialTangentSubmodule
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The adjoint action preserves the tangent space

A dual-number matrix `p + εX` multiplies by the rule `(p + εX)(q + εY) = pq + ε(pY + Xq)`, so
conjugating `1 + εX` by the constant matrix `g` — with `g` and its inverse both in the zero set —
gives `1 + ε(g X g⁻¹)`.  If the zero set is closed under multiplication over the dual numbers, that
matrix is again in the zero set, so `g X g⁻¹` is again a tangent direction at the identity.

That is `Ad`-stability of the Lie algebra of a differential algebraic group, and it is the step
between "the tangent space is a module over the constants" and "the tangent space is closed under
the bracket": the bracket is the derivative of `Ad` along a one-parameter family.

* `dualMatrix`, `dualMatrix_mul`, `dualMatrix_one`;
* `evalOver_inl` — the base embeds through the evaluation;
* `mem_zeroSet_dualMatrix_inl`;
* `adjoint_mem_tangent_of_zeroSet`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [CommRing C] [Differential C]

/-! ### Dual-number matrices -/

/-- The dual-number matrix `p + εX`. -/
def dualMatrix (p X : Matrix (Fin 2) (Fin 2) C) : Matrix (Fin 2) (Fin 2) (DualNumber C) :=
  fun i j => dualMk (p i j) (X i j)

omit [Differential C] in
@[simp] theorem dualMatrix_apply (p X : Matrix (Fin 2) (Fin 2) C) (i j : Fin 2) :
    dualMatrix p X i j = dualMk (p i j) (X i j) := rfl

omit [Differential C] in
theorem dualMk_mul (a b c d : C) :
    dualMk a b * dualMk c d = dualMk (a * c) (a * d + b * c) := by
  apply TrivSqZeroExt.ext <;> simp [dualMk]

omit [Differential C] in
/-- **Dual-number matrices multiply by the first-order product rule.** -/
theorem dualMatrix_mul (p X q Y : Matrix (Fin 2) (Fin 2) C) :
    dualMatrix p X * dualMatrix q Y = dualMatrix (p * q) (p * Y + X * q) := by
  refine Matrix.ext fun i j => TrivSqZeroExt.ext ?_ ?_
  · simp [Matrix.mul_apply, dualMatrix, dualMk, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, dualMatrix, dualMk, Fin.sum_univ_two]
    ring

/-! ### The base embeds through the evaluation -/

theorem differentialJet_zero_elt' (n : ℕ) : differentialJet n (0 : C) = 0 := by
  induction n with
  | zero => rw [differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, ih, map_zero]

theorem differentialJet_inl (n : ℕ) (a : C) :
    differentialJet n (TrivSqZeroExt.inl a : DualNumber C)
      = TrivSqZeroExt.inl (differentialJet n a) := by
  rw [differentialJet_dual]
  apply TrivSqZeroExt.ext
  · simp
  · simp [differentialJet_zero_elt']

theorem evalOver_inl {ι : Type*} (x : ι → C) (P : DifferentialPolynomial ι C) :
    differentialPolynomialEvalOver (K := C)
        (fun i => (TrivSqZeroExt.inl (x i) : DualNumber C)) P
      = TrivSqZeroExt.inl (differentialPolynomialEvalOver (K := C) x P) := by
  have key : differentialPolynomialEvalOver (K := C)
        (fun i => (TrivSqZeroExt.inl (x i) : DualNumber C))
      = (TrivSqZeroExt.inlAlgHom C C C).comp
          (differentialPolynomialEvalOver (K := C) x) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [differentialPolynomialEvalOver_X, AlgHom.comp_apply, differentialPolynomialEvalOver_X]
    rw [show (TrivSqZeroExt.inlAlgHom C C C) (differentialJet v.2 (x v.1))
      = TrivSqZeroExt.inl (differentialJet v.2 (x v.1)) from rfl]
    exact differentialJet_inl v.2 (x v.1)
  rw [key, AlgHom.comp_apply]
  rfl

/-! ### The adjoint action -/

variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- The matrices over a differential `C`-algebra annihilated by every member of `S`. -/
def matrixZeroSet {A : Type*} [CommRing A] [Algebra C A] [Differential A] :
    Set (Matrix (Fin 2) (Fin 2) A) :=
  {g | ∀ P ∈ S, differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => g q.1 q.2) P = 0}

/-- A constant matrix of the zero set stays in it over the dual numbers. -/
theorem mem_zeroSet_dualMatrix_inl {g : Matrix (Fin 2) (Fin 2) C} (hg : g ∈ matrixZeroSet S) :
    dualMatrix g 0 ∈ matrixZeroSet (C := C) (A := DualNumber C) S := by
  intro P hP
  have hpt : (fun q : Fin 2 × Fin 2 => dualMatrix g 0 q.1 q.2)
      = fun q : Fin 2 × Fin 2 => (TrivSqZeroExt.inl (g q.1 q.2) : DualNumber C) := by
    funext q
    rw [dualMatrix_apply, dualMk]
    simp
  rw [hpt, evalOver_inl, hg P hP]
  simp

/-- **The adjoint action preserves the tangent directions at the identity.** -/
theorem adjoint_mem_tangent_of_zeroSet
    (hmul : ∀ u ∈ matrixZeroSet (C := C) (A := DualNumber C) S,
      ∀ v ∈ matrixZeroSet (C := C) (A := DualNumber C) S,
      u * v ∈ matrixZeroSet (C := C) (A := DualNumber C) S)
    {g h : Matrix (Fin 2) (Fin 2) C} (hg : g ∈ matrixZeroSet S) (hh : h ∈ matrixZeroSet S)
    (hgh : g * h = 1) {X : Matrix (Fin 2) (Fin 2) C}
    (hX : dualMatrix 1 X ∈ matrixZeroSet (C := C) (A := DualNumber C) S) :
    dualMatrix 1 (g * X * h) ∈ matrixZeroSet (C := C) (A := DualNumber C) S := by
  have hprod : dualMatrix g 0 * dualMatrix 1 X * dualMatrix h 0
      = dualMatrix 1 (g * X * h) := by
    rw [dualMatrix_mul, dualMatrix_mul]
    congr 1
    · rw [mul_one, hgh]
    · simp only [mul_one, add_zero, mul_zero, zero_add, mul_assoc]
  rw [← hprod]
  exact hmul _ (hmul _ (mem_zeroSet_dualMatrix_inl S hg) _ hX) _
    (mem_zeroSet_dualMatrix_inl S hh)

end

end GaloisForLFunctions.HTGeometry
