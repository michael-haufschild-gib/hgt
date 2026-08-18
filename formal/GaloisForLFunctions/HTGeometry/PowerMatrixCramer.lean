import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Cramer generation for the powers of an algebra element

For a free algebra with a chosen basis, the determinant of the coordinate matrix of
`1, θ, …, θ^(n-1)` times any element is a polynomial in `θ`.  This is the generation datum required
by the chart of `AlgebraSpectrumCovering`, obtained from Cramer's rule alone — no localization and
no Nakayama.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Matrix

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}

/-- The coordinate matrix of the powers of an element in a chosen basis. -/
noncomputable def powerMatrix (e : Module.Basis (Fin n) A B) (θ : B) : Matrix (Fin n) (Fin n) A :=
  fun i j => e.repr (θ ^ (j : ℕ)) i

/-- **Cramer's rule for the powers of an element.**  The determinant of the coordinate matrix of
`1, θ, …, θ^(n-1)` times a basis vector is a polynomial in `θ`. -/
theorem det_powerMatrix_smul_basis (e : Module.Basis (Fin n) A B) (θ : B) (i : Fin n) :
    (powerMatrix e θ).det • e i =
      ∑ j : Fin n, (algebraMap A B) ((powerMatrix e θ).adjugate j i) * θ ^ (j : ℕ) := by
  classical
  apply e.ext_elem
  intro k
  have hrhs : e.repr (∑ j : Fin n, (algebraMap A B) ((powerMatrix e θ).adjugate j i) *
      θ ^ (j : ℕ)) k = ∑ j : Fin n, (powerMatrix e θ).adjugate j i * (powerMatrix e θ) k j := by
    rw [map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Algebra.smul_def, map_smul]
    simp [powerMatrix]
  rw [hrhs]
  have hmul : ∑ j : Fin n, (powerMatrix e θ).adjugate j i * (powerMatrix e θ) k j =
      ((powerMatrix e θ) * (powerMatrix e θ).adjugate) k i := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hmul, Matrix.mul_adjugate]
  simp [Matrix.smul_apply, Matrix.one_apply, Module.Basis.repr_self, Finsupp.single_apply,
    eq_comm]

/-- **Cramer generation.**  The determinant of the coordinate matrix of the powers of `θ` times any
element of the algebra is a polynomial in `θ`. -/
theorem exists_aeval_of_det_smul (e : Module.Basis (Fin n) A B) (θ : B) (b : B) :
    ∃ q : A[X], (powerMatrix e θ).det • b = Polynomial.aeval θ q := by
  classical
  refine ⟨∑ j : Fin n,
    Polynomial.C (∑ i : Fin n, e.repr b i * (powerMatrix e θ).adjugate j i) * X ^ (j : ℕ), ?_⟩
  have hb : b = ∑ i : Fin n, e.repr b i • e i := (e.sum_repr b).symm
  calc (powerMatrix e θ).det • b
      = ∑ i : Fin n, e.repr b i • ((powerMatrix e θ).det • e i) := by
        conv_lhs => rw [hb]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    _ = ∑ i : Fin n, e.repr b i •
          (∑ j : Fin n, (algebraMap A B) ((powerMatrix e θ).adjugate j i) * θ ^ (j : ℕ)) := by
        exact Finset.sum_congr rfl fun i _ => by rw [det_powerMatrix_smul_basis]
    _ = Polynomial.aeval θ (∑ j : Fin n,
          Polynomial.C (∑ i : Fin n, e.repr b i * (powerMatrix e θ).adjugate j i) *
            X ^ (j : ℕ)) := by
        rw [map_sum]
        simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, map_sum,
          Algebra.smul_def, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

end GaloisForLFunctions.HTGeometry
