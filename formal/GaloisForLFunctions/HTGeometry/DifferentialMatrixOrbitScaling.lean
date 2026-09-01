import GaloisForLFunctions.HTGeometry.MatrixTranslationZeroSet
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialSubfieldDescent

/-!
# Scalar differential relations and dense matrix orbits

A scalar relation on the first entry of `Y` is rewritten as a matrix differential polynomial on
the right orbit `Yg`.  Coefficientwise linear functionals descend that polynomial to the constant
field.  Membership of every determinant-one diagonal matrix in the differential zero set then
forces the original relation to vanish at every nonzero constant multiple of `Y₀₀`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

attribute [local instance] differentialPolynomialOverDifferential

universe u

variable {C K R : Type u} [Field C] [Field K] [CommRing R]
  [Algebra C K] [Algebra K R] [Algebra C R] [IsScalarTower C K R]
  [Differential C] [Differential K] [Differential R]
  [DifferentialAlgebra C K] [DifferentialAlgebra K R] [DifferentialAlgebra C R]

/-- Matrix differential polynomial obtained by inserting the first entry of `Yg` into a scalar
differential polynomial. -/
def firstEntryRightOrbitPolynomial
    (Y : Matrix (Fin 2) (Fin 2) R) (P : DifferentialPolynomial Unit K) :
    DifferentialPolynomial (Fin 2 × Fin 2) R :=
  matrixLeftTranslate Y
    (differentialRename (fun _ : Unit => (0, 0))
      (differentialCoeffExtend (ι := Unit) (F := K) (L := R) P))

theorem eval_firstEntryRightOrbitPolynomial
    (Y : Matrix (Fin 2) (Fin 2) R) (P : DifferentialPolynomial Unit K)
    (g : Matrix (Fin 2) (Fin 2) C) :
    differentialPolynomialEvalOver (K := R)
        (fun q : Fin 2 × Fin 2 => algebraMap C R (g q.1 q.2))
        (firstEntryRightOrbitPolynomial Y P) =
      differentialPolynomialEvalOver (K := K)
        (fun _ : Unit => ∑ l : Fin 2, Y 0 l * algebraMap C R (g l 0)) P := by
  let gR : Matrix (Fin 2) (Fin 2) R := g.map (algebraMap C R)
  change differentialPolynomialEvalOver (K := R)
      (fun q : Fin 2 × Fin 2 => gR q.1 q.2)
      (firstEntryRightOrbitPolynomial Y P) = _
  rw [firstEntryRightOrbitPolynomial,
    evalOver_matrixLeftTranslate Y gR,
    differentialPolynomialEvalOver_differentialRename,
    differentialPolynomialEvalOver_differentialCoeffExtend]
  congr 1

/-- Standard determinant-one diagonal matrix. -/
def differentialScalingMatrix (c : C) : Matrix (Fin 2) (Fin 2) C :=
  !![c, 0; 0, c⁻¹]

theorem differentialScalingMatrix_det {c : C} (hc : c ≠ 0) :
    (differentialScalingMatrix c).det = 1 := by
  simp [differentialScalingMatrix, Matrix.det_fin_two, hc]

theorem firstEntryRightOrbitPolynomial_scaling_eval
    (Y : Matrix (Fin 2) (Fin 2) R) (P : DifferentialPolynomial Unit K)
    (c : C) :
    differentialPolynomialEvalOver (K := R)
        (fun q : Fin 2 × Fin 2 =>
          algebraMap C R (differentialScalingMatrix c q.1 q.2))
        (firstEntryRightOrbitPolynomial Y P) =
      differentialPolynomialEvalOver (K := K)
        (fun _ : Unit => Y 0 0 * algebraMap C R c) P := by
  rw [eval_firstEntryRightOrbitPolynomial]
  simp [differentialScalingMatrix, Fin.sum_univ_two]

/-- Dense determinant-one matrix orbits propagate a scalar differential relation to every
nonzero constant multiple of the first fundamental entry. -/
theorem differentialRelation_scaled_of_matrixZeroSet
    (Y : Matrix (Fin 2) (Fin 2) R) (P : DifferentialPolynomial Unit K)
    (H : Set (Matrix (Fin 2) (Fin 2) C))
    (horbit : ∀ g ∈ H, g.det = 1 →
      differentialPolynomialEvalOver (K := K)
        (fun _ : Unit => ∑ l : Fin 2, Y 0 l * algebraMap C R (g l 0)) P = 0)
    (hclosure : ∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 →
      g ∈ matrixZeroSet (C := C) (A := C)
        (matrixVanishingIdeal {h ∈ H | h.det = 1}))
    (c : C) (hc : c ≠ 0) :
    differentialPolynomialEvalOver (K := K)
      (fun _ : Unit => Y 0 0 * algebraMap C R c) P = 0 := by
  let G := firstEntryRightOrbitPolynomial Y P
  have hCR : ∀ a : C, Differential.deriv (algebraMap C R a) =
      algebraMap C R (Differential.deriv a) := DifferentialAlgebra.deriv_algebraMap
  have hpush : ∀ ψ : R →ₗ[C] C, linearPush ψ G ∈
      matrixVanishingIdeal {h ∈ H | h.det = 1} := by
    intro ψ g hg
    rw [evalOver_linearPush ψ hCR
      (fun q : Fin 2 × Fin 2 => g q.1 q.2) G]
    have hGzero : differentialPolynomialEvalOver (K := R)
        (fun q : Fin 2 × Fin 2 => algebraMap C R (g q.1 q.2)) G = 0 := by
      rw [show G = firstEntryRightOrbitPolynomial Y P by rfl,
        eval_firstEntryRightOrbitPolynomial]
      exact horbit g hg.1 hg.2
    rw [hGzero, map_zero]
  have hdiag := hclosure (differentialScalingMatrix c)
    (differentialScalingMatrix_det hc)
  have hdual : ∀ ψ : R →ₗ[C] C,
      ψ (differentialPolynomialEvalOver (K := R)
        (fun q : Fin 2 × Fin 2 =>
          algebraMap C R (differentialScalingMatrix c q.1 q.2)) G) = 0 := by
    intro ψ
    have hz := hdiag (linearPush ψ G) (hpush ψ)
    rw [evalOver_linearPush ψ hCR
      (fun q : Fin 2 × Fin 2 => differentialScalingMatrix c q.1 q.2) G] at hz
    exact hz
  have hGdiag : differentialPolynomialEvalOver (K := R)
      (fun q : Fin 2 × Fin 2 =>
        algebraMap C R (differentialScalingMatrix c q.1 q.2)) G = 0 := by
    by_contra hne
    obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero C hne
    exact hψ (hdual ψ)
  rw [show G = firstEntryRightOrbitPolynomial Y P by rfl,
    firstEntryRightOrbitPolynomial_scaling_eval] at hGdiag
  exact hGdiag

end

end GaloisForLFunctions.HTGeometry
