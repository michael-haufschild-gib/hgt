import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolSpectralDifferentialUniversalityLaw
import GaloisForLFunctions.RHTower.DSSDeterminant

/-!
# Differential null-mode holography for flat matrix principal laws

Flat principal-symbol transport conserves the normalized characteristic polynomial throughout the
filtration.  The finite DSS determinant criterion turns its zero root into an actual nontrivial
null mode at every layer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {L g : Type*} [Field L] [Algebra ℂ L] [Differential L]

/-- **Matrix-principal differential null-mode holography universality law.**  A direction of a
flat realized complex matrix principal law is differentially dependent exactly when every
normalized filtration layer admits a nonzero null vector. -/
theorem matrixPrincipalLowerLaw_differentialDependent_iff_everyLayer_nontrivialNullMode
    {d : ℕ}
    (source : Fin d → L) (target : g → Fin d → L)
    (symbol : ℕ → g → Matrix (Fin d) (Fin d) ℂ)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw
      (fun n i ↦ differentialJet n (source i))
      (fun n i ↦ differentialJet n (target A i))
      (fun n ↦ symbol n A))
    (hsource : DifferentialIndependent ℂ source)
    (A : g) :
    A ∈ matrixDifferentialDependentSet (K := ℂ) target ↔
      ∀ n, ∃ v : Fin d → ℂ, v ≠ 0 ∧
        (normalizedMatrixPrincipalSymbol symbol A₀ n A).mulVec v = 0 := by
  have hspec :=
    matrixPrincipalLowerLaw_spectralDifferentialHorizon
      source target symbol hflat A₀ hA₀ hlaw hsource
  constructor
  · intro hdep n
    apply (GaloisForLFunctions.matrix_nontrivial_kernel_iff_det_eq_zero
      (normalizedMatrixPrincipalSymbol symbol A₀ n A)).2
    have hroot0 :
        (matrixPrincipalSpectralPolynomial symbol A₀ 0 A).IsRoot 0 :=
      (hspec.2 A).mp hdep
    have hrootn :
        (matrixPrincipalSpectralPolynomial symbol A₀ n A).IsRoot 0 := by
      rw [hspec.1 n A]
      exact hroot0
    rw [Polynomial.IsRoot] at hrootn
    simp only [matrixPrincipalSpectralPolynomial, Matrix.eval_charpoly] at hrootn
    have hscalarZero : Matrix.scalar (Fin d) (0 : ℂ) = 0 := by
      ext i j
      simp [Matrix.scalar_apply]
    rw [hscalarZero, zero_sub, Matrix.det_neg] at hrootn
    exact (mul_eq_zero.mp hrootn).resolve_left (by simp)
  · intro hall
    apply (hspec.2 A).mpr
    rw [Polynomial.IsRoot]
    have hdet :
        (normalizedMatrixPrincipalSymbol symbol A₀ 0 A).det = 0 :=
      (GaloisForLFunctions.matrix_nontrivial_kernel_iff_det_eq_zero
        (normalizedMatrixPrincipalSymbol symbol A₀ 0 A)).mp (hall 0)
    simp only [matrixPrincipalSpectralPolynomial, Matrix.eval_charpoly]
    have hscalarZero : Matrix.scalar (Fin d) (0 : ℂ) = 0 := by
      ext i j
      simp [Matrix.scalar_apply]
    rw [hscalarZero, zero_sub, Matrix.det_neg, hdet, mul_zero]

end

end GaloisForLFunctions.HTGeometry
