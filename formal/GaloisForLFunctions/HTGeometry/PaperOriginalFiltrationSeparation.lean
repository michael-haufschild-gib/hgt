import GaloisForLFunctions.HTGeometry.PaperFiberClockGeometry
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.FiltrationSeparation
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.Presentation
import Mathlib.RingTheory.Polynomial.Basic

/-!
The source's signed-weight filtration is exhaustive and separated on the actual
four-variable polynomial algebra. Its distinguished negative-weight generator
maps to the literal source polynomial `f`. The affine zero fibre proves `f` is
a nonunit, discharging the separation theorem's geometric input.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate MvPolynomial

/-- The actual source presentation, before quotienting out its relation. -/
def paperOriginalPresentation : R 5 →ₐ[ℂ] R 4 :=
  Presentation.originalPresentation.toAlgHom.comp (Presentation.mk 0)

theorem paperOriginalPresentation_X_zero : paperOriginalPresentation (X 0) = f :=
  Presentation.originalPresentation_p

theorem paperOriginalPresentation_surjective : Function.Surjective paperOriginalPresentation :=
  Presentation.originalPresentation.surjective.comp
    (Ideal.Quotient.mkₐ_surjective ℂ (Presentation.relationIdeal 0))

/-- The exact zero-fibre theorem supplies noninvertibility, with no premise. -/
theorem paperOriginalPolynomial_not_isUnit : ¬ IsUnit f := by
  have hproper : (Ideal.span ({f} : Set (R 4))) ≠ ⊤ := by
    simpa [fiberIdeal] using (paperFiberIdeal_isPrime 0).ne_top
  exact fun h => hproper (Ideal.span_singleton_eq_top.mpr h)

/-- The signed source-weight filtration transported to the original four variables. -/
def paperOriginalFiltration (d : ℤ) : Submodule ℂ (R 4) :=
  Filtration.imagePiece paperOriginalPresentation d

theorem paperOriginalFiltration_mono : Monotone paperOriginalFiltration :=
  Filtration.imagePiece_mono paperOriginalPresentation

theorem paperOriginalFiltration_exhaustive (p : R 4) :
    ∃ d : ℤ, p ∈ paperOriginalFiltration d :=
  Filtration.exists_mem_imagePiece paperOriginalPresentation
    paperOriginalPresentation_surjective p

/-- Negative filtration depth forces an actual power of `f` as a factor. -/
theorem paperOriginalFiltration_negative_le (r : ℕ) :
    paperOriginalFiltration (-(r : ℤ)) ≤
      (Ideal.span ({f ^ r} : Set (R 4))).restrictScalars ℂ := by
  intro p hp
  apply Ideal.mem_span_singleton.mpr
  simpa only [paperOriginalPresentation_X_zero] using
    Filtration.pow_dvd_of_mem_imagePiece_neg paperOriginalPresentation hp

/-- There is no nonzero residual element at every signed filtration depth. -/
theorem paperOriginalFiltration_separated :
    (⨅ d : ℤ, paperOriginalFiltration d) = ⊥ := by
  apply Filtration.iInf_imagePiece_eq_bot paperOriginalPresentation
  simpa only [paperOriginalPresentation_X_zero] using paperOriginalPolynomial_not_isUnit

theorem paperOriginalFiltration_residual_iff_zero (p : R 4) :
    (∀ d : ℤ, p ∈ paperOriginalFiltration d) ↔ p = 0 := by
  rw [← Submodule.mem_iInf, paperOriginalFiltration_separated]
  rfl

/-- Agreement at every depth detects literal equality of ambient polynomials. -/
theorem paperOriginalFiltration_equal_iff (p q : R 4) :
    (∀ d : ℤ, p - q ∈ paperOriginalFiltration d) ↔ p = q := by
  rw [paperOriginalFiltration_residual_iff_zero, sub_eq_zero]

end GaloisForLFunctions.HTGeometry
