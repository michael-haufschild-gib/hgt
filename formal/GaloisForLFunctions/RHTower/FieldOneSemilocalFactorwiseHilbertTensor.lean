import GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatL2Density
import GaloisForLFunctions.RHTower.L2HilbertTensorProduct

/-!
# Factorwise Hilbert tensor realization of semilocal Bruhat space

This module compares the independently defined Hilbert completion of the algebraic semilocal
Bruhat space with the Hilbert tensor product of real and finite-adele `L²` factors.  The canonical
linear isometric equivalence agrees on pure Bruhat tensors with tensoring the two factor maps.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory
open scoped TensorProduct

def fieldOneSemilocalProductL2Equiv :
    Lp ℂ 2 ((volume : Measure ℝ).prod fieldOneFiniteAdeleAddHaar) ≃ₗᵢ[ℂ]
      Lp ℂ 2 fieldOneSemilocalAddHaar :=
  LinearIsometryEquiv.ofSurjective
    fieldOneSemilocalProductToExistingL2
    fieldOneSemilocalProductToExistingL2_surjective

abbrev FieldOneSemilocalFactorwiseHilbertTensor :=
  L2HilbertTensorProduct
    (α := ℝ) (β := FieldOneFiniteAdele)
    (μ := (volume : Measure ℝ))
    (ν := fieldOneFiniteAdeleAddHaar)

def fieldOneSemilocalBruhatCompletionEquivFactorwiseHilbertTensor :
    FieldOneSemilocalBruhatHilbertCompletion ≃ₗᵢ[ℂ]
      FieldOneSemilocalFactorwiseHilbertTensor :=
  fieldOneSemilocalBruhatCompletionEquivL2.trans
    (fieldOneSemilocalProductL2Equiv.symm.trans
      (l2HilbertTensorProductEquiv
        (α := ℝ) (β := FieldOneFiniteAdele)
        (μ := (volume : Measure ℝ))
        (ν := fieldOneFiniteAdeleAddHaar)).symm)

@[simp]
theorem fieldOneSemilocalBruhatCompletionEquivFactorwiseHilbertTensor_tmul
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    fieldOneSemilocalBruhatCompletionEquivFactorwiseHilbertTensor
        ((f ⊗ₜ[ℂ] g : FieldOneSemilocalBruhatSchwartz) :
          FieldOneSemilocalBruhatHilbertCompletion) =
      ((fieldOneArchimedeanSchwartzToL2 f ⊗ₜ[ℂ]
          fieldOneFiniteBruhatToL2Linear g :
        Lp ℂ 2 (volume : Measure ℝ) ⊗[ℂ]
          Lp ℂ 2 fieldOneFiniteAdeleAddHaar) :
        FieldOneSemilocalFactorwiseHilbertTensor) := by
  apply
    (l2HilbertTensorProductEquiv
      (α := ℝ) (β := FieldOneFiniteAdele)
      (μ := (volume : Measure ℝ))
      (ν := fieldOneFiniteAdeleAddHaar)).injective
  simp only [
    fieldOneSemilocalBruhatCompletionEquivFactorwiseHilbertTensor,
    LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply,
    l2HilbertTensorProductEquiv_coe]
  apply fieldOneSemilocalProductL2Equiv.injective
  change
    fieldOneSemilocalProductL2Equiv
        (fieldOneSemilocalProductL2Equiv.symm
          (fieldOneSemilocalBruhatCompletionEquivL2
            ((f ⊗ₜ[ℂ] g : FieldOneSemilocalBruhatSchwartz) :
              FieldOneSemilocalBruhatHilbertCompletion))) =
      fieldOneSemilocalProductL2Equiv
        (l2TensorToProduct
          (fieldOneArchimedeanSchwartzToL2 f ⊗ₜ[ℂ]
            fieldOneFiniteBruhatToL2Linear g))
  rw [LinearIsometryEquiv.apply_symm_apply]
  rw [fieldOneSemilocalBruhatCompletionEquivL2_coe]
  rw [fieldOneSemilocalBruhatToL2_eq_transported]
  rfl

end

end GaloisForLFunctions.RHTower
