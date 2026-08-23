import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The common cyclic energy completion

Under the cyclic transition the semilocal and archimedean spectral measures are uniformly
equivalent: their densities are trapped between two positive constants.  Weighted energies are
therefore comparable term by term, so the two number-form domains coincide with equivalent norms.
On that common energy completion, any bounded symmetric sesquilinear form -- in particular the
cyclic prolate constraint -- has a canonical bounded self-adjoint representative.
-/

namespace RHTower

open MeasureTheory

/-- **Uniformly equivalent weights give comparable energies.**  A weight trapped between two
constants changes every energy by at most those constants, so the weighted and unweighted form
domains coincide with equivalent norms. -/
theorem weighted_lintegral_bounds {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {c C : ENNReal} (hc : c ≠ ⊤) (hC : C ≠ ⊤)
    (w : α → ENNReal) (hlo : ∀ x, c ≤ w x) (hhi : ∀ x, w x ≤ C)
    (f : α → ENNReal) :
    c * ∫⁻ x, f x ∂μ ≤ ∫⁻ x, w x * f x ∂μ
      ∧ ∫⁻ x, w x * f x ∂μ ≤ C * ∫⁻ x, f x ∂μ := by
  constructor
  · rw [← lintegral_const_mul' c f hc]
    exact lintegral_mono fun x => by gcongr; exact hlo x
  · refine le_trans (lintegral_mono fun x => ?_) (le_of_eq (lintegral_const_mul' C f hC))
    gcongr
    exact hhi x

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The canonical bounded self-adjoint representative.**  A bounded symmetric sesquilinear form
on a Hilbert space is the inner-product form of a unique bounded self-adjoint operator.  This is
the sense in which the cyclic prolate constraint has a canonical representative on the common
energy completion. -/
theorem exists_isSelfAdjoint_representative (B : H →L⋆[ℂ] H →L[ℂ] ℂ)
    (hsymm : ∀ x y : H, B x y = (starRingEnd ℂ) (B y x)) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ ∀ x y : H, inner ℂ (T x) y = B x y := by
  refine ⟨InnerProductSpace.continuousLinearMapOfBilin B, ?_,
    fun x y => InnerProductSpace.continuousLinearMapOfBilin_apply B x y⟩
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply B x y,
    ← inner_conj_symm, InnerProductSpace.continuousLinearMapOfBilin_apply B y x, ← hsymm]

end RHTower
