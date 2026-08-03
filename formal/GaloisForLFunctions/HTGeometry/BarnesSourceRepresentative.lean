import GaloisForLFunctions.HTGeometry.PuncturedRepresentativePieces
import GaloisForLFunctions.HTGeometry.BarnesPoleAvoidance
import GaloisForLFunctions.HTGeometry.BarnesSourceMero

/-!
# The Barnes source and its punctured representative

The Barnes source is the logarithmic derivative, in the global meromorphic differential field, of
the entire cone product.  It is therefore represented, on the punctured neighbourhood of every
point, by the pointwise logarithmic derivative of that product, and its translate by the translated
logarithmic derivative.

Together with the uniqueness of a punctured representative and the punctured-thinness of the cone
poles, this is what turns the pointwise ladder identities of the cone product into identities in the
field.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

attribute [local instance] puncturedRepDomain puncturedRepComplexAlgebraAnalytic
  puncturedRepComplexAlgebraMero puncturedRepDifferential

variable {ι : Type} [Fintype ι] [Nonempty ι]

theorem analyticOnNhd_barnesConeProduct (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    AnalyticOnNhd ℂ (barnesConeProduct ω) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact differentiable_barnesConeProduct ω hω

/-- **The Barnes source is represented by the pointwise logarithmic derivative of the cone
product.** -/
theorem hasPuncturedMeromorphicRep_barnesSourceLogDerivMero (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i).im) :
    HasPuncturedMeromorphicRep (barnesSourceLogDerivMero ω hω)
      (logDeriv (barnesConeProduct ω)) := by
  have hrep := hasPuncturedMeromorphicRep_logDeriv (barnesConeAnalytic_ne_zero ω hω)
    (f := barnesConeProduct ω) (analyticOnNhd_barnesConeProduct ω hω) rfl
  refine hrep.congr_fun fun z => Filter.Eventually.of_forall fun w => ?_
  rw [logDeriv_apply]

/-- **The translated Barnes source is represented by the translated logarithmic derivative.** -/
theorem hasPuncturedMeromorphicRep_addTranslation_barnesSourceLogDerivMero (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i).im) (q : ℂ) :
    HasPuncturedMeromorphicRep
      (addTranslationMeroEquiv q (barnesSourceLogDerivMero ω hω))
      (fun z => logDeriv (barnesConeProduct ω) (z + q)) :=
  (hasPuncturedMeromorphicRep_barnesSourceLogDerivMero ω hω).translate q

end

end GaloisForLFunctions
