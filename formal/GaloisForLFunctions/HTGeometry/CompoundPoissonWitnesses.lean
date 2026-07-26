import GaloisForLFunctions.HTGeometry.ConvolutionAtomBounds

/-!
# Compound Poisson mixtures exist by construction

Every convolution-power mixture with nonvanishing weights over an s-finite base is a compound Poisson
mixture, which realizes the interface for an arbitrary s-finite base measure.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

variable {M : Type*} [AddCommMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M]
  [MeasurableSingletonClass M]

omit [MeasurableAdd₂ M] [MeasurableSingletonClass M] in
/-- A convolution-power mixture with nonvanishing weights is a compound Poisson mixture. -/
theorem isCompoundPoissonMixture_convPowMixture (c : ℕ → ℝ≥0∞) (hc : ∀ m, c m ≠ 0)
    (Q : Measure M) [SFinite Q] :
    IsCompoundPoissonMixture (convPowMixture c Q) :=
  ⟨c, Q, hc, inferInstance, rfl⟩

omit [MeasurableAdd₂ M] [MeasurableSingletonClass M] in
/-- The interface is realized for every s-finite base measure. -/
theorem exists_isCompoundPoissonMixture (Q : Measure M) [SFinite Q] :
    ∃ μ : Measure M, IsCompoundPoissonMixture μ :=
  ⟨convPowMixture (fun _ => 1) Q, isCompoundPoissonMixture_convPowMixture _
    (fun _ => one_ne_zero) Q⟩

end GaloisForLFunctions.HTGeometry
