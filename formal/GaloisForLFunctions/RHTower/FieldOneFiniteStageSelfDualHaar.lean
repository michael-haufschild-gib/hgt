import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteAdeleHaar
import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleLocusMeasure

/-!
# Self-dual additive Haar measure at a rational finite stage

For the standard conductor-zero character on every rational nonarchimedean
completion, self-dual additive Haar measure is normalized by giving its
valuation ring mass one.  This file constructs those local measures and their
finite product explicitly.  The real factor is Lebesgue measure, matching the
source character `x ↦ exp(-2πix)`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory Set TopologicalSpace

/-- Valuation ring as a compact set with nonempty interior in the local
completion. -/
def fieldOneLocalIntegersPositiveCompacts
    (v : HeightOneSpectrum ℤ) :
    PositiveCompacts (v.adicCompletion ℚ) where
  carrier := v.adicCompletionIntegers ℚ
  isCompact' := by
    exact isCompact_iff_compactSpace.mpr
      (inferInstance : CompactSpace (v.adicCompletionIntegers ℚ))
  interior_nonempty' := by
    have hopen : IsOpen
        (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
      Valued.isOpen_valuationSubring (v.adicCompletion ℚ)
    rw [hopen.interior_eq]
    exact ⟨0, zero_mem _⟩

/-- Conductor-zero local additive Haar measure, normalized by
`vol(ℤ_v) = 1`. -/
def fieldOneLocalSelfDualAddHaar
    (v : HeightOneSpectrum ℤ) :
    Measure (v.adicCompletion ℚ) :=
  Measure.addHaarMeasure (fieldOneLocalIntegersPositiveCompacts v)

instance fieldOneLocalSelfDualAddHaar_isAddHaar
    (v : HeightOneSpectrum ℤ) :
    (fieldOneLocalSelfDualAddHaar v).IsAddHaarMeasure := by
  unfold fieldOneLocalSelfDualAddHaar
  infer_instance

instance fieldOneLocalSelfDualAddHaar_regular
    (v : HeightOneSpectrum ℤ) :
    (fieldOneLocalSelfDualAddHaar v).Regular := by
  unfold fieldOneLocalSelfDualAddHaar
  infer_instance

@[simp]
theorem fieldOneLocalSelfDualAddHaar_integers
    (v : HeightOneSpectrum ℤ) :
    fieldOneLocalSelfDualAddHaar v (v.adicCompletionIntegers ℚ) = 1 := by
  exact Measure.addHaarMeasure_self

/-- Explicit self-dual additive Haar product on
`A_{ℚ,S} = ℝ × ∏_{v∈S} ℚ_v`. -/
def fieldOneFiniteStageSelfDualAddHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageAdele S) :=
  (volume : Measure ℝ).prod
    (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)

end

end GaloisForLFunctions.RHTower
