import GaloisForLFunctions.RHTower.PrimeBurnolPositiveSymbol

/-! Exact classification of physical positivity among actual-prime Burnol eigenoperators. -/

noncomputable section
open MeasureTheory Set
open scoped ComplexOrder NNReal

namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

theorem primeBurnol_packetTest_representation
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (hp : BurnolPositivePacketTest T) :
    ∃ τ : Measure ℝ≥0, IsFiniteMeasure τ ∧
      ∀ f, T f = ∫ h, burnolWeightedShift h f ∂τ := by
  obtain ⟨τ, hτ, hsymbol⟩ := exists_burnolPositiveSymbol_measure T a ha hp
  letI : IsFiniteMeasure τ := hτ
  have he : T = burnolPositiveShiftMixture τ := by
    apply primeBurnol_operator_ext
    intro p
    rw [primeLogCriticalLaplaceFeatureL2_eq_burnol, map_smul, map_smul]
    congr 1
    have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
    change T (burnolComplexFeature (Real.log (p : ℝ) : ℂ) hl) =
      burnolPositiveShiftMixture τ (burnolComplexFeature (Real.log (p : ℝ) : ℂ) hl)
    rw [burnolComplexFeature_ofReal]
    change T (burnolRateFeature (Real.log (p : ℝ)) hl) =
      burnolPositiveShiftMixture τ (burnolRateFeature (Real.log (p : ℝ)) hl)
    rw [burnolOperatorSymbol_rate T a ha, burnolPositiveShiftMixture_rate, hsymbol _ hl]
  exact ⟨τ, hτ, fun f => by rw [he]; rfl⟩

/-- Testing every explicit positive exponential-difference packet is complete. -/
theorem primeBurnol_preservesNonnegativity_iff_packetTest
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2)
    (hline : ∀ p : Nat.Primes, ∃ a : ℂ,
      T (primeLogCriticalLaplaceFeatureL2 p) = a • primeLogCriticalLaplaceFeatureL2 p) :
    BurnolPreservesNonnegativity T ↔ BurnolPositivePacketTest T := by
  constructor
  · exact BurnolPreservesNonnegativity.packetTest
  · intro hp
    choose a ha using hline
    obtain ⟨τ, hτ, he⟩ := primeBurnol_packetTest_representation T a ha hp
    letI : IsFiniteMeasure τ := hτ
    intro f hf
    rw [he]
    exact burnolPositiveShiftMixture_nonneg τ hf

/-- Every positive actual-prime eigenoperator has one and only one finite shift measure. -/
theorem primeBurnol_preservesNonnegativity_iff_unique_measure
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2)
    (hline : ∀ p : Nat.Primes, ∃ a : ℂ,
      T (primeLogCriticalLaplaceFeatureL2 p) = a • primeLogCriticalLaplaceFeatureL2 p) :
    BurnolPreservesNonnegativity T ↔
      ∃! τ : Measure ℝ≥0, IsFiniteMeasure τ ∧
        ∀ f, T f = ∫ h, burnolWeightedShift h f ∂τ := by
  constructor
  · intro hp
    choose a ha using hline
    obtain ⟨τ, hτ, he⟩ := primeBurnol_packetTest_representation T a ha hp.packetTest
    letI : IsFiniteMeasure τ := hτ
    refine ⟨τ, ⟨hτ, he⟩, ?_⟩
    rintro σ ⟨hσ, hs⟩
    letI : IsFiniteMeasure σ := hσ
    apply burnolPositiveShiftMixture_injective
    apply ContinuousLinearMap.ext
    intro f
    exact (hs f).symm.trans (he f)
  · rintro ⟨τ, ⟨hτ, he⟩, _⟩
    letI : IsFiniteMeasure τ := hτ
    intro f hf
    rw [he]
    exact burnolPositiveShiftMixture_nonneg τ hf

/-- In the unique measure coordinates, operator norm is exactly total positive mass. -/
theorem primeBurnol_positive_measure_norm
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2)
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ]
    (he : ∀ f, T f = ∫ h, burnolWeightedShift h f ∂τ) :
    ‖T‖ = (τ univ).toReal := by
  have hT : T = burnolPositiveShiftMixture τ := ContinuousLinearMap.ext he
  rw [hT, norm_burnolPositiveShiftMixture]

/-- The measure class is genuinely realized on the actual physical critical-prime columns. -/
theorem primeBurnol_positive_measure_realization (τ : Measure ℝ≥0) [IsFiniteMeasure τ] :
    BurnolPreservesNonnegativity (burnolPositiveShiftMixture τ) ∧
      (∀ p : Nat.Primes, burnolPositiveShiftMixture τ (primeLogCriticalLaplaceFeatureL2 p) =
        (burnolMeasureLaplace τ (Real.log (p : ℝ)) : ℂ) • primeLogCriticalLaplaceFeatureL2 p) ∧
      ‖burnolPositiveShiftMixture τ‖ = (τ univ).toReal := by
  refine ⟨fun _ hf => burnolPositiveShiftMixture_nonneg τ hf, ?_, norm_burnolPositiveShiftMixture τ⟩
  intro p
  rw [primeLogCriticalLaplaceFeatureL2_eq_burnol, map_smul, smul_comm]
  congr 1
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  change burnolPositiveShiftMixture τ (burnolComplexFeature (Real.log (p : ℝ) : ℂ) hl) =
    (burnolMeasureLaplace τ (Real.log (p : ℝ)) : ℂ) •
      burnolComplexFeature (Real.log (p : ℝ) : ℂ) hl
  rw [burnolComplexFeature_ofReal]
  exact burnolPositiveShiftMixture_rate τ (Real.log (p : ℝ)) hl

end RHTower
