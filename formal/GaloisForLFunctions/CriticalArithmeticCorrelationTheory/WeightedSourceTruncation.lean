import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePrimeAndPoleFormsAreContinuousInTheWeightedNorm

/-!
# Measurable truncation of weighted sources

Hard spatial cuts preserve the exponential source domain. Their squared
norms are exactly the corresponding restricted weighted integrals.
-/

noncomputable section
open MeasureTheory Filter Set
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticCastelnuovoSeveri

theorem WeightedTwo.indicator {f : ℝ → ℝ} (hf : WeightedTwo f)
    {s : Set ℝ} (hs : MeasurableSet s) : WeightedTwo (s.indicator f) := by
  refine ⟨hf.meas.indicator hs, (hf.sq.indicator hs).congr ?_⟩
  exact Eventually.of_forall fun u => by
    by_cases hu : u ∈ s
    · simp only [indicator_of_mem hu]
    · simp only [indicator_of_notMem hu, mul_zero, zero_pow two_ne_zero]

theorem exponentialSourceMass_indicator (f : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    exponentialSourceMass (s.indicator f) = ∫ u in s, (Real.exp |u| * f u) ^ 2 := by
  unfold exponentialSourceMass
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    by_cases hu : u ∈ s
    · simp only [indicator_of_mem hu]
    · simp only [indicator_of_notMem hu, mul_zero, zero_pow two_ne_zero]

theorem exponentialSourceMass_indicator_le {f : ℝ → ℝ} (hf : WeightedTwo f)
    {s : Set ℝ} (hs : MeasurableSet s) :
    exponentialSourceMass (s.indicator f) ≤ exponentialSourceMass f := by
  rw [exponentialSourceMass_indicator f hs]
  exact setIntegral_le_integral hf.sq (Eventually.of_forall fun u => sq_nonneg _)

/-- The mass removed by a spatial cut is the weighted mass of its complement. -/
theorem exponentialSourceMass_sub_indicator (f : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    exponentialSourceMass (fun u => f u - s.indicator f u) =
      ∫ u in sᶜ, (Real.exp |u| * f u) ^ 2 := by
  have heq : (fun u => f u - s.indicator f u) = sᶜ.indicator f := by
    funext u
    by_cases hu : u ∈ s
    · have hc : u ∉ sᶜ := fun h => h hu
      simp only [indicator_of_mem hu, sub_self, indicator_of_notMem hc]
    · have hc : u ∈ sᶜ := hu
      simp only [indicator_of_notMem hu, sub_zero, indicator_of_mem hc]
  rw [heq, exponentialSourceMass_indicator f hs.compl]

#print axioms WeightedTwo.indicator
#print axioms exponentialSourceMass_sub_indicator

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
