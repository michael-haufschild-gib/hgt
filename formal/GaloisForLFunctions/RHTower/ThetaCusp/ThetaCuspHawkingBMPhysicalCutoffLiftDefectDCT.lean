import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalCutoffDCT
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsLiftDefect

/-! The compact physical exhaustion retains the literal full-minus-native lift defect. -/

open Set MeasureTheory Filter Topology
namespace RHTower.D4BMFullAngularCausalPeierls
open D4BMFullSourceReciprocity D4BMLiteralCyclicPeierlsLiftDefect
noncomputable section

/-- The full density integral is exactly its native integral plus the explicit lift defect. -/
theorem fullSourcePairDensity_integral_eq_native_add_liftDefect (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    (∫ z, fullSourcePairDensity q branch b c a d X k z ∂eventMeasure.prod eventMeasure) =
      (∫ z, sourcePairDensity q b c a d X k z ∂eventMeasure.prod eventMeasure) +
        ∫ z, sourcePairLiftDefect q branch b c a d X k z ∂eventMeasure.prod eventMeasure := by
  simp_rw [fullSourcePairDensity_eq_native_add_defect]
  rw [integral_add (sourcePairDensity_integrable q b c a d X k)
    (sourcePairLiftDefect_integrable q branch b c a d X k)]

/-- The joint compact physical cutoff converges to the native Peierls density plus precisely
the displayed full-minus-native lift defect. -/
theorem cutoffFullSourcePairDensity_integral_tendsto_native_add_liftDefect (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    Tendsto (fun n => ∫ z, cutoffFullSourcePairDensity n q branch b c a d X k z
      ∂eventMeasure.prod eventMeasure) atTop
      (𝓝 ((∫ z, sourcePairDensity q b c a d X k z ∂eventMeasure.prod eventMeasure) +
        ∫ z, sourcePairLiftDefect q branch b c a d X k z ∂eventMeasure.prod eventMeasure)) := by
  rw [← fullSourcePairDensity_integral_eq_native_add_liftDefect q branch b c a d X k]
  exact cutoffFullSourcePairDensity_integral_tendsto q branch b c a d X k

end
end RHTower.D4BMFullAngularCausalPeierls
