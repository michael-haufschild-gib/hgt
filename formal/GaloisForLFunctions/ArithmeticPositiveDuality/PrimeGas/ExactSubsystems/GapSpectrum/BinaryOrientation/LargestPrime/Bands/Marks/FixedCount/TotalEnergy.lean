import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.OrderedLaw

/-! # Total measured prime energy at fixed occupation count -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount

open Filter Topology Set MeasureTheory _root_.RHTower
open GaloisForLFunctions.HTGeometry

/-- Sum of the observed single-mode energies. -/
def total {k : ℕ} (v : Fin k → ℝ) := ∑ i, v i

theorem continuous_total (k : ℕ) : Continuous (total (k := k)) :=
  continuous_finsetSum _ fun i _ => continuous_apply i

theorem total_sorted {k : ℕ} (v : Fin k → ℝ) : total (sortedTuple v) = total v :=
  Equiv.sum_comp (Tuple.sort v) v

/-- The sum on a count slice is the scaled Hamiltonian of that very configuration. -/
theorem total_spectrum {S : Finset Nat.Primes} {k : ℕ} (h : Ioi (0:ℝ)) (R : BreadthSubset k ↥S) :
    total (spectrum h R) = packetEnergy S h ((squarefreeOccupationEquiv S).symm R.val) := by
  letI : LinearOrder Nat.Primes := LinearOrder.lift' Subtype.val Subtype.val_injective
  rw [spectrum,total_sorted,packetEnergy,finiteSquarefreeHamiltonian_eq_sum_occupation,
    show squarefreeOccupationFinset ((squarefreeOccupationEquiv S).symm R.val) = R.val from
      (squarefreeOccupationEquiv S).apply_symm_apply R.val,Finset.mul_sum]
  let e := (R.val.orderIsoOfFin R.property).toEquiv
  calc _ = ∑ p : ↥R.val, location h p.val.val := e.sum_comp (fun p => location h p.val.val)
       _ = _ := Finset.sum_coe_sort R.val (fun p => location h p.val)

/-- Summing order statistics gives the sum of independent draws. -/
theorem sum_orderStatistics (k : ℕ) (μ : ProbabilityMeasure ℝ) :
    (orderStatistics k μ).map (continuous_total k).measurable.aemeasurable =
      (iid k μ).map (continuous_total k).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map,orderStatistics,ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map,Measure.map_map (continuous_total k).measurable (continuous_sort k).measurable]
  exact congrArg (fun f => Measure.map f (iid k μ : Measure (Fin k → ℝ))) (funext total_sorted)

/-- Conditional total energy converges to the distribution of the sum of k independent jumps. -/
theorem total_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) (k : ℕ) :
    Tendsto (fun h => (conditional c d a h k).map (continuous_total k).measurable.aemeasurable)
      criticalApproach (𝓝 ((iid k (draw hc hcd.le a)).map (continuous_total k).measurable.aemeasurable)) := by
  rw [← sum_orderStatistics]
  exact ((ProbabilityMeasure.continuous_map (continuous_total k)).tendsto _).comp (conditional_limit hc hcd a k)

#print axioms total_sorted
#print axioms total_spectrum
#print axioms sum_orderStatistics
#print axioms total_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount
