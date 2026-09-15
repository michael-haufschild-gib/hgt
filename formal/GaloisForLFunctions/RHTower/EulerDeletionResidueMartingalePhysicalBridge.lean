import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingale
import GaloisForLFunctions.RHTower.EulerDeletionRamarePhysicalEnergy

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower.DeletionResidueMartingalePhysical

private theorem source_eq_neg_modular_approximant (N : ℕ) :
    DeletionCoefficientTransfer.source
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N =
      -bdMobiusModularApproximantVec N := by
  rw [bdMobiusModularApproximantVec_eq_generatorCombination,
    bdMobiusGeneratorCombination, ← Finset.sum_neg_distrib]
  simp
  unfold DeletionCoefficientTransfer.source
  have hreindex (f : ℕ → BDCarrier) :
      ∑ i ∈ range N, f (i + 1) = ∑ m ∈ Icc 1 N, f m := by
    induction N with
    | zero => simp
    | succ N ih =>
      calc
        ∑ i ∈ range (N + 1), f (i + 1) =
            (∑ i ∈ range N, f (i + 1)) + f (N + 1) := by
          simpa using Finset.sum_range_succ (fun i => f (i + 1)) N
        _ = (∑ m ∈ Icc 1 N, f m) + f (N + 1) := by rw [ih]
        _ = ∑ m ∈ Icc 1 (N + 1), f m := by
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  simpa using
    (hreindex (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ) •
      bdGen (1 / (m : ℝ))))

/-- The complete physical Möbius carrier is within bounded norm gap of its
chronological predictable drift; every possible unbounded component is in that drift. -/
theorem modular_norm_drift_gap (N : ℕ) :
    |‖bdMobiusModularApproximantVec N‖ -
      ‖DeletionResidueMartingale.predictableDrift N‖| ^ 2 ≤ 2 := by
  rw [← norm_neg (bdMobiusModularApproximantVec N),
    ← source_eq_neg_modular_approximant]
  exact DeletionResidueMartingale.source_drift_norm_gap N

/-- The full signed physical Gram energy is controlled by the predictable
chronological drift, up to a cutoff-independent additive constant. -/
theorem sourceGramEnergy_le_two_drift_sq_add_four (N : ℕ) :
    DeletionRamarePhysical.sourceGramEnergy N ≤
      2 * ‖DeletionResidueMartingale.predictableDrift N‖ ^ 2 + 4 := by
  rw [DeletionRamarePhysical.sourceGramEnergy_eq_modular_norm_sq]
  have hgap := modular_norm_drift_gap N
  rw [sq_abs] at hgap
  nlinarith [sq_nonneg (‖bdMobiusModularApproximantVec N‖ -
    2 * ‖DeletionResidueMartingale.predictableDrift N‖)]

/-- The literal Ramaré rough-minus-packet field has the same predictable-drift
ceiling; no packet, rough term, or signed cross term has been dropped. -/
theorem packetField_energy_le_two_drift_sq_add_four {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (N : ℕ) :
    (∫ u in Set.Ioi (1 : ℝ),
      (DeletionRamarePhysical.rough P N u -
        ∑ p ∈ P, DeletionRamarePhysical.packet P N p u) ^ 2) ≤
      2 * ‖DeletionResidueMartingale.predictableDrift N‖ ^ 2 + 4 := by
  rw [DeletionRamarePhysical.integral_packetField_sq_eq_sourceGramEnergy hPprime N]
  exact sourceGramEnergy_le_two_drift_sq_add_four N

end RHTower.DeletionResidueMartingalePhysical
