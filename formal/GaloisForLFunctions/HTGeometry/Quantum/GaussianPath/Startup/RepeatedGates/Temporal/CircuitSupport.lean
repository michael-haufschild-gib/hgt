import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.TriplePacking
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.CausalSupport

/-! # Temporal input sets enclose the support of conjugated observables -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
noncomputable section
variable {N : ℕ}

/-- Below the packing bound some ordered pair at physical distance one
or two has exactly zero signal for every pair of local observables. -/
theorem missing_short_signal (C : TwoQubitCircuit N) (hc : 2*(C.gateCount+1)<2*N+N/3) :
    ∃ i j : Fin N, i≠j ∧ i.val ≤ j.val+2 ∧ j.val ≤ i.val+2 ∧
      ∀ A B : Register N, IsSiteSupported {i} A → IsSiteSupported {j} B →
        Commute (star C.eval.val*A*C.eval.val) B := by
  classical
  apply missing_of_incomplete C
  intro h
  have hb := path_exchange_budget (circuitWord C) h
  rw [circuitWord_length] at hb
  exact hc.not_ge hb

end
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
