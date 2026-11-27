import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitTargets.EnergyRotation.PauliFrames
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.CrossingDeadline

/-! # Pauli corrections of the circuit at the distinguished first dip -/
open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section
open PrecisionReturns

/-- From the original robust crossing, each first affordable date has
a circuit witness whose extensive Pauli corrections are excluded at
every physical date of the same prefix. The tolerance at both dates is
one tenth and all budgets through the crossing budget are simultaneous. -/
theorem gaussian_first_dip_pauli_corrections :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let P := nearHilbertContinuousCircuitBudget K
      let σ := ReturnExcursions.Iterated.crossing H P 0
      ∀ s ≤ P, let v := firstVisit H σ s (1/10)
        ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧
          ‖unitaryEvolution H.val v-z • C.eval.val‖ ≤ 1/10 ∧
          ∀ Q : Fin K → Option (Fin 3), ∀ t : ℝ, ∀ w : ℂ, ‖w‖=1 →
            η*(K:ℝ)<(labelSupport Q).card →
            1/10<‖unitaryEvolution H.val t-w • (finitePauliMatrix Q*C.eval.val)‖ := by
  filter_upwards [gaussian_all_time_pauli_support] with ω hw
  intro η hη
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (hw η hη)] with k hk
  intro K u H P σ s _ v
  have hl := (firstVisit_isLeast H σ s (by norm_num : (0:ℝ) < 1/10)).1.2
  obtain ⟨z,hz,C,hC,hfit⟩ := hl
  refine ⟨z,hz,C,hC,hfit,?_⟩
  intro Q t w hw hS
  by_contra! hclose
  obtain ⟨r,hr,h⟩ := pauli_lag H Q C.eval.val v t z w hz hw
  exact hS.not_ge (hk Q (t-v) r hr (h.trans (by linarith only [hfit,hclose])))

#print axioms gaussian_first_dip_pauli_corrections
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
