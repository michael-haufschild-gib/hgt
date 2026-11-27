import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.GapClock
import GaloisForLFunctions.HTGeometry.PhaseTwistedReplicaShortcutActionLaw

/-! # Exact finite-date moments for every target on the same Hamiltonian -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Distinct nonzero absolute detunings between order-q energy sums. -/
def frequencies (E : I → ℝ) (q : ℕ) : Finset ℝ :=
  gaps (univ.piAntidiag q) (replicaMultiplicityEnergy E)

/-- The same positive temporal quadrature retains exactly the equal-energy
replica pairs for every choice of weights, complex target and origin.
Spectral degeneracies and higher-order resonances are included. -/
theorem exact_replica_moment (w E : I → ℝ) (v : I → ℂ) (q : ℕ) (a : ℝ) :
    average (frequencies E q).toList (fun t => twistedFiniteSpectralFidelity w E v t^q) a =
      ∑ p ∈ univ.piAntidiag q, ∑ z ∈ univ.piAntidiag q,
        if replicaMultiplicityEnergy E p=replicaMultiplicityEnergy E z then
          (fidelityReplicaMultiplicityWeight w p z:ℂ)*replicaMultiplicityTwist v p z else 0 := by
  classical
  let S := (univ : Finset I).piAntidiag q
  let d (p z : I → ℕ) := replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E z
  let c (p z : I → ℕ) := (fidelityReplicaMultiplicityWeight w p z:ℂ)*replicaMultiplicityTwist v p z
  have hex (t : ℝ) : twistedFiniteSpectralFidelity w E v t^q =
      ∑ p ∈ S, ∑ z ∈ S, c p z*wave (d p z) t := by
    simpa only [S,c,wave,d,mul_comm t] using twistedFiniteSpectralFidelity_pow_expansion w E v q t
  rw [show (fun t => twistedFiniteSpectralFidelity w E v t^q)=_ from funext hex,average_sum]
  apply sum_congr rfl
  intro p hp
  rw [average_sum]
  apply sum_congr rfl
  intro z hz
  rw [average_scale,show average (frequencies E q).toList (wave (d p z)) a=
    (if replicaMultiplicityEnergy E p=replicaMultiplicityEnergy E z then 1 else 0)
    from gap_phase S (replicaMultiplicityEnergy E) hp hz a]
  split_ifs <;> simp [c]

/-- The finite clock reads the infinite-time moment exactly, for any
origin and all target twists, including resonant finite spectra. -/
theorem mean_tendsto_quadrature (w E : I → ℝ) (v : I → ℂ) (q : ℕ) (a : ℝ) :
    Filter.Tendsto (twistedFiniteSpectralFidelityMean w E v q) Filter.atTop
      (nhds (average (frequencies E q).toList (fun t => twistedFiniteSpectralFidelity w E v t^q) a)) := by
  classical
  rw [exact_replica_moment]
  change Filter.Tendsto (fun T => twistedFiniteSpectralFidelityMean w E v q T) _ _
  simp only [twistedFiniteSpectralFidelityMean_eq_replicaPhaseAverage]
  apply tendsto_finsetSum
  intro p _
  apply tendsto_finsetSum
  intro z _
  let c := (fidelityReplicaMultiplicityWeight w p z:ℂ)*replicaMultiplicityTwist v p z
  let d := replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E z
  have h := (symmetricPhaseAverage_tendsto_resonanceIndicator d).const_mul c
  by_cases hz : replicaMultiplicityEnergy E p=replicaMultiplicityEnergy E z
  · simpa only [d,sub_eq_zero,if_pos hz,mul_one,c] using h
  · simpa only [d,sub_eq_zero,if_neg hz,mul_zero,c] using h

#print axioms exact_replica_moment
#print axioms mean_tendsto_quadrature
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
