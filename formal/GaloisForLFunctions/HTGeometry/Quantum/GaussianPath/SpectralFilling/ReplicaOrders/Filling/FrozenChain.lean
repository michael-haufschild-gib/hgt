import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Filling.PolynomialOrder
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.PhysicalRecords
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.MaximumClock

/-! # Phase filling at physical time set by one observed multiset gap -/
open MeasureTheory Filter Set Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SpectralJets.AllHeights
open private maximum_windows_of_scalar from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.MaximumClock
noncomputable section

/-- Four pi divided by the spacing at the target-dependent replica order. -/
def alignmentLength (k : ℕ) (E : Level k → ℝ) (ε : ℝ) :=
  4*π/recordGap k E (alignmentOrder (2^(k+3)) (min ε 1))

/-- Every target on the relative phase torus is visited from every origin
on the same frozen prefix. Only the spacing at one polynomial order enters. -/
theorem gaussian_replica_phase_filling :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues ∘
        (qubitConfigFin K).symm
      ∀ ε > (0:ℝ), ∀ a : ℝ, ∀ v : Level k → ℂ, (∀ i, ‖v i‖=1) →
        ∃ t ∈ Icc a (a+alignmentLength k E ε), ∃ z : ℂ, ‖z‖=1 ∧ ∀ i,
          ‖v i*Complex.exp (Complex.I*(E i:ℂ)*(t:ℂ))-z‖ < ε := by
  filter_upwards [gaussian_record_gaps] with ω hw
  filter_upwards [hw] with k hk
  intro K E ε hε a v hv
  let δ := min ε 1
  have hd : 0 < δ := lt_min hε zero_lt_one
  let q := alignmentOrder (2^K) δ
  have hp := alignmentOrder_price (Level k) hd (min_le_right ε 1)
  rw [Fintype.card_fin] at hp
  obtain ⟨t,ht,z,hz,hall⟩ := all_targets_at_order E q (recordGap_pos k E q) hd (hk q) hp v hv a
  exact ⟨t,ht,z,hz,fun i => (hall i).trans_le (min_le_left ..)⟩

private theorem scalar_chords {n : ℕ} (H : selfAdjoint (SharpOccupation.Register n)) (t ε : ℝ)
    (hε : 0 ≤ ε) (z : ℂ) (hz : ‖z‖=1) (he : ∀ i,
      ‖Complex.exp (Complex.I*(H.2.isHermitian.eigenvalues i:ℂ)*(t:ℂ))-z‖ ≤ ε) :
    HasProjectiveCircuitApproximation n ε 0 (unitaryEvolution H.val t) := by
  let V := H.2.isHermitian.eigenvectorUnitary
  let c := star z
  let f (i : Fin n → Bool) := Complex.exp (-(Complex.I*((t:ℂ)*(H.2.isHermitian.eigenvalues i:ℂ))))
  have hc : ‖c‖=1 := (norm_star z).trans hz
  have hf (i) : ‖f i-c‖ ≤ ε := by
    have h : star (Complex.exp (Complex.I*(H.2.isHermitian.eigenvalues i:ℂ)*(t:ℂ)))=f i := by
      change (starRingEnd ℂ) _=_
      rw [←Complex.exp_conj,map_mul,map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.conj_ofReal]
      dsimp only [f]
      congr 1
      ring
    simpa only [←h,c,←star_sub,norm_star] using he i
  have hone : c • (1 : SharpOccupation.Register n)=V.val*diagonal (fun _ => c)*star V.val := by
    rw [←smul_one_eq_diagonal_const,Matrix.mul_smul,mul_one,Matrix.smul_mul,(Unitary.mem_iff.mp V.property).2]
  refine ⟨c,hc,TwoQubitCircuit.one n,Nat.zero_le _,?_⟩
  rw [TwoQubitCircuit.one_eval,hone,unitaryEvolution_spectral H.2.isHermitian,←Matrix.sub_mul,←Matrix.mul_sub,
    ←Matrix.diagonal_sub,l2_opNorm_unitary_conj_eq V.property,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hε).mpr hf

/-- The same measured horizon bounds the wait for a zero-gate visit
from any starting date, including a disorder-selected crossing. -/
theorem gaussian_replica_scalar_windows :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      ∀ ε > (0:ℝ), ∀ a : ℝ, ∃ t ∈ Icc a (a+alignmentLength k E ε),
        HasProjectiveCircuitApproximation K ε 0 (unitaryEvolution H.val t) := by
  filter_upwards [gaussian_replica_phase_filling] with ω hw
  filter_upwards [hw] with k hk
  intro K u H E ε hε a
  obtain ⟨t,ht,z,hz,he⟩ := hk ε hε a (fun _ => 1) (fun _ => norm_one)
  refine ⟨t,ht,scalar_chords H t ε hε.le z hz (fun i => ?_)⟩
  simpa only [E,Function.comp_apply,Equiv.symm_apply_apply,one_mul] using (he (qubitConfigFin K i)).le

/-- One measured order bounds the true first affordable date at every
budget and every positive tolerance, after any selected physical date. -/
theorem gaussian_replica_first_visit :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      ∀ ε > (0:ℝ), ∀ a : ℝ, ∀ s : ℕ,
        PrecisionReturns.firstVisit H a s ε-a ∈ Icc 0 (alignmentLength k E ε) := by
  filter_upwards [gaussian_replica_scalar_windows] with ω hw
  filter_upwards [hw] with k hk
  intro K u H E ε hε a s
  have hfirst := PrecisionReturns.firstVisit_isLeast H a s hε
  obtain ⟨t,ht,c,hc,C,hC,he⟩ := hk ε hε a
  have hh := hfirst.2 (show t∈PrecisionReturns.visitSet H a s ε from
    ⟨ht.1,c,hc,C,hC.trans (Nat.zero_le _),he⟩)
  exact ⟨sub_nonneg.mpr hfirst.1.1,by linarith only [hh,ht.2]⟩

/-- Every interval of the measured length at the predecessor clearance
contains a whole-bandwidth neighborhood attaining the actual maximum. -/
theorem gaussian_replica_maximum_windows :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      ∀ ε > (0:ℝ), ∃ m, IsRecurrentOrbitCircuitMaximumAt H ε m ∧
        let ρ := maximumResolution H m ε
        0 < ρ ∧ ∀ a : ℝ, ∃ z ∈ Icc a (a+alignmentLength k E ρ), ∀ t : ℝ,
          circuitHamiltonianSpectralWidth H*|t-z| ≤ ρ → ∀ s,
            HasProjectiveCircuitApproximation K ε s (unitaryEvolution H.val t) ↔ m ≤ s := by
  filter_upwards [gaussian_replica_scalar_windows] with ω hw
  filter_upwards [hw] with k hk
  intro K u H E ε hε
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at (by dsimp only [K]; omega : 2 ≤ K)
    H (hasPauliWeightAtMost_pathHamiltonian u _) ε hε
  exact ⟨m,hm,maximum_windows_of_scalar H hm (alignmentLength k E) (fun r hr => hk r hr.1)⟩

#print axioms gaussian_replica_maximum_windows
#print axioms gaussian_replica_first_visit
#print axioms gaussian_replica_phase_filling
#print axioms gaussian_replica_scalar_windows
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
