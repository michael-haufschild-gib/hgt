import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.GaussianRows
import GaloisForLFunctions.HTGeometry.ReplicaAmplitudeMoments

/-! # Gaussian replica moment at inverse occupation-frequency spacing -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section

/-- Unit spacing of the scaled multiplicity energies bounds the moment
by a constant times its diagonal, uniformly over phase twists and order. -/
theorem separated_replica_moment {I : Type*} [Fintype I] [DecidableEq I] {w : I → ℝ}
    (E : I → ℝ) {v : I → ℂ} (hv : ∀ i, ‖v i‖=1) (q : ℕ) (T : ℝ)
    (hsep : ∀ p z : ReplicaMultiplicityIndex I q, p≠z →
      1 ≤ |T*replicaMultiplicityEnergy E p.val-T*replicaMultiplicityEnergy E z.val|) :
    ‖twistedGaussianSpectralFidelityMean w E v q T‖ ≤ 12*fidelityReplicaPermutationFloor w q := by
  classical
  let a (p : ReplicaMultiplicityIndex I q) := fidelityReplicaMultiplicityAmplitude w p.val
  let F (p : ReplicaMultiplicityIndex I q) := T*replicaMultiplicityEnergy E p.val
  let term (p z : I → ℕ) := (fidelityReplicaMultiplicityWeight w p z:ℂ)*
    replicaMultiplicityTwist v p z*gaussianObserverActionKernel (T*(replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E z))
  have he : twistedGaussianSpectralFidelityMean w E v q T=
      ∑ p : ReplicaMultiplicityIndex I q, ∑ z : ReplicaMultiplicityIndex I q, term p.val z.val := by
    rw [twistedGaussianSpectralFidelityMean_eq_actionKernel,Finset.sum_coe_sort (univ.piAntidiag q)
      (fun p => ∑ z : ReplicaMultiplicityIndex I q, term p z.val)]
    apply sum_congr rfl
    intro p _
    exact (Finset.sum_coe_sort (univ.piAntidiag q) (term p)).symm
  have ht (p z : ReplicaMultiplicityIndex I q) : ‖term p.val z.val‖=
      |a p| * |a z| * exp (-(F p-F z)^2/2) := by
    simp only [term,norm_mul,norm_replicaMultiplicityTwist hv,mul_one,norm_gaussianObserverActionKernel,
      Complex.norm_real,Real.norm_eq_abs,fidelityReplicaMultiplicityWeight_eq_amplitude_mul,F,a,mul_sub]
  have hfloor : (∑ p : ReplicaMultiplicityIndex I q, (a p)^2)=fidelityReplicaPermutationFloor w q := by
    rw [←fidelityReplicaSubtypePermutationFloor_eq]
    simp only [fidelityReplicaSubtypePermutationFloor,fidelityReplicaMultiplicityWeight_eq_amplitude_mul,pow_two,a]
  rw [he,←hfloor]
  calc _ ≤ ∑ p : ReplicaMultiplicityIndex I q, ∑ z : ReplicaMultiplicityIndex I q, ‖term p.val z.val‖ :=
         (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
       _ ≤ _ := by
         simp only [ht]
         exact separated_gaussian_energy F a hsep

#print axioms separated_replica_moment
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
