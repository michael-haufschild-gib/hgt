import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ResolutionBins.AlignedMoment
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ResolutionBins.QuadraticMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.FiniteCircuitWindow

/-! # Physical gate occupation at the energy resolution of the record -/
open Finset Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SharpOccupation
noncomputable section

/-- Collision mass of replica frequencies grouped at resolution 1/T. -/
def replicaBinCollision {I : Type*} [Fintype I] [DecidableEq I] (w E : I → ℝ) (q : ℕ) (T : ℝ) :=
  binCollision (fun p : ReplicaMultiplicityIndex I q => T*replicaMultiplicityEnergy E p.val)
    (fun p => fidelityReplicaMultiplicityAmplitude w p.val)

/-- At any spectrum, the measured histogram gives both sides of the
worst Gaussian moment, up to absolute constants independent of order. -/
theorem aligned_bin_bounds {I : Type*} [Fintype I] [DecidableEq I] {w : I → ℝ}
    (hw : ∀ i, 0 ≤ w i) (E : I → ℝ) (q : ℕ) (T : ℝ) :
    exp (-1/2)*replicaBinCollision w E q T ≤ alignedMoment w E q T ∧
    alignedMoment w E q T ≤ 12*replicaBinCollision w E q T := by
  classical
  let F (p : ReplicaMultiplicityIndex I q) := T*replicaMultiplicityEnergy E p.val
  let a (p : ReplicaMultiplicityIndex I q) := fidelityReplicaMultiplicityAmplitude w p.val
  have he : alignedMoment w E q T=∑ p, ∑ z, a p*a z*exp (-(F p-F z)^2/2) := by
    unfold alignedMoment
    rw [sum_coe_sort (univ.piAntidiag q) (fun p => ∑ z : ReplicaMultiplicityIndex I q,
      fidelityReplicaMultiplicityAmplitude w p*a z*exp (-(T*replicaMultiplicityEnergy E p-F z)^2/2))]
    apply sum_congr rfl
    intro p _
    rw [sum_coe_sort (univ.piAntidiag q)]
    simp only [fidelityReplicaMultiplicityWeight_eq_amplitude_mul,a,F,mul_sub]
  rw [he]
  exact gaussian_energy_bins F a (fun p => fidelityReplicaMultiplicityAmplitude_nonneg hw p.val)

/-- No spacing or randomness is required. A single heavily crowded but
lightly weighted energy bin is priced by the square of its actual mass. -/
theorem physical_binned_gate_window {K : ℕ} (H : selfAdjoint (SharpOccupation.Register K))
    {ε δ ρ : ℝ} (hδ : 0 < δ) (hnear : ε+δ ≤ ρ) (hρ : 0 ≤ ρ) (hsmall : ρ^2 < 2)
    (s q : ℕ) (hq : 0 < q) (o : ℝ) {T : ℝ} (hT : 0 < T) :
    let w := microcanonicalWeight (Fin (2^K))
    let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
    let N := ((s:ℝ)+1)*((((K:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s
    visitFraction H s ε o (o+T) ≤ N*(96*replicaBinCollision w E q T/(1-ρ^2/2)^(2*q)) := by
  intro w E N
  let B := replicaBinCollision w E q T
  let τ := 1-ρ^2/2
  have hτ : 0 ≤ τ := by dsimp only [τ]; linarith only [hsmall]
  have hB : 0 ≤ B := sum_nonneg fun _ _ => sq_nonneg _
  have hw (i) : 0 ≤ w i := by dsimp only [w,microcanonicalWeight]; positivity
  have hd := (aligned_bin_bounds hw E q T).2
  apply gate_fraction_of_capture H hδ hnear hρ hsmall s q o hT (mul_nonneg (by norm_num) hB)
  intro J v hv
  let S := ⋃ j, uniformTwistedCoherenceCaptureSet w E (v j) T τ
  let A j := gaussianTwistedCoherenceCaptureSet w E (v j) T τ
  have hvol := volume_window_le_gaussian hT (show MeasurableSet S from
    MeasurableSet.iUnion fun j => uniformTwistedCoherenceCaptureSet_measurable ..)
    (show S ⊆ Icc (-T) T from iUnion_subset fun _ _ ht => ⟨ht.1.1.le,ht.1.2⟩)
  have hsub : (T * ·) ⁻¹' S ⊆ ⋃ j, A j := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (show T*x ∈ S from hx)
    exact mem_iUnion.mpr ⟨j,hj.2⟩
  have hsum := (measureReal_mono (μ:=gaussianReal 0 1) hsub).trans (measureReal_iUnion_fintype_le A)
  have htotal := hvol.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hj (j) : τ^(2*q)*(gaussianReal 0 1).real (A j) ≤ 12*B :=
    (threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_norm hw
      (sum_microcanonicalWeight_eq_one _).le (hv j) q hq hτ).trans
        (((greatest_gaussian_moment hw E q T).2 ⟨v j,fun i => (hv j i).le,rfl⟩).trans hd)
  calc _ ≤ τ^(2*q)*(8*T*∑ j, (gaussianReal 0 1).real (A j)) :=
         mul_le_mul_of_nonneg_left htotal (pow_nonneg hτ _)
       _ = 8*T*∑ j, τ^(2*q)*(gaussianReal 0 1).real (A j) := by rw [←Finset.mul_sum]; ring
       _ ≤ 8*T*∑ _j : Fin J, 12*B := mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hj j) (by positivity)
       _ = _ := by rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

#print axioms physical_binned_gate_window
#print axioms aligned_bin_bounds
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
