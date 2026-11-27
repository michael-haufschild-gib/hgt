import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.NearHilbertWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.Timeline

/-! # First robust crossing before an entropy-discounted inverse replica spacing -/
open Set Filter MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SharpOccupation
noncomputable section

/-- From every origin, including zero and all later low visits, the
actual first robust crossing occurs within an exponentially small
fraction of the inverse half-dimension occupation spacing. -/
theorem gaussian_replica_crossing_deadline :
    ∃ b ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      let P := nearHilbertContinuousCircuitBudget K
      ∀ a : ℝ, let σ := ReturnExcursions.Iterated.crossing H P a
        IsLeast {t : ℝ | a≤t ∧ 9/80 ≤ orbitCircuitDistance H P t} σ ∧
          σ-a ≤ b^D*sampleLength k E := by
  obtain ⟨b,hb,h⟩ := gaussian_nearHilbert_duration
  refine ⟨b,hb,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with k hk
  intro K D u H E P a σ
  let L := sampleLength k E
  let T := b^D*L
  have hL : 0 < L := inv_pos.mpr (recordGap_pos k E _)
  have hT : 0 ≤ T := mul_nonneg (pow_nonneg hb.1.le _) hL.le
  have hTL : T ≤ L := mul_le_of_le_one_left hL.le (pow_le_one₀ hb.1.le hb.2.le)
  have hhit : ∃ t ∈ Icc a (a+T), 9/80 ≤ orbitCircuitDistance H P t := by
    by_contra! hall
    have hsub : Icc a (a+T) ⊆ visitSet H P (9/80) := fun t ht =>
      (hasProjectiveCircuitApproximation_iff_infDist ..).mpr (hall t ht).le
    have hh := hk (9/80) (by norm_num) a T hT P le_rfl
    rw [inter_eq_right.mpr hsub,Real.volume_real_Icc_of_le (le_add_of_nonneg_right hT),add_sub_cancel_left,
      max_eq_right hTL] at hh
    exact lt_irrefl T hh
  obtain ⟨t,ht,he⟩ := hhit
  let A := {s : ℝ | a ≤ s ∧ 9/80 ≤ orbitCircuitDistance H P s}
  have hmem : t∈A := ⟨ht.1,he⟩
  have hclosed : IsClosed A := isClosed_Ici.inter
    (isClosed_le continuous_const (orbitCircuitDistance_lipschitz H P).continuous)
  have hleast : IsLeast A σ :=
    ⟨hclosed.csInf_mem ⟨t,hmem⟩ ⟨a,fun _ hx => hx.1⟩,fun _ hx => csInf_le ⟨a,fun _ hy => hy.1⟩ hx⟩
  exact ⟨hleast,by linarith only [hleast.2 hmem,ht.2]⟩

#print axioms gaussian_replica_crossing_deadline
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
