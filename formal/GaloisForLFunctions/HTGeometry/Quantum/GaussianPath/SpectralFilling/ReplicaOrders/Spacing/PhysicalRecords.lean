import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.SeparatedMoment
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.FiniteCircuitWindow

/-! # Gate occupation from the diagonal replica moment at inverse spacing -/
open Filter Set Finset MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SharpOccupation
noncomputable section

private theorem capture_of_spacing {I : Type*} [Fintype I] [DecidableEq I] {w : I → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i ≤ 1) (E : I → ℝ) {q : ℕ} (hq : 0 < q)
    {T γ τ : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hgap : ∀ p z : ReplicaMultiplicityIndex I q, p≠z →
      γ ≤ |replicaMultiplicityEnergy E p.val-replicaMultiplicityEnergy E z.val|)
    (J : ℕ) (v : Fin J → I → ℂ) (hv : ∀ j i, ‖v j i‖=1) :
    τ^(2*q)*volume.real (⋃ j, uniformTwistedCoherenceCaptureSet w E (v j) T τ) ≤
      T*J*(96*fidelityReplicaPermutationFloor w q*max 1 (T*γ)⁻¹) := by
  let L := max T γ⁻¹
  have hL : 0 < L := hT.trans_le (le_max_left ..)
  have hLG : 1 ≤ L*γ := (div_le_iff₀ hγ).mp (by simpa only [one_div] using (le_max_right T γ⁻¹))
  have hsep (p z : ReplicaMultiplicityIndex I q) (hpz : p≠z) :
      1 ≤ |L*replicaMultiplicityEnergy E p.val-L*replicaMultiplicityEnergy E z.val| := by
    rw [←mul_sub,abs_mul,abs_of_pos hL]
    exact hLG.trans (mul_le_mul_of_nonneg_left (hgap p z hpz) hL.le)
  let S := ⋃ j, uniformTwistedCoherenceCaptureSet w E (v j) T τ
  let A j := gaussianTwistedCoherenceCaptureSet w E (v j) L τ
  have hsub : S ⊆ Icc (-L) L := iUnion_subset fun j t ht =>
    ⟨(neg_le_neg (le_max_left ..)).trans ht.1.1.le, ht.1.2.trans (le_max_left ..)⟩
  have hobs := volume_window_le_gaussian hL (MeasurableSet.iUnion (fun j =>
    uniformTwistedCoherenceCaptureSet_measurable w E (v j) T τ)) hsub
  have he : (L * ·) ⁻¹' S ⊆ ⋃ j, A j := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (show L*x ∈ S from hx)
    exact mem_iUnion.mpr ⟨j,hj.2⟩
  have hsum := (measureReal_mono (μ:=gaussianReal 0 1) he).trans (measureReal_iUnion_fintype_le A)
  have hvol := hobs.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hterm j := (threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_norm
    hw hw₁ (hv j) q hq (T:=L) hτ).trans (separated_replica_moment E (hv j) q L hsep)
  have hd : T*max 1 (T*γ)⁻¹=L := by
    rw [mul_max_of_nonneg _ _ hT.le,mul_one,mul_inv_rev]
    congr 1
    field_simp
  calc _ ≤ τ^(2*q)*(8*L*∑ j, (gaussianReal 0 1).real (A j)) :=
         mul_le_mul_of_nonneg_left hvol (pow_nonneg hτ _)
       _ = 8*L*∑ j, τ^(2*q)*(gaussianReal 0 1).real (A j) := by rw [←Finset.mul_sum]; ring
       _ ≤ 8*L*∑ _j : Fin J, 12*fidelityReplicaPermutationFloor w q :=
         mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hterm j) (by positivity)
       _ = _ := by rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←hd]; ring

/-- The observed spacing (capped at one) and the deterministic disorder
bound both hold for every nonzero occupation gap. -/
def recordGap {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (E : I → ℝ) (q : ℕ) :=
  max (effectiveGap k q) (intrinsicReplicaActionResolution E q)

theorem recordGap_pos {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (E : I → ℝ) (q : ℕ) :
    0 < recordGap k E q := (effectiveGap_pos k q).trans_le (le_max_left ..)

/-- Individual multiplicity energies are separated simultaneously at the
larger of the observed and deterministic resolutions. -/
theorem gaussian_record_gaps :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues ∘
        (qubitConfigFin (k+3)).symm
      ∀ q : ℕ, ∀ p z : ReplicaMultiplicityIndex (Level k) q, p≠z →
        recordGap k E q ≤ |replicaMultiplicityEnergy E p.val-replicaMultiplicityEnergy E z.val| := by
  filter_upwards [gaussian_effective_replica_gaps,gaussian_path_all_prefixes_maximally_projective] with ω hw hfull
  filter_upwards [hw] with k hk
  intro E q p z hne
  have hrigid := (forall_replicaRigidAt_iff_maximallyProjectiveEnergy E).mpr ((hfull k).comp_equiv _) q
  have hn : replicaMultiplicityEnergy E p.val ≠ replicaMultiplicityEnergy E z.val :=
    fun he => hne (Subtype.ext (hrigid _ p.property _ z.property he))
  exact max_le (multiplicity_gap (hk q) _ p.property _ z.property hn)
    (intrinsicReplicaActionResolution_le E q p.property z.property hn)

/-- Even a record shorter than the inverse detuning pays only the
multiplicative factor max(1,1/(Tγ)) on the diagonal moment. All orders
and circuit nets are allowed on the same infinite disorder draw. -/
theorem gaussian_spaced_gate_window :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      ∀ ε δ ρ : ℝ, 0 < δ → ε+δ ≤ ρ → 0 ≤ ρ → ρ^2 < 2 → ∀ s q : ℕ, 0 < q → ∀ o : ℝ, ∀ T > (0:ℝ),
        let N := ((s:ℝ)+1)*((((K:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s
        visitFraction H s ε o (o+T) ≤
          N*((96*((q.factorial:ℝ)/(D:ℝ)^q)*max 1 (T*recordGap k E q)⁻¹)/(1-ρ^2/2)^(2*q)) := by
  filter_upwards [gaussian_record_gaps] with ω hw
  filter_upwards [hw] with k hk
  intro K D u H E ε δ ρ hδ hnear hρ hsmall s q hq o T hT N
  let w := microcanonicalWeight (Level k)
  have hw₀ (i) : 0 ≤ w i := by dsimp only [w,microcanonicalWeight]; positivity
  let a := max 1 (T*recordGap k E q)⁻¹
  have ha : 0 ≤ a := zero_le_one.trans (le_max_left ..)
  apply gate_fraction_of_capture H hδ hnear hρ hsmall s q o hT (mul_nonneg (by positivity) ha)
  intro J v hv
  have hτ : 0 ≤ 1-ρ^2/2 := by linarith only [hsmall]
  have h := capture_of_spacing hw₀ (sum_microcanonicalWeight_eq_one (Level k)).le E hq hT
    (recordGap_pos k E q) hτ (hk q) J v hv
  have hf := fidelityReplicaPermutationFloor_microcanonical_le (I:=Level k) q
  rw [Fintype.card_fin] at hf
  exact h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hf (by norm_num : (0:ℝ) ≤ 96)) ha) (by positivity))

#print axioms gaussian_spaced_gate_window
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
