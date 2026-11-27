import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.EffectiveGap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ObservationMeasure
import GaloisForLFunctions.HTGeometry.PhaseTwistedReplicaShortcutActionLaw
import GaloisForLFunctions.HTGeometry.ReplicaCrowdingCentralLimitFloor

/-! # Explicit observation windows for spectral overlap on the frozen chain -/
open Finset Filter Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem multiset_of_occupancy {q : ℕ} {p : I→ℕ} (hp : p ∈ Finset.univ.piAntidiag q) :
    ∃ u : Sym I q, (fun i => u.val.count i)=p := by
  rw [←Finset.map_sym_eq_piAntidiag] at hp
  obtain ⟨u,_,hu⟩ := Finset.mem_map.mp hp
  exact ⟨u,hu⟩

/-- The same multiset detuning controls every active term in the
finite-window expansion, including arbitrary twists of the energy phases. -/
theorem multiplicity_gap {q : ℕ} {E : I→ℝ} {γ : ℝ} (hg : ∀ z : Pair I q, γ ≤ |gap E z|)
    (p : I→ℕ) (hp : p∈Finset.univ.piAntidiag q) (w : I→ℕ) (hw : w∈Finset.univ.piAntidiag q)
    (hne : replicaMultiplicityEnergy E p≠replicaMultiplicityEnergy E w) :
    γ ≤ |replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E w| := by
  obtain ⟨u,hu⟩ := multiset_of_occupancy hp
  obtain ⟨v,hv⟩ := multiset_of_occupancy hw
  have hne' : u≠v := by
    intro he
    subst v
    exact hne (congrArg (replicaMultiplicityEnergy E) (hu.symm.trans hv))
  let z : Pair I q := ⟨(u,v),hne'⟩
  have h := hg z
  unfold gap mode at h
  dsimp only [z] at h
  simpa only [Int.cast_sub,Int.cast_natCast,sub_mul,Finset.sum_sub_distrib,congrFun hu,congrFun hv,
    replicaMultiplicityEnergy] using h

/-- The uniform and Gaussian observers give separate upper bounds on the
same physical interval. The Gaussian error decays quadratically in time
in the exponent. -/
def momentPrice (floor action : ℝ) : ℝ :=
  min (2*(floor+min 1 action⁻¹)) (8*(floor+Real.exp (-action^2/2)))

theorem momentPrice_nonneg {floor action : ℝ} (hf : 0 ≤ floor) (ha : 0 ≤ action) :
    0 ≤ momentPrice floor action :=
  le_min (mul_nonneg (by norm_num) (add_nonneg hf (le_min zero_le_one (inv_nonneg.mpr ha))))
    (mul_nonneg (by norm_num) (add_nonneg hf (Real.exp_pos _).le))

/-- The same explicit disorder event works for every order, every
twist, and every finite target family, chosen after reading the chain. -/
theorem gaussian_replica_capture_windows :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues ∘
        (qubitConfigFin (k+3)).symm
      let D : ℕ := 2^(k+3)
      ∀ q : ℕ, 0 < q → ∀ T > (0:ℝ), ∀ τ ≥ (0:ℝ), ∀ J : ℕ, ∀ v : Fin J→Level k→ℂ,
        (∀ j i, ‖v j i‖=1) →
        τ^(2*q)*volume.real (⋃ j, uniformTwistedCoherenceCaptureSet (microcanonicalWeight (Level k)) E (v j) T τ) ≤
          T*J*momentPrice ((q.factorial:ℝ)/(D:ℝ)^q) (T*effectiveGap k q) := by
  filter_upwards [gaussian_effective_replica_gaps,gaussian_path_all_prefixes_maximally_projective] with ω hw hm
  filter_upwards [hw] with k hk
  intro E D q hq T hT τ hτ J v hv
  let w := microcanonicalWeight (Level k)
  have hp (i : Level k) : 0 < w i := by dsimp only [w,microcanonicalWeight]; positivity
  have hf := (all_fidelityReplicaCollisionMass_eq_floor_iff hp E).mpr ((hm k).comp_equiv _) q
  have hc := fidelityReplicaPermutationFloor_microcanonical_le (I:=Level k) q
  rw [Fintype.card_fin] at hc
  have H := threshold_pow_mul_uniformAdaptiveCoherenceShortcut_measureReal_le
    (weight:=w) (energy:=E) (twist:=v) (fun i => (hp i).le) (sum_microcanonicalWeight_eq_one (Level k))
    hv q hq hT (effectiveGap_pos k q) hτ (multiplicity_gap (hk q))
  rw [hf,Fintype.card_fin] at H
  let S := ⋃ j, uniformTwistedCoherenceCaptureSet w E (v j) T τ
  let A := ⋃ j, gaussianTwistedCoherenceCaptureSet w E (v j) T τ
  have hvol := volume_window_le_gaussian hT
    (show MeasurableSet S from MeasurableSet.iUnion fun _ => uniformTwistedCoherenceCaptureSet_measurable ..)
    (show S ⊆ Icc (-T) T from iUnion_subset fun j t ht => ⟨ht.1.1.le,ht.1.2⟩)
  have hgauss := threshold_pow_mul_gaussianAdaptiveCoherenceShortcut_measureReal_le
    (weight:=w) (energy:=E) (twist:=v) (fun i => (hp i).le) (sum_microcanonicalWeight_eq_one (Level k))
    hv q hq T hT (effectiveGap_pos k q) hτ (multiplicity_gap (hk q))
  rw [hf,Fintype.card_fin] at hgauss
  have hsub : (T * ·) ⁻¹' S ⊆ A := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (show T*x ∈ S from hx)
    exact mem_iUnion.mpr ⟨j,hj.2⟩
  have hs := hvol.trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity))
  rw [momentPrice,mul_min_of_nonneg _ _ (by positivity)]
  apply le_min
  · calc _ ≤ 2*T*J*((q.factorial:ℝ)/(D:ℝ)^q+min 1 (T*effectiveGap k q)⁻¹) :=
           H.trans (mul_le_mul_of_nonneg_left (add_le_add hc le_rfl) (by positivity))
         _ = _ := by ring
  · have hh := hgauss.trans (mul_le_mul_of_nonneg_left (add_le_add hc le_rfl) (Nat.cast_nonneg J))
    calc _ ≤ τ^(2*q)*(8*T*(ProbabilityTheory.gaussianReal 0 1).real A) :=
           mul_le_mul_of_nonneg_left hs (pow_nonneg hτ _)
         _ = 8*T*(τ^(2*q)*(ProbabilityTheory.gaussianReal 0 1).real A) := by ring
         _ ≤ _ := (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 8*T)).trans_eq (by ring)

#print axioms gaussian_replica_capture_windows
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
