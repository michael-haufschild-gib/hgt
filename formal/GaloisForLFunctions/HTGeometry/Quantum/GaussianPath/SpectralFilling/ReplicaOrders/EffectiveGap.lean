import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.FrozenGaps
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.ModeHeights

/-! # Two physical detuning bounds at every replica order -/
open Filter MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SpectralJets.AllHeights
noncomputable section

/-- Fixed-order polynomial elimination and the all-height derivative estimate
apply to the same occupation differences on the same frozen prefix. -/
def effectiveGap (k q : ℕ) := max (replicaGap k q) (heightMargin k q)

theorem effectiveGap_pos (k q : ℕ) : 0 < effectiveGap k q :=
  (replicaGap_pos k q).trans_le (le_max_left ..)

private theorem mode_height {I : Type*} [DecidableEq I] {q : ℕ} (p : Pair I q) (i : I) :
    (mode p i).natAbs ≤ q := by
  have hu := (Multiset.count_le_card i p.val.1.val).trans_eq p.val.1.property
  have hv := (Multiset.count_le_card i p.val.2.val).trans_eq p.val.2.property
  unfold mode
  omega

/-- The polynomial bound can be used at small orders and the height
bound at large orders without changing the draw or the prefix cutoff. -/
theorem gaussian_effective_replica_gaps :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ q : ℕ, ∀ p : Pair (Level k) q, effectiveGap k q ≤ |gap (E ∘ (qubitConfigFin (k+3)).symm) p| := by
  filter_upwards [gaussian_frozen_replica_gaps,gaussian_all_heights,gaussian_path_all_prefixes_maximally_projective]
    with ω h₁ h₂ hspec
  filter_upwards [h₁,h₂] with k hk₁ hk₂
  intro E q p
  let e := qubitConfigFin (k+3)
  let m := mode p
  have hb : ∑ i, m i=0 := by
    change (∑ i, ((p.val.1.val.count i:ℤ)-(p.val.2.val.count i:ℤ)))=0
    rw [Finset.sum_sub_distrib,←Nat.cast_sum,←Nat.cast_sum,count_sum,count_sum,sub_self]
  have hn : m ∘ e ≠ 0 := by
    intro hz
    have hzero (i) : mode p i=0 := by
      simpa only [Function.comp_apply,m,e.apply_symm_apply,Pi.zero_apply] using congrFun hz (e.symm i)
    apply gap_ne_zero ((hspec k).comp_equiv e.symm) p
    simp only [gap,hzero,Int.cast_zero,zero_mul,Finset.sum_const_zero]
  have h := hk₂ q (m ∘ e) hn ((Equiv.sum_comp e m).trans hb) (fun i => mode_height p (e i))
  apply max_le (hk₁ q p)
  rw [gap,←Equiv.sum_comp e (fun i => (mode p i:ℝ)*(E ∘ e.symm) i)]
  simpa only [Function.comp_apply,e.symm_apply_apply,m] using h

#print axioms gaussian_effective_replica_gaps
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
