import GaloisForLFunctions.HTGeometry.ReplicaObserverActionCrowding
import GaloisForLFunctions.HTGeometry.SoftLightFilterCollisionBound

/-!
# Crowding floor against an explicit collision budget

The amplitude-weighted crowding floor pays the exact replica collision mass.  When the weighting has
been flattened — its largest entry `M` small enough that `r M ≤ 1/12` — that collision mass is below
`12^{-r}`, so the floor becomes an explicit two-term bound in which the negative term is
exponentially small in the replica order while the positive term is only polynomially small in the
observer dimension.

This is the exact shape of the seed-target estimate: the crowded mass cannot be discarded, because
its floor exceeds the collision budget for every sufficiently flat weighting.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}

theorem vectorLawDiagonalMass_replicaAmplitude (weight : I → ℝ) (r : ℕ) :
    vectorLawDiagonalMass
        (fun p : ReplicaMultiplicityIndex I r =>
          fidelityReplicaMultiplicityAmplitude weight p.1)
      = ∑ p ∈ Finset.univ.piAntidiag r, fidelityReplicaMultiplicityAmplitude weight p ^ 2 := by
  classical
  rw [vectorLawDiagonalMass]
  rw [Finset.sum_coe_sort ((Finset.univ : Finset I).piAntidiag r)
    (fun p => fidelityReplicaMultiplicityAmplitude weight p *
      fidelityReplicaMultiplicityAmplitude weight p)]
  exact Finset.sum_congr rfl fun p _ => (sq _).symm

/-- **Corollary C1, equation (19).**  For a flattened weighting the amplitude-weighted crowding
floor becomes an explicit two-term bound: the observer-dimension term minus `12^{-r}`. -/
theorem replicaAction_crowding_floor_of_flat {weight : I → ℝ} (hw : ∑ i, weight i = 1)
    (hwnn : ∀ i, 0 ≤ weight i) (v : I → EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ j, ‖v j‖ ≤ L) (hd : 0 < d) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, weight j ≤ M) (hrM : (r : ℝ) * M ≤ 1 / 12) :
    (9 : ℝ) / 16 / (1 + 8 * (L * Real.sqrt r) / δ) ^ d - (1 / 12 : ℝ) ^ r ≤
      vectorLawOffDiagonalWithinMass
        (fun p : ReplicaMultiplicityIndex I r =>
          fidelityReplicaMultiplicityAmplitude weight p.1)
        (fun p : ReplicaMultiplicityIndex I r => replicaMultiplicityAction v p.1) δ := by
  have hfloor := replicaAction_crowding_floor hw hwnn v L hL0 hL hd r hδ
  have hcoll : vectorLawDiagonalMass
      (fun p : ReplicaMultiplicityIndex I r =>
        fidelityReplicaMultiplicityAmplitude weight p.1) ≤ (1 / 12 : ℝ) ^ r := by
    rw [vectorLawDiagonalMass_replicaAmplitude]
    refine le_trans (replicaCollisionMass_le hwnn hw hM0 hM r) ?_
    exact pow_le_pow_left₀ (by positivity) hrM r
  linarith

end GaloisForLFunctions.HTGeometry
