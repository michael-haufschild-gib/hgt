import GaloisForLFunctions.HTGeometry.VectorLawCentralCellCrowding
import GaloisForLFunctions.HTGeometry.ReplicaCrowdingCentralLimitFloor

/-!
# Amplitude-weighted crowding of replica actions in observer space

The replica multiplicity law of order `r` sends a multiplicity vector to the observed action vector
`∑_j p_j v_j` of a low-dimensional observer space.  Coordinatewise this is the scalar replica energy
already treated in the corpus, so the exact variance additivity of the replica law transfers: the
second moment of the observed action about `r` times the single-level mean is `r` times the
single-level observer variance, hence at most `r L²` when every `v_j` has norm at most `L`.

Feeding that into the vector-valued central-cell crowding floor gives the amplitude-weighted
crowding statement: at resolution `δ` the mass of distinct multiplicity pairs with observed actions
closer than `δ` is at least `9/(16 (1 + 8 L√r/δ)^d)` minus the exact collision mass.
-/

open MeasureTheory Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}

theorem euclidean_norm_sq (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

/-- The observed action vector of a replica multiplicity vector. -/
def replicaMultiplicityAction (v : I → EuclideanSpace ℝ (Fin d)) (p : I → ℕ) :
    EuclideanSpace ℝ (Fin d) := ∑ j, (p j : ℝ) • v j

theorem replicaMultiplicityAction_apply (v : I → EuclideanSpace ℝ (Fin d)) (p : I → ℕ)
    (i : Fin d) :
    replicaMultiplicityAction v p i = replicaMultiplicityEnergy (fun j => v j i) p := by
  rw [replicaMultiplicityAction, replicaMultiplicityEnergy]
  simp

/-- The centre of the observed replica action law: `r` times the single-level mean. -/
def replicaActionCentre (weight : I → ℝ) (v : I → EuclideanSpace ℝ (Fin d)) (r : ℕ) :
    EuclideanSpace ℝ (Fin d) := (r : ℝ) • ∑ j, weight j • v j

theorem replicaActionCentre_apply (weight : I → ℝ) (v : I → EuclideanSpace ℝ (Fin d)) (r : ℕ)
    (i : Fin d) :
    replicaActionCentre weight v r i = (r : ℝ) * ∑ j, weight j * v j i := by
  rw [replicaActionCentre]
  simp [Finset.mul_sum]

/-- The weighted variance of a finite law, expanded. -/
theorem weighted_variance_eq {weight : I → ℝ} (hw : ∑ i, weight i = 1) (e : I → ℝ) :
    ∑ i, weight i * (e i - ∑ j, weight j * e j) ^ 2 =
      (∑ i, weight i * e i ^ 2) - (∑ i, weight i * e i) ^ 2 := by
  have hexpand : ∀ i : I, weight i * (e i - ∑ j, weight j * e j) ^ 2
      = weight i * e i ^ 2
        - 2 * (∑ j, weight j * e j) * (weight i * e i)
        + (∑ j, weight j * e j) ^ 2 * weight i := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => hexpand i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hw]
  ring

/-- **The observer second moment of the replica action law.**  It is `r` times the single-level
observer variance. -/
theorem replicaAction_second_moment {weight : I → ℝ} (hw : ∑ i, weight i = 1)
    (v : I → EuclideanSpace ℝ (Fin d)) (r : ℕ) :
    ∑ p : ReplicaMultiplicityIndex I r,
        fidelityReplicaMultiplicityAmplitude weight p.1 *
          ‖replicaMultiplicityAction v p.1 - replicaActionCentre weight v r‖ ^ 2
      = (r : ℝ) * ∑ i : Fin d, singleLevelSpectralVariance weight (fun j => v j i) := by
  classical
  have hcoord : ∀ p : ReplicaMultiplicityIndex I r,
      ‖replicaMultiplicityAction v p.1 - replicaActionCentre weight v r‖ ^ 2 =
        ∑ i : Fin d, (replicaMultiplicityEnergy (fun j => v j i) p.1
          - (r : ℝ) * ∑ j, weight j * v j i) ^ 2 := by
    intro p
    rw [euclidean_norm_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsub : (replicaMultiplicityAction v p.1 - replicaActionCentre weight v r) i =
        replicaMultiplicityAction v p.1 i - replicaActionCentre weight v r i := rfl
    rw [hsub, replicaMultiplicityAction_apply, replicaActionCentre_apply]
  calc ∑ p : ReplicaMultiplicityIndex I r,
        fidelityReplicaMultiplicityAmplitude weight p.1 *
          ‖replicaMultiplicityAction v p.1 - replicaActionCentre weight v r‖ ^ 2
      = ∑ p : ReplicaMultiplicityIndex I r, ∑ i : Fin d,
          fidelityReplicaMultiplicityAmplitude weight p.1 *
            (replicaMultiplicityEnergy (fun j => v j i) p.1
              - (r : ℝ) * ∑ j, weight j * v j i) ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hcoord p, Finset.mul_sum]
    _ = ∑ i : Fin d, ∑ p : ReplicaMultiplicityIndex I r,
          fidelityReplicaMultiplicityAmplitude weight p.1 *
            (replicaMultiplicityEnergy (fun j => v j i) p.1
              - (r : ℝ) * ∑ j, weight j * v j i) ^ 2 := Finset.sum_comm
    _ = ∑ i : Fin d, (r : ℝ) * singleLevelSpectralVariance weight (fun j => v j i) :=
        Finset.sum_congr rfl fun i _ =>
          sum_replicaAmplitude_variance_subtype hw (fun j => v j i) r
    _ = (r : ℝ) * ∑ i : Fin d, singleLevelSpectralVariance weight (fun j => v j i) := by
        rw [Finset.mul_sum]

/-- The total single-level observer variance is at most the squared norm bound. -/
theorem sum_singleLevelSpectralVariance_le {weight : I → ℝ} (hw : ∑ i, weight i = 1)
    (hwnn : ∀ i, 0 ≤ weight i) (v : I → EuclideanSpace ℝ (Fin d)) (L : ℝ)
    (hL : ∀ j, ‖v j‖ ≤ L) :
    ∑ i : Fin d, singleLevelSpectralVariance weight (fun j => v j i) ≤ L ^ 2 := by
  classical
  have hexp : ∀ i : Fin d, singleLevelSpectralVariance weight (fun j => v j i) =
      (∑ j, weight j * (v j i) ^ 2) - (∑ j, weight j * v j i) ^ 2 := by
    intro i
    rw [singleLevelSpectralVariance]
    exact weighted_variance_eq hw (fun j => v j i)
  calc ∑ i : Fin d, singleLevelSpectralVariance weight (fun j => v j i)
      = ∑ i : Fin d, ((∑ j, weight j * (v j i) ^ 2) - (∑ j, weight j * v j i) ^ 2) :=
        Finset.sum_congr rfl fun i _ => hexp i
    _ ≤ ∑ i : Fin d, ∑ j, weight j * (v j i) ^ 2 :=
        Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (∑ j, weight j * v j i)]
    _ = ∑ j, weight j * ‖v j‖ ^ 2 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => by
          rw [euclidean_norm_sq, Finset.mul_sum]
    _ ≤ ∑ j, weight j * L ^ 2 :=
        Finset.sum_le_sum fun j _ => by
          have hsq : ‖v j‖ ^ 2 ≤ L ^ 2 := by nlinarith [norm_nonneg (v j), hL j]
          exact mul_le_mul_of_nonneg_left hsq (hwnn j)
    _ = L ^ 2 := by rw [← Finset.sum_mul, hw, one_mul]


/-- **Theorem B: amplitude-weighted observer crowding of replica actions.**  For every finite
probability weighting, every replica order `r`, every observer dimension `d ≥ 1` and every
resolution `δ > 0`, the mass of ordered pairs of *distinct* multiplicity vectors whose observed
actions are closer than `δ` is at least `9/(16 (1 + 8 L √r / δ)^d)` minus the exact collision
mass. -/
theorem replicaAction_crowding_floor {weight : I → ℝ} (hw : ∑ i, weight i = 1)
    (hwnn : ∀ i, 0 ≤ weight i) (v : I → EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ j, ‖v j‖ ≤ L) (hd : 0 < d) (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (9 : ℝ) / 16 / (1 + 8 * (L * Real.sqrt r) / δ) ^ d -
        vectorLawDiagonalMass
          (fun p : ReplicaMultiplicityIndex I r =>
            fidelityReplicaMultiplicityAmplitude weight p.1) ≤
      vectorLawOffDiagonalWithinMass
        (fun p : ReplicaMultiplicityIndex I r =>
          fidelityReplicaMultiplicityAmplitude weight p.1)
        (fun p : ReplicaMultiplicityIndex I r => replicaMultiplicityAction v p.1) δ := by
  classical
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    refine Module.nontrivial_of_finrank_pos (R := ℝ) ?_
    rw [hrank]
    exact hd
  have hmom : ∑ p : ReplicaMultiplicityIndex I r,
      fidelityReplicaMultiplicityAmplitude weight p.1 *
        ‖replicaMultiplicityAction v p.1 - replicaActionCentre weight v r‖ ^ 2 ≤
      (r : ℝ) * L ^ 2 := by
    rw [replicaAction_second_moment hw v r]
    exact mul_le_mul_of_nonneg_left (sum_singleLevelSpectralVariance_le hw hwnn v L hL)
      (Nat.cast_nonneg r)
  have hVnn : (0 : ℝ) ≤ (r : ℝ) * L ^ 2 := by positivity
  have hsqrt : Real.sqrt ((r : ℝ) * L ^ 2) = L * Real.sqrt r := by
    rw [Real.sqrt_mul (Nat.cast_nonneg r), Real.sqrt_sq hL0, mul_comm]
  have hfloor := vectorLaw_offDiagonal_crowding_floor (E := EuclideanSpace ℝ (Fin d))
    (MeasureTheory.volume)
    (a := fun p : ReplicaMultiplicityIndex I r =>
      fidelityReplicaMultiplicityAmplitude weight p.1)
    (X := fun p : ReplicaMultiplicityIndex I r => replicaMultiplicityAction v p.1)
    (fun p => fidelityReplicaMultiplicityAmplitude_nonneg hwnn p.1)
    (sum_replicaAmplitude_subtype hw r) (replicaActionCentre weight v r) hVnn hmom hδ
  rw [hsqrt, hrank] at hfloor
  exact hfloor

end GaloisForLFunctions.HTGeometry
