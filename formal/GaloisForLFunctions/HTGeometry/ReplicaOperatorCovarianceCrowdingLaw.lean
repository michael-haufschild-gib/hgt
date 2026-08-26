import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw
import GaloisForLFunctions.HTGeometry.ReplicaActionCrowdingShortcutLaw

/-!
# Replica operator-covariance crowding law

The Hilbert--Schmidt collision mass controls two independent target cells and
therefore loses a square root in the accessible recurrence horizon.  A
one-cell coarea argument instead needs the largest directional Gaussian
moment.  This file identifies its sharp finite-spectrum invariant: maximum
row multiplicity of exact and unresolved replica actions.

The resulting bound is uniform over every phase twist.  At replica order one
it is an operator-covariance estimate proportional to one inverse spectral
dimension, rather than a square root of a pair-collision estimate.
-/

open scoped BigOperators Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def replicaSameAction
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ)
    (p q : ReplicaMultiplicityIndex I n) : Prop :=
  replicaMultiplicityEnergy energy p.1 =
    replicaMultiplicityEnergy energy q.1

noncomputable instance replicaSameActionDecidable
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) :
    DecidableRel (replicaSameAction energy n) :=
  Classical.decRel _

/-- Maximum number of exactly resonant replica packets in one action row. -/
noncomputable def replicaActionCollisionDegree
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup fun p : ReplicaMultiplicityIndex I n =>
    (Finset.univ.filter (replicaSameAction energy n p)).card

theorem card_filter_replicaSameAction_le_collisionDegree
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ)
    (p : ReplicaMultiplicityIndex I n) :
    (Finset.univ.filter (replicaSameAction energy n p)).card ≤
      replicaActionCollisionDegree energy n := by
  classical
  unfold replicaActionCollisionDegree
  exact Finset.le_sup
    (s := (Finset.univ : Finset (ReplicaMultiplicityIndex I n)))
    (f := fun p => (Finset.univ.filter (replicaSameAction energy n p)).card)
    (Finset.mem_univ p)

theorem fidelityReplicaCollisionMass_eq_subtype
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) :
    fidelityReplicaCollisionMass weight energy n =
      ∑ p : ReplicaMultiplicityIndex I n,
        ∑ q : ReplicaMultiplicityIndex I n,
          if replicaSameAction energy n p q then
            fidelityReplicaMultiplicityWeight weight p.1 q.1
          else 0 := by
  classical
  rw [← fidelityReplicaResonantMass_eq_collisionMass]
  unfold fidelityReplicaResonantMass
  calc
    (∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          if replicaMultiplicityEnergy energy p =
              replicaMultiplicityEnergy energy q then
            fidelityReplicaMultiplicityWeight weight p q
          else 0) =
        ∑ p : ReplicaMultiplicityIndex I n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            if replicaMultiplicityEnergy energy p.1 =
                replicaMultiplicityEnergy energy q then
              fidelityReplicaMultiplicityWeight weight p.1 q
            else 0 := by
      exact Finset.sum_subtype (Finset.univ.piAntidiag n) (by simp) _
    _ = ∑ p : ReplicaMultiplicityIndex I n,
          ∑ q : ReplicaMultiplicityIndex I n,
            if replicaMultiplicityEnergy energy p.1 =
                replicaMultiplicityEnergy energy q.1 then
              fidelityReplicaMultiplicityWeight weight p.1 q.1
            else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_subtype (Finset.univ.piAntidiag n) (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rfl

/-- Exact collision mass is controlled by maximum resonant row multiplicity,
not by total pair count. -/
theorem fidelityReplicaCollisionMass_le_collisionDegree_mul_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) :
    fidelityReplicaCollisionMass weight energy n ≤
      (replicaActionCollisionDegree energy n : ℝ) *
        fidelityReplicaPermutationFloor weight n := by
  classical
  rw [fidelityReplicaCollisionMass_eq_subtype,
    ← fidelityReplicaSubtypePermutationFloor_eq]
  have hsymm : ∀ p q : ReplicaMultiplicityIndex I n,
      replicaSameAction energy n p q → replicaSameAction energy n q p := by
    intro p q hpq
    exact hpq.symm
  have hdegree : ∀ p : ReplicaMultiplicityIndex I n,
      (∑ q, if replicaSameAction energy n p q then (1 : ℝ) else 0) ≤
        (replicaActionCollisionDegree energy n : ℝ) := by
    intro p
    have hcard := card_filter_replicaSameAction_le_collisionDegree energy n p
    calc
      (∑ q, if replicaSameAction energy n p q then (1 : ℝ) else 0) =
          ((Finset.univ.filter (replicaSameAction energy n p)).card : ℝ) := by
            simp
      _ ≤ (replicaActionCollisionDegree energy n : ℝ) := by
        exact_mod_cast hcard
  have hgraph := symmetricRelation_weighted_sum_le_degree_mul_sq
    (replicaSameAction energy n) hsymm
    (fun p : ReplicaMultiplicityIndex I n =>
      fidelityReplicaMultiplicityAmplitude weight p.1)
    (replicaActionCollisionDegree energy n : ℝ) hdegree
  unfold fidelityReplicaSubtypePermutationFloor
  simp_rw [fidelityReplicaMultiplicityWeight_eq_amplitude_mul]
  simpa only [pow_two] using hgraph

/-- Uniform operator-covariance estimate.  Exact and unresolved row degrees
enter additively, while every resolved action is killed by the Gaussian tail. -/
theorem norm_twistedGaussianSpectralFidelityMean_le_rowDegree_mul_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedGaussianSpectralFidelityMean weight energy twist n T‖ ≤
      ((replicaActionCollisionDegree energy n : ℝ) +
          replicaActionCrowdingDegree energy n δ) *
        fidelityReplicaPermutationFloor weight n +
          Real.exp (-((T * δ) ^ 2) / 2) := by
  have hbase := norm_twistedGaussianSpectralFidelityMean_le_collision_add_crowding
    (weight := weight) (energy := energy) (twist := twist)
    hweight hweightSum htwist n hT hδ
  have hcollision := fidelityReplicaCollisionMass_le_collisionDegree_mul_floor
    weight energy n
  have hnear := fidelityReplicaNearActionMass_le_crowdingDegree_mul_floor
    weight energy n δ
  rw [fidelityReplicaSubtypePermutationFloor_eq] at hnear
  calc
    ‖twistedGaussianSpectralFidelityMean weight energy twist n T‖ ≤
        fidelityReplicaCollisionMass weight energy n +
          fidelityReplicaNearActionMass weight energy n δ +
            Real.exp (-((T * δ) ^ 2) / 2) := hbase
    _ ≤ (replicaActionCollisionDegree energy n : ℝ) *
          fidelityReplicaPermutationFloor weight n +
        (replicaActionCrowdingDegree energy n δ : ℝ) *
          fidelityReplicaPermutationFloor weight n +
        Real.exp (-((T * δ) ^ 2) / 2) := by
      exact add_le_add (add_le_add hcollision hnear) (le_refl _)
    _ = ((replicaActionCollisionDegree energy n : ℝ) +
          replicaActionCrowdingDegree energy n δ) *
        fidelityReplicaPermutationFloor weight n +
          Real.exp (-((T * δ) ^ 2) / 2) := by ring

/-- Order-one form: maximum unresolved row multiplicity times coefficient
ℓ² mass.  This is the finite-dimensional Schur operator norm bound used by
one-cell incidence. -/
theorem norm_twistedGaussianSpectralFidelityMean_one_le_rowDegree_mul_sum_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedGaussianSpectralFidelityMean weight energy twist 1 T‖ ≤
      ((replicaActionCollisionDegree energy 1 : ℝ) +
          replicaActionCrowdingDegree energy 1 δ) *
        ∑ i, weight i ^ 2 +
          Real.exp (-((T * δ) ^ 2) / 2) := by
  simpa only [fidelityReplicaPermutationFloor_one_eq_sum_sq] using
    (norm_twistedGaussianSpectralFidelityMean_le_rowDegree_mul_floor
      hweight hweightSum htwist 1 hT hδ)

/-! ## Spectral-index form at operator order one -/

def replicaOneHot {I : Type*} [DecidableEq I] (i : I) : I → ℕ :=
  fun j => if j = i then 1 else 0

theorem replicaOneHot_injective
    {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Injective (replicaOneHot : I → I → ℕ) := by
  intro i j hij
  by_contra hne
  have h := congrFun hij i
  simp [replicaOneHot, hne] at h

theorem replicaMultiplicityEnergy_oneHot
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (i : I) :
    replicaMultiplicityEnergy energy (replicaOneHot i) = energy i := by
  unfold replicaMultiplicityEnergy replicaOneHot
  simp

theorem fidelityReplicaMultiplicityWeight_oneHot
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (i j : I) :
    fidelityReplicaMultiplicityWeight weight (replicaOneHot i) (replicaOneHot j) =
      weight i * weight j := by
  have hmulti (k : I) :
      Nat.multinomial Finset.univ (replicaOneHot k) = 1 := by
    unfold replicaOneHot
    rw [show (fun j : I => if j = k then 1 else 0) = Pi.single k 1 by
      funext j
      simp [Pi.single_apply, eq_comm] ]
    exact Nat.multinomial_single Finset.univ k 1
  unfold fidelityReplicaMultiplicityWeight
  rw [hmulti i, hmulti j]
  simp [replicaOneHot]

theorem fidelityReplicaCollisionMass_one_eq_spectralRows
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) :
    fidelityReplicaCollisionMass weight energy 1 =
      ∑ i, ∑ j, if energy i = energy j then weight i * weight j else 0 := by
  rw [← fidelityReplicaResonantMass_eq_collisionMass]
  unfold fidelityReplicaResonantMass
  rw [piAntidiag_one_eq_image_single]
  change
    (∑ p ∈ Finset.univ.image replicaOneHot,
      ∑ q ∈ Finset.univ.image replicaOneHot,
        if replicaMultiplicityEnergy energy p = replicaMultiplicityEnergy energy q then
          fidelityReplicaMultiplicityWeight weight p q else 0) = _
  rw [Finset.sum_image replicaOneHot_injective.injOn]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_image replicaOneHot_injective.injOn]
  apply Finset.sum_congr rfl
  intro j hj
  rw [replicaMultiplicityEnergy_oneHot, replicaMultiplicityEnergy_oneHot,
    fidelityReplicaMultiplicityWeight_oneHot]

theorem fidelityReplicaNearActionMass_one_eq_spectralRows
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (δ : ℝ) :
    fidelityReplicaNearActionMass weight energy 1 δ =
      ∑ i, ∑ j,
        if 0 < |energy i - energy j| ∧ |energy i - energy j| < δ then
          weight i * weight j else 0 := by
  rw [fidelityReplicaNearActionMass_eq_finset,
    piAntidiag_one_eq_image_single]
  change
    (∑ p ∈ Finset.univ.image replicaOneHot,
      ∑ q ∈ Finset.univ.image replicaOneHot,
        if 0 < |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q| ∧
            |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q| < δ then
          fidelityReplicaMultiplicityWeight weight p q else 0) = _
  rw [Finset.sum_image replicaOneHot_injective.injOn]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_image replicaOneHot_injective.injOn]
  apply Finset.sum_congr rfl
  intro j hj
  rw [replicaMultiplicityEnergy_oneHot, replicaMultiplicityEnergy_oneHot,
    fidelityReplicaMultiplicityWeight_oneHot]

/-- Maximum exact spectral-level multiplicity. -/
noncomputable def spectralCollisionRowDegree
    {I : Type*} [Fintype I] (energy : I → ℝ) : ℕ := by
  classical
  exact Finset.univ.sup fun i =>
    (Finset.univ.filter fun j => energy i = energy j).card

/-- Maximum nonzero unresolved spectral-action multiplicity at resolution `δ`. -/
noncomputable def spectralNearActionRowDegree
    {I : Type*} [Fintype I] (energy : I → ℝ) (δ : ℝ) : ℕ := by
  classical
  exact Finset.univ.sup fun i =>
    (Finset.univ.filter fun j =>
      0 < |energy i - energy j| ∧ |energy i - energy j| < δ).card

theorem card_filter_spectralCollision_le_rowDegree
    {I : Type*} [Fintype I] (energy : I → ℝ) (i : I) :
    (Finset.univ.filter fun j => energy i = energy j).card ≤
      spectralCollisionRowDegree energy := by
  classical
  unfold spectralCollisionRowDegree
  exact Finset.le_sup
    (s := (Finset.univ : Finset I))
    (f := fun i => (Finset.univ.filter fun j => energy i = energy j).card)
    (Finset.mem_univ i)

theorem card_filter_spectralNearAction_le_rowDegree
    {I : Type*} [Fintype I] (energy : I → ℝ) (δ : ℝ) (i : I) :
    (Finset.univ.filter fun j =>
      0 < |energy i - energy j| ∧ |energy i - energy j| < δ).card ≤
      spectralNearActionRowDegree energy δ := by
  classical
  unfold spectralNearActionRowDegree
  exact Finset.le_sup
    (s := (Finset.univ : Finset I))
    (f := fun i => (Finset.univ.filter fun j =>
      0 < |energy i - energy j| ∧ |energy i - energy j| < δ).card)
    (Finset.mem_univ i)

theorem fidelityReplicaCollisionMass_one_le_spectralRowDegree_mul_sum_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) :
    fidelityReplicaCollisionMass weight energy 1 ≤
      (spectralCollisionRowDegree energy : ℝ) * ∑ i, weight i ^ 2 := by
  classical
  rw [fidelityReplicaCollisionMass_one_eq_spectralRows]
  have hsymm : ∀ i j : I, energy i = energy j → energy j = energy i := by
    intro i j h
    exact h.symm
  have hdegree : ∀ i : I,
      (∑ j, if energy i = energy j then (1 : ℝ) else 0) ≤
        (spectralCollisionRowDegree energy : ℝ) := by
    intro i
    have hcard := card_filter_spectralCollision_le_rowDegree energy i
    calc
      (∑ j, if energy i = energy j then (1 : ℝ) else 0) =
          ((Finset.univ.filter fun j => energy i = energy j).card : ℝ) := by simp
      _ ≤ (spectralCollisionRowDegree energy : ℝ) := by exact_mod_cast hcard
  exact symmetricRelation_weighted_sum_le_degree_mul_sq
    (fun i j => energy i = energy j) hsymm weight
    (spectralCollisionRowDegree energy : ℝ) hdegree

theorem fidelityReplicaNearActionMass_one_le_spectralRowDegree_mul_sum_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (δ : ℝ) :
    fidelityReplicaNearActionMass weight energy 1 δ ≤
      (spectralNearActionRowDegree energy δ : ℝ) * ∑ i, weight i ^ 2 := by
  classical
  rw [fidelityReplicaNearActionMass_one_eq_spectralRows]
  let R : I → I → Prop := fun i j =>
    0 < |energy i - energy j| ∧ |energy i - energy j| < δ
  have hsymm : ∀ i j, R i j → R j i := by
    intro i j h
    simpa only [R, abs_sub_comm] using h
  have hdegree : ∀ i : I,
      (∑ j, if R i j then (1 : ℝ) else 0) ≤
        (spectralNearActionRowDegree energy δ : ℝ) := by
    intro i
    have hcard := card_filter_spectralNearAction_le_rowDegree energy δ i
    calc
      (∑ j, if R i j then (1 : ℝ) else 0) =
          ((Finset.univ.filter fun j => R i j).card : ℝ) := by simp [R]
      _ ≤ (spectralNearActionRowDegree energy δ : ℝ) := by exact_mod_cast hcard
  exact symmetricRelation_weighted_sum_le_degree_mul_sq R hsymm weight
    (spectralNearActionRowDegree energy δ : ℝ) hdegree

/-- Spectral-index Schur form of the operator-covariance law. -/
theorem norm_twistedGaussianSpectralFidelityMean_one_le_spectralRowDegree
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedGaussianSpectralFidelityMean weight energy twist 1 T‖ ≤
      ((spectralCollisionRowDegree energy : ℝ) +
          spectralNearActionRowDegree energy δ) *
        ∑ i, weight i ^ 2 +
          Real.exp (-((T * δ) ^ 2) / 2) := by
  have hbase := norm_twistedGaussianSpectralFidelityMean_le_collision_add_crowding
    (weight := weight) (energy := energy) (twist := twist)
    hweight hweightSum htwist 1 hT hδ
  have hcollision :=
    fidelityReplicaCollisionMass_one_le_spectralRowDegree_mul_sum_sq weight energy
  have hnear :=
    fidelityReplicaNearActionMass_one_le_spectralRowDegree_mul_sum_sq weight energy δ
  calc
    ‖twistedGaussianSpectralFidelityMean weight energy twist 1 T‖ ≤
        fidelityReplicaCollisionMass weight energy 1 +
          fidelityReplicaNearActionMass weight energy 1 δ +
            Real.exp (-((T * δ) ^ 2) / 2) := hbase
    _ ≤ (spectralCollisionRowDegree energy : ℝ) * ∑ i, weight i ^ 2 +
        (spectralNearActionRowDegree energy δ : ℝ) * ∑ i, weight i ^ 2 +
          Real.exp (-((T * δ) ^ 2) / 2) :=
      add_le_add (add_le_add hcollision hnear) (le_refl _)
    _ = ((spectralCollisionRowDegree energy : ℝ) +
          spectralNearActionRowDegree energy δ) *
        ∑ i, weight i ^ 2 +
          Real.exp (-((T * δ) ^ 2) / 2) := by ring

end

end GaloisForLFunctions.HTGeometry
