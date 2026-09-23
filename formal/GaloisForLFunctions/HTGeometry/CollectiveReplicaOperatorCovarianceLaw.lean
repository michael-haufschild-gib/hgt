import GaloisForLFunctions.HTGeometry.HistogramCentralizerDimension
import GaloisForLFunctions.HTGeometry.ReplicaOperatorCovarianceCrowdingLaw

/-!
# Collective-replica operator covariance

Ordered replica tuples contain permutation sheets above each multiplicity
histogram.  This file proves that those sheets cost at most `r!` in every
exact or unresolved action row.  Combining this finite-fibre theorem with
the operator-covariance Schur bound converts multiplicity-space crowding into
a uniform directional bound on the full ordered replica Hilbert space.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Under maximal projective rank, every collective-energy row consists of
one histogram fibre and hence has at most `r!` ordered sheets. -/
theorem spectralCollisionRowDegree_collectiveReplicaEnergy_le_factorial
    {I : Type*} [Fintype I] [DecidableEq I]
    {energy : I → ℝ} (henergy : MaximallyProjectiveEnergy energy) (r : ℕ) :
    spectralCollisionRowDegree
        (collectiveReplicaEnergy energy : (Fin r → I) → ℝ) ≤
      r.factorial := by
  classical
  unfold spectralCollisionRowDegree
  apply Finset.sup_le
  intro α hα
  have hfilt :
      (Finset.univ.filter fun β : Fin r → I =>
        collectiveReplicaEnergy energy α = collectiveReplicaEnergy energy β) =
      (Finset.univ.filter fun β : Fin r → I =>
        orderedReplicaMultiplicity β = orderedReplicaMultiplicity α) := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [collectiveReplicaEnergy_eq_iff_multiplicity_eq henergy]
    exact eq_comm
  rw [hfilt,
    card_fiber_orderedReplicaMultiplicity
      (orderedReplicaMultiplicity_mem_piAntidiag α)]
  exact multinomial_le_factorial
    (Finset.mem_piAntidiag.mp
      (orderedReplicaMultiplicity_mem_piAntidiag α)).1

/-- Every unresolved multiplicity-space action row lifts to at most `r!`
ordered sheets per histogram. -/
theorem card_filter_collectiveReplicaEnergy_nearAction_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (r : ℕ) (δ : ℝ) (α : Fin r → I) :
    (Finset.univ.filter fun β : Fin r → I =>
      0 < |collectiveReplicaEnergy energy α - collectiveReplicaEnergy energy β| ∧
      |collectiveReplicaEnergy energy α - collectiveReplicaEnergy energy β| < δ).card ≤
      r.factorial * replicaActionCrowdingDegree energy r δ := by
  classical
  let S := Finset.univ.filter fun β : Fin r → I =>
    0 < |collectiveReplicaEnergy energy α - collectiveReplicaEnergy energy β| ∧
    |collectiveReplicaEnergy energy α - collectiveReplicaEnergy energy β| < δ
  let pα : ReplicaMultiplicityIndex I r :=
    ⟨orderedReplicaMultiplicity α, orderedReplicaMultiplicity_mem_piAntidiag α⟩
  have hmaps : Set.MapsTo orderedReplicaMultiplicity
      (↑S : Set (Fin r → I))
      (↑((Finset.univ : Finset I).piAntidiag r) : Set (I → ℕ)) := by
    intro β hβ
    exact orderedReplicaMultiplicity_mem_piAntidiag β
  rw [show (Finset.univ.filter fun β : Fin r → I =>
      0 < |collectiveReplicaEnergy energy α - collectiveReplicaEnergy energy β| ∧
      |collectiveReplicaEnergy energy α - collectiveReplicaEnergy energy β| < δ) = S from rfl]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    (∑ p ∈ Finset.univ.piAntidiag r,
        (S.filter fun β => orderedReplicaMultiplicity β = p).card) ≤
      ∑ p ∈ Finset.univ.piAntidiag r,
        if 0 < |replicaMultiplicityEnergy energy pα.1 -
              replicaMultiplicityEnergy energy p| ∧
            |replicaMultiplicityEnergy energy pα.1 -
              replicaMultiplicityEnergy energy p| < δ
        then r.factorial else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hnear :
          0 < |replicaMultiplicityEnergy energy pα.1 -
                replicaMultiplicityEnergy energy p| ∧
              |replicaMultiplicityEnergy energy pα.1 -
                replicaMultiplicityEnergy energy p| < δ
      · rw [if_pos hnear]
        calc
          (S.filter fun β => orderedReplicaMultiplicity β = p).card ≤
              (Finset.univ.filter fun β : Fin r → I =>
                orderedReplicaMultiplicity β = p).card := by
            apply Finset.card_le_card
            intro β hβ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact (Finset.mem_filter.mp hβ).2
          _ = Nat.multinomial Finset.univ p :=
            card_fiber_orderedReplicaMultiplicity hp
          _ ≤ r.factorial := multinomial_le_factorial
            (Finset.mem_piAntidiag.mp hp).1
      · rw [if_neg hnear]
        simp only [Nat.le_zero]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro β hS hpβ
        have hnearβ := (Finset.mem_filter.mp hS).2
        apply hnear
        simpa only [pα, collectiveReplicaEnergy_eq_sum_multiplicity, hpβ] using hnearβ
    _ = r.factorial *
        ((Finset.univ.piAntidiag r).filter fun p =>
          0 < |replicaMultiplicityEnergy energy pα.1 -
                replicaMultiplicityEnergy energy p| ∧
              |replicaMultiplicityEnergy energy pα.1 -
                replicaMultiplicityEnergy energy p| < δ).card := by
      rw [Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp
    _ ≤ r.factorial * replicaActionCrowdingDegree energy r δ := by
      apply Nat.mul_le_mul_left
      let Q := Finset.univ.filter (replicaNearAction energy r δ pα)
      have hcardQ := card_filter_replicaNearAction_le_crowdingDegree
        energy r δ pα
      let A := ((Finset.univ : Finset I).piAntidiag r).filter fun p =>
        0 < |replicaMultiplicityEnergy energy pα.1 -
              replicaMultiplicityEnergy energy p| ∧
            |replicaMultiplicityEnergy energy pα.1 -
              replicaMultiplicityEnergy energy p| < δ
      have hAQ : A.card ≤ Q.card := by
        rw [← Finset.card_attach]
        apply Finset.card_le_card_of_injOn
          (fun p : {x // x ∈ A} =>
            (⟨p.1, (Finset.mem_filter.mp p.2).1⟩ : ReplicaMultiplicityIndex I r))
        · intro p hp
          change (⟨p.1, (Finset.mem_filter.mp p.2).1⟩ :
            ReplicaMultiplicityIndex I r) ∈ Q
          simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and,
            replicaNearAction]
          exact (Finset.mem_filter.mp p.2).2
        · intro p hp q hq hpq
          have hv : (p.1 : I → ℕ) = q.1 :=
            congrArg (fun z : ReplicaMultiplicityIndex I r => z.1) hpq
          exact Subtype.ext hv
      exact hAQ.trans hcardQ

theorem spectralNearActionRowDegree_collectiveReplicaEnergy_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (r : ℕ) (δ : ℝ) :
    spectralNearActionRowDegree
        (collectiveReplicaEnergy energy : (Fin r → I) → ℝ) δ ≤
      r.factorial * replicaActionCrowdingDegree energy r δ := by
  classical
  unfold spectralNearActionRowDegree
  apply Finset.sup_le
  intro α hα
  exact card_filter_collectiveReplicaEnergy_nearAction_le energy r δ α

/-- **Collective-replica operator-covariance law.**  Every direction in the
ordered replica Hilbert space obeys the same row bound.  The permutation
sheets cost `r!`; all further loss is the intrinsic multiplicity-space
near-action crowding degree. -/
theorem norm_twistedGaussian_collectiveReplicaMean_one_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {energy : I → ℝ} (henergy : MaximallyProjectiveEnergy energy)
    {r : ℕ}
    {weight : (Fin r → I) → ℝ} {twist : (Fin r → I) → ℂ}
    (hweight : ∀ α, 0 ≤ weight α)
    (hweightSum : ∑ α, weight α ≤ 1)
    (htwist : ∀ α, ‖twist α‖ = 1)
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedGaussianSpectralFidelityMean weight
        (collectiveReplicaEnergy energy) twist 1 T‖ ≤
      (r.factorial : ℝ) *
          (1 + replicaActionCrowdingDegree energy r δ) *
          ∑ α, weight α ^ (2 : ℕ) +
        Real.exp (-((T * δ) ^ (2 : ℕ)) / 2) := by
  have hbase := norm_twistedGaussianSpectralFidelityMean_one_le_spectralRowDegree
    (energy := collectiveReplicaEnergy energy) hweight hweightSum htwist hT hδ
  have hcollision :=
    spectralCollisionRowDegree_collectiveReplicaEnergy_le_factorial henergy r
  have hnear :=
    spectralNearActionRowDegree_collectiveReplicaEnergy_le energy r δ
  have hcollisionR :
      (spectralCollisionRowDegree
        (collectiveReplicaEnergy energy : (Fin r → I) → ℝ) : ℝ) ≤
        (r.factorial : ℝ) := by
    exact_mod_cast hcollision
  have hnearR :
      (spectralNearActionRowDegree
        (collectiveReplicaEnergy energy : (Fin r → I) → ℝ) δ : ℝ) ≤
        (r.factorial : ℝ) * replicaActionCrowdingDegree energy r δ := by
    exact_mod_cast hnear
  have hsq : 0 ≤ ∑ α, weight α ^ (2 : ℕ) :=
    Finset.sum_nonneg fun α hα => sq_nonneg _
  calc
    ‖twistedGaussianSpectralFidelityMean weight
        (collectiveReplicaEnergy energy) twist 1 T‖ ≤
      ((spectralCollisionRowDegree
          (collectiveReplicaEnergy energy : (Fin r → I) → ℝ) : ℝ) +
        spectralNearActionRowDegree
          (collectiveReplicaEnergy energy : (Fin r → I) → ℝ) δ) *
          ∑ α, weight α ^ (2 : ℕ) +
        Real.exp (-((T * δ) ^ (2 : ℕ)) / 2) := hbase
    _ ≤ ((r.factorial : ℝ) +
          (r.factorial : ℝ) * replicaActionCrowdingDegree energy r δ) *
          ∑ α, weight α ^ (2 : ℕ) +
        Real.exp (-((T * δ) ^ (2 : ℕ)) / 2) := by
      gcongr
    _ = (r.factorial : ℝ) *
          (1 + replicaActionCrowdingDegree energy r δ) *
          ∑ α, weight α ^ (2 : ℕ) +
        Real.exp (-((T * δ) ^ (2 : ℕ)) / 2) := by ring

end

end GaloisForLFunctions.HTGeometry
