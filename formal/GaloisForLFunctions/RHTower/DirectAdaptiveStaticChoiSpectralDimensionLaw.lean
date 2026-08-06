import GaloisForLFunctions.HTGeometry.ReplicaCrowdingSpectralDimensionLaw
import GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiCrowdingLaw

/-!
# Adaptive circuit shortcuts obey spectral-dimension crowding

For static Hamiltonian Choi orbits, the probability of matching any target selected from a
padded circuit dictionary is bounded by circuit entropy times a collision term, a finite-window
spectral-dimension term, and the averaging remainder.  The result is invariant under reversing
the spectrum and contains no global minimum-gap assumption.
-/

open scoped BigOperators ComplexConjugate Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem replicaNearDifferenceSet_neg
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p : ReplicaMultiplicityIndex I n) :
    replicaNearDifferenceSet (fun i => -energy i) n δ p =
      replicaNearDifferenceSet energy n δ p := by
  classical
  have hfilter :
      Finset.univ.filter
          (replicaNearAction (fun i => -energy i) n δ p) =
        Finset.univ.filter (replicaNearAction energy n δ p) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact replicaNearAction_neg_iff energy n δ p q
  unfold replicaNearDifferenceSet
  rw [hfilter]

theorem replicaNearActionRankAt_neg
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p : ReplicaMultiplicityIndex I n) :
    replicaNearActionRankAt (fun i => -energy i) n δ p =
      replicaNearActionRankAt energy n δ p := by
  unfold replicaNearActionRankAt
  rw [replicaNearDifferenceSet_neg energy n δ p]

theorem replicaNearActionRank_neg
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ) :
    replicaNearActionRank (fun i => -energy i) n δ =
      replicaNearActionRank energy n δ := by
  classical
  unfold replicaNearActionRank
  apply Finset.sup_congr rfl
  intro p hp
  exact replicaNearActionRankAt_neg energy n δ p

theorem gaussian_directAdaptivePaddedCircuitShortcut_spectralDimensionProbability_le
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (gaussianReal 0 1).real
          (⋃ w : PaddedCircuitWord gate s,
            gaussianStaticChoiTargetCaptureSet
              energy (target w) T epsilon) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
  have hdegreeNat := replicaActionCrowdingDegree_le_pow_rank energy n δ
  have hdegree : (replicaActionCrowdingDegree energy n δ : ℝ) ≤
      (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) := by
    exact_mod_cast hdegreeNat
  have hfloor : 0 ≤ (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n := by
    positivity
  exact (gaussian_directAdaptivePaddedCircuitShortcut_crowdingProbability_le
      hd hmax s target htarget n hn hT hδ hepsilon hepsilonOne).trans (by
        gcongr)

theorem uniform_directAdaptivePaddedCircuitShortcut_spectralDimensionProbability_le
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (volume.real
          (⋃ w : PaddedCircuitWord gate s,
            uniformStaticChoiTargetCaptureSet
              energy (target w) T epsilon) / (2 * T)) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := by
  have hdegreeNat := replicaActionCrowdingDegree_le_pow_rank energy n δ
  have hdegree : (replicaActionCrowdingDegree energy n δ : ℝ) ≤
      (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) := by
    exact_mod_cast hdegreeNat
  have hfloor : 0 ≤ (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n := by
    positivity
  exact (uniform_directAdaptivePaddedCircuitShortcut_crowdingProbability_le
      hd hmax s target htarget n hn hT hδ hepsilon hepsilonOne).trans (by
        gcongr)

theorem exists_directAdaptivePaddedCircuitHardTime_of_spectralDimensionBudget
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
              ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
            min 1 (T * δ)⁻¹) <
        (1 - epsilon ^ 2) ^ n) :
    ∃ t ∈ Set.Ioc (-T) T,
      ∀ w : PaddedCircuitWord gate s,
        t ∉ staticChoiTargetCaptureSet energy (target w) epsilon := by
  have hmain :=
    uniform_directAdaptivePaddedCircuitShortcut_spectralDimensionProbability_le
      hd hmax s target htarget n hn hT hδ hepsilon hepsilonOne
  by_contra hnone
  push Not at hnone
  have hunion :
      (⋃ w : PaddedCircuitWord gate s,
          uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) = Set.Ioc (-T) T := by
    apply Set.Subset.antisymm
    · intro t ht
      simp only [Set.mem_iUnion] at ht
      obtain ⟨w, hw⟩ := ht
      exact hw.2
    · intro t ht
      obtain ⟨w, hw⟩ := hnone t ht
      simp only [Set.mem_iUnion]
      exact ⟨w, hw, ht⟩
  rw [hunion] at hmain
  have hmeasure : volume.real (Set.Ioc (-T) T) / (2 * T) = 1 := by
    rw [Real.volume_real_Ioc]
    rw [max_eq_left]
    · field_simp
      ring
    · linarith
  rw [hmeasure, mul_one] at hmain
  exact (not_lt_of_ge hmain) hbudget

end RHTower
