import GaloisForLFunctions.HTGeometry.ReplicaActionCrowdingShortcutLaw
import GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiShortcutActionLaw

/-!
# Direct adaptive static-Choi crowding law

This module replaces worst-nonzero-action resolution in adaptive Choi and
padded-circuit shortcut bounds by local replica-action crowding.  Under
maximal projective spectral rank, exact collisions and each unresolved
near-action neighbor both cost at most one `r! d⁻ʳ` permutation-floor unit.
The target may be selected after time is observed.
-/

open scoped BigOperators ComplexConjugate Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem replicaNearAction_neg_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p q : ReplicaMultiplicityIndex I n) :
    replicaNearAction (fun i => -energy i) n δ p q ↔
      replicaNearAction energy n δ p q := by
  unfold replicaNearAction
  rw [replicaMultiplicityEnergy_neg energy p.1,
    replicaMultiplicityEnergy_neg energy q.1]
  rw [show -replicaMultiplicityEnergy energy p.1 -
      -replicaMultiplicityEnergy energy q.1 =
        -(replicaMultiplicityEnergy energy p.1 -
          replicaMultiplicityEnergy energy q.1) by ring, abs_neg]

theorem replicaActionCrowdingDegree_neg
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ) :
    replicaActionCrowdingDegree (fun i => -energy i) n δ =
      replicaActionCrowdingDegree energy n δ := by
  classical
  unfold replicaActionCrowdingDegree
  apply Finset.sup_congr rfl
  intro p hp
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact replicaNearAction_neg_iff energy n δ p q

theorem directStaticChoiTarget_floor_le_factorial_inv_pow
    {d : ℕ} (hd : 0 < d)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) (n : ℕ) :
    fidelityReplicaPermutationFloor
        (directStaticChoiTargetWeight d target) n ≤
      (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n := by
  exact (fidelityReplicaPermutationFloor_le_factorial_mul_sum_sq_pow
    (directStaticChoiTargetWeight_nonneg target) n).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity)
          (sum_sq_directStaticChoiTargetWeight_le_inv hd htarget) n)
        (by positivity))

theorem gaussian_directStaticChoiTargetShortcut_crowdingLaw
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianStaticChoiTargetCaptureSet energy target T epsilon) ≤
      (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        (replicaActionCrowdingDegree energy n δ : ℝ) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
        Real.exp (-((T * δ) ^ 2) / 2) := by
  let weight := directStaticChoiTargetWeight d target
  let negEnergy : Fin d → ℝ := fun i => -energy i
  let twist := directStaticChoiTargetTwist target
  let threshold := Real.sqrt (1 - epsilon ^ 2)
  have hsubset :
      gaussianStaticChoiTargetCaptureSet energy target T epsilon ⊆
        gaussianTwistedCoherenceCaptureSet weight negEnergy twist T threshold :=
    gaussianStaticChoiTargetCapture_subset_directCoherence hd htarget
      hepsilon hepsilonOne
  have hpow : 0 ≤ threshold ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianStaticChoiTargetCaptureSet energy target T epsilon) ≤
      threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianTwistedCoherenceCaptureSet weight negEnergy twist T threshold) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hpow
    _ ≤ fidelityReplicaCollisionMass weight negEnergy n +
        (replicaActionCrowdingDegree negEnergy n δ : ℝ) *
          fidelityReplicaPermutationFloor weight n +
        Real.exp (-((T * δ) ^ 2) / 2) := by
      exact threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_degree_floor
        (directStaticChoiTargetWeight_nonneg target)
        (sum_directStaticChoiTargetWeight_le_one hd htarget)
        (norm_directStaticChoiTargetTwist target) n hn hT hδ
        (Real.sqrt_nonneg _)
    _ ≤ (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        (replicaActionCrowdingDegree negEnergy n δ : ℝ) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
        Real.exp (-((T * δ) ^ 2) / 2) := by
      have hcollision := directStaticChoiTarget_collision_le_factorial_inv_pow
        hd hmax htarget n
      have hfloor := directStaticChoiTarget_floor_le_factorial_inv_pow
        hd htarget n
      have hk : 0 ≤ (replicaActionCrowdingDegree negEnergy n δ : ℝ) := by
        positivity
      gcongr
    _ = (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        (replicaActionCrowdingDegree energy n δ : ℝ) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
        Real.exp (-((T * δ) ^ 2) / 2) := by
      rw [replicaActionCrowdingDegree_neg]

theorem uniform_directStaticChoiTargetShortcut_crowdingLaw
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        volume.real
          (uniformStaticChoiTargetCaptureSet energy target T epsilon) ≤
      2 * T *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := by
  let weight := directStaticChoiTargetWeight d target
  let negEnergy : Fin d → ℝ := fun i => -energy i
  let twist := directStaticChoiTargetTwist target
  let threshold := Real.sqrt (1 - epsilon ^ 2)
  have hsubset :
      uniformStaticChoiTargetCaptureSet energy target T epsilon ⊆
        uniformTwistedCoherenceCaptureSet weight negEnergy twist T threshold :=
    uniformStaticChoiTargetCapture_subset_directCoherence hd htarget
      hepsilon hepsilonOne
  have hwindow :
      uniformTwistedCoherenceCaptureSet weight negEnergy twist T threshold ⊆
        Set.Ioc (-T) T := fun t ht => ht.1
  have hfinite :
      volume (uniformTwistedCoherenceCaptureSet
        weight negEnergy twist T threshold) ≠ ∞ :=
    ne_of_lt ((measure_mono hwindow).trans_lt measure_Ioc_lt_top)
  have hpow : 0 ≤ threshold ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    threshold ^ (2 * n) *
        volume.real
          (uniformStaticChoiTargetCaptureSet energy target T epsilon) ≤
      threshold ^ (2 * n) *
        volume.real
          (uniformTwistedCoherenceCaptureSet weight negEnergy twist T threshold) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset hfinite) hpow
    _ ≤ 2 * T *
        (fidelityReplicaCollisionMass weight negEnergy n +
          (replicaActionCrowdingDegree negEnergy n δ : ℝ) *
            fidelityReplicaPermutationFloor weight n +
          min 1 (T * δ)⁻¹) := by
      exact threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le_degree_floor
        (directStaticChoiTargetWeight_nonneg target)
        (sum_directStaticChoiTargetWeight_le_one hd htarget)
        (norm_directStaticChoiTargetTwist target) n hn hT hδ
        (Real.sqrt_nonneg _)
    _ ≤ 2 * T *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree negEnergy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hT.le)
      have hcollision := directStaticChoiTarget_collision_le_factorial_inv_pow
        hd hmax htarget n
      have hfloor := directStaticChoiTarget_floor_le_factorial_inv_pow
        hd htarget n
      have hk : 0 ≤ (replicaActionCrowdingDegree negEnergy n δ : ℝ) := by
        positivity
      gcongr
    _ = 2 * T *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := by
      rw [replicaActionCrowdingDegree_neg]

theorem gaussian_directAdaptiveStaticChoiTargetShortcut_crowdingLaw
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
  have hpow : 0 ≤ Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        ∑ w : W, (gaussianReal 0 1).real
          (gaussianStaticChoiTargetCaptureSet energy (target w) T epsilon) :=
      mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le _) hpow
    _ = ∑ w : W, Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianStaticChoiTargetCaptureSet energy (target w) T epsilon) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _w : W,
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
      apply Finset.sum_le_sum
      intro w hw
      exact gaussian_directStaticChoiTargetShortcut_crowdingLaw
        hd hmax (htarget w) n hn hT hδ hepsilon hepsilonOne
    _ = (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
      simp
      ring

theorem uniform_directAdaptiveStaticChoiTargetShortcut_crowdingLaw
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      2 * T * (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := by
  have hpow : 0 ≤ Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        ∑ w : W, volume.real
          (uniformStaticChoiTargetCaptureSet energy (target w) T epsilon) :=
      mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le _) hpow
    _ = ∑ w : W, Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        volume.real
          (uniformStaticChoiTargetCaptureSet energy (target w) T epsilon) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _w : W, 2 * T *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := by
      apply Finset.sum_le_sum
      intro w hw
      exact uniform_directStaticChoiTargetShortcut_crowdingLaw
        hd hmax (htarget w) n hn hT hδ hepsilon hepsilonOne
    _ = 2 * T * (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := by
      simp
      ring

theorem gaussian_directAdaptiveStaticChoiTargetShortcut_crowdingProbability_le
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
  rw [← sqrt_one_sub_sq_pow_two_mul hepsilon hepsilonOne n]
  exact gaussian_directAdaptiveStaticChoiTargetShortcut_crowdingLaw
    hd hmax target htarget n hn hT hδ hepsilon hepsilonOne

theorem uniform_directAdaptiveStaticChoiTargetShortcut_crowdingProbability_le
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) / (2 * T)) ≤
      (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := by
  have hmain := uniform_directAdaptiveStaticChoiTargetShortcut_crowdingLaw
    hd hmax target htarget n hn hT hδ hepsilon hepsilonOne
  rw [sqrt_one_sub_sq_pow_two_mul hepsilon hepsilonOne n] at hmain
  have h2T : 0 < 2 * T := mul_pos (by norm_num) hT
  rw [← mul_div_assoc]
  apply (div_le_iff₀ h2T).2
  calc
    (1 - epsilon ^ 2) ^ n *
        volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      2 * T * (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := hmain
    _ = (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) * (2 * T) := by ring

theorem gaussian_directAdaptivePaddedCircuitShortcut_crowdingProbability_le
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
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    gaussian_directAdaptiveStaticChoiTargetShortcut_crowdingProbability_le
      hd hmax target htarget n hn hT hδ hepsilon hepsilonOne

theorem uniform_directAdaptivePaddedCircuitShortcut_crowdingProbability_le
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
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
          min 1 (T * δ)⁻¹) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    uniform_directAdaptiveStaticChoiTargetShortcut_crowdingProbability_le
      hd hmax target htarget n hn hT hδ hepsilon hepsilonOne

end RHTower
