import GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiCrowdingLaw

/-!
# Target-weighted replica crowding for adaptive static Choi shortcuts

The maximum crowding degree is avoidable.  This module retains the exact near-action mass induced
by each normalized Choi target and sums those masses only after the adaptive circuit union.  The
resulting resonance partition function is always bounded by the earlier degree-floor term, while
the Gaussian, uniform, padded-circuit, and hard-time laws hold directly with the sharper quantity.
-/

open scoped BigOperators ComplexConjugate Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable def directStaticChoiTargetNearActionMass
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  fidelityReplicaNearActionMass
    (directStaticChoiTargetWeight d target) (fun i => -energy i) n δ

noncomputable def directAdaptiveChoiNearActionPartition
    {d : ℕ} {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∑ w, directStaticChoiTargetNearActionMass (target w) energy n δ

theorem directStaticChoiTargetNearActionMass_le_degree_floor
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) (n : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass target energy n δ ≤
      (replicaActionCrowdingDegree energy n δ : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) := by
  have hnear := fidelityReplicaNearActionMass_le_crowdingDegree_mul_floor
    (directStaticChoiTargetWeight d target) (fun i => -energy i) n δ
  rw [fidelityReplicaSubtypePermutationFloor_eq] at hnear
  have hfloor := directStaticChoiTarget_floor_le_factorial_inv_pow
    hd htarget n
  have hk : 0 ≤
      (replicaActionCrowdingDegree (fun i => -energy i) n δ : ℝ) := by
    positivity
  calc
    directStaticChoiTargetNearActionMass target energy n δ ≤
        (replicaActionCrowdingDegree (fun i => -energy i) n δ : ℝ) *
          fidelityReplicaPermutationFloor
            (directStaticChoiTargetWeight d target) n := hnear
    _ ≤ (replicaActionCrowdingDegree (fun i => -energy i) n δ : ℝ) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) :=
      mul_le_mul_of_nonneg_left hfloor hk
    _ = _ := by rw [replicaActionCrowdingDegree_neg]

theorem directAdaptiveChoiNearActionPartition_le_degree_floor
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (δ : ℝ) :
    directAdaptiveChoiNearActionPartition target energy n δ ≤
      (Fintype.card W : ℝ) *
        ((replicaActionCrowdingDegree energy n δ : ℝ) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n)) := by
  unfold directAdaptiveChoiNearActionPartition
  calc
    ∑ w, directStaticChoiTargetNearActionMass (target w) energy n δ ≤
        ∑ _w : W, (replicaActionCrowdingDegree energy n δ : ℝ) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) := by
      apply Finset.sum_le_sum
      intro w hw
      exact directStaticChoiTargetNearActionMass_le_degree_floor
        hd (htarget w) n δ
    _ = _ := by simp

theorem gaussian_directStaticChoiTargetShortcut_weightedCrowdingLaw
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
        directStaticChoiTargetNearActionMass target energy n δ +
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
    _ ≤ ‖twistedGaussianSpectralFidelityMean
        weight negEnergy twist n T‖ :=
      threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_norm
        (directStaticChoiTargetWeight_nonneg target)
        (sum_directStaticChoiTargetWeight_le_one hd htarget)
        (norm_directStaticChoiTargetTwist target) n hn (Real.sqrt_nonneg _)
    _ ≤ fidelityReplicaCollisionMass weight negEnergy n +
        fidelityReplicaNearActionMass weight negEnergy n δ +
        Real.exp (-((T * δ) ^ 2) / 2) :=
      norm_twistedGaussianSpectralFidelityMean_le_collision_add_crowding
        (directStaticChoiTargetWeight_nonneg target)
        (sum_directStaticChoiTargetWeight_le_one hd htarget)
        (norm_directStaticChoiTargetTwist target) n hT hδ
    _ ≤ (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        fidelityReplicaNearActionMass weight negEnergy n δ +
        Real.exp (-((T * δ) ^ 2) / 2) := by
      gcongr
      exact directStaticChoiTarget_collision_le_factorial_inv_pow
        hd hmax htarget n
    _ = _ := rfl

theorem uniform_directStaticChoiTargetShortcut_weightedCrowdingLaw
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
          directStaticChoiTargetNearActionMass target energy n δ +
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
    _ ≤ 2 * T * ‖twistedFiniteSpectralFidelityMean
        weight negEnergy twist n T‖ :=
      threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le_norm
        n hn hT (Real.sqrt_nonneg _)
    _ ≤ 2 * T *
        (fidelityReplicaCollisionMass weight negEnergy n +
          fidelityReplicaNearActionMass weight negEnergy n δ +
          min 1 (T * δ)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (norm_twistedFiniteSpectralFidelityMean_le_collision_add_crowding
          (directStaticChoiTargetWeight_nonneg target)
          (sum_directStaticChoiTargetWeight_le_one hd htarget)
          (norm_directStaticChoiTargetTwist target) n hT hδ)
        (mul_nonneg (by norm_num) hT.le)
    _ ≤ 2 * T *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          fidelityReplicaNearActionMass weight negEnergy n δ +
          min 1 (T * δ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hT.le)
      gcongr
      exact directStaticChoiTarget_collision_le_factorial_inv_pow
        hd hmax htarget n
    _ = _ := rfl

theorem gaussian_directAdaptiveStaticChoiTargetShortcut_weightedCrowdingLaw
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
            Real.exp (-((T * δ) ^ 2) / 2)) +
        directAdaptiveChoiNearActionPartition target energy n δ := by
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
    _ ≤ ∑ w : W,
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          directStaticChoiTargetNearActionMass (target w) energy n δ +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
      apply Finset.sum_le_sum
      intro w hw
      exact gaussian_directStaticChoiTargetShortcut_weightedCrowdingLaw
        hd hmax (htarget w) n hn hT hδ hepsilon hepsilonOne
    _ = (Fintype.card W : ℝ) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            Real.exp (-((T * δ) ^ 2) / 2)) +
        directAdaptiveChoiNearActionPartition target energy n δ := by
      unfold directAdaptiveChoiNearActionPartition
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ]
      ring_nf

theorem uniform_directAdaptiveStaticChoiTargetShortcut_weightedCrowdingLaw
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
      2 * T *
        ((Fintype.card W : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
              min 1 (T * δ)⁻¹) +
          directAdaptiveChoiNearActionPartition target energy n δ) := by
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
    _ ≤ ∑ w : W, 2 * T *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          directStaticChoiTargetNearActionMass (target w) energy n δ +
          min 1 (T * δ)⁻¹) := by
      apply Finset.sum_le_sum
      intro w hw
      exact uniform_directStaticChoiTargetShortcut_weightedCrowdingLaw
        hd hmax (htarget w) n hn hT hδ hepsilon hepsilonOne
    _ = 2 * T *
        ((Fintype.card W : ℝ) *
            ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
              min 1 (T * δ)⁻¹) +
          directAdaptiveChoiNearActionPartition target energy n δ) := by
      rw [← Finset.mul_sum]
      congr 1
      unfold directAdaptiveChoiNearActionPartition
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ]
      ring_nf

theorem gaussian_directAdaptiveStaticChoiTargetShortcut_weightedCrowdingProbability_le
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
            Real.exp (-((T * δ) ^ 2) / 2)) +
        directAdaptiveChoiNearActionPartition target energy n δ := by
  rw [← sqrt_one_sub_sq_pow_two_mul hepsilon hepsilonOne n]
  exact gaussian_directAdaptiveStaticChoiTargetShortcut_weightedCrowdingLaw
    hd hmax target htarget n hn hT hδ hepsilon hepsilonOne

theorem uniform_directAdaptiveStaticChoiTargetShortcut_weightedCrowdingProbability_le
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
            min 1 (T * δ)⁻¹) +
        directAdaptiveChoiNearActionPartition target energy n δ := by
  have hmain := uniform_directAdaptiveStaticChoiTargetShortcut_weightedCrowdingLaw
    hd hmax target htarget n hn hT hδ hepsilon hepsilonOne
  rw [sqrt_one_sub_sq_pow_two_mul hepsilon hepsilonOne n] at hmain
  have h2T : 0 < 2 * T := mul_pos (by norm_num) hT
  rw [← mul_div_assoc]
  apply (div_le_iff₀ h2T).2
  simpa only [mul_comm] using hmain

theorem gaussian_directAdaptivePaddedCircuitShortcut_weightedCrowdingProbability_le
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (gaussianReal 0 1).real
          (⋃ w : PaddedCircuitWord gate s,
            gaussianStaticChoiTargetCaptureSet energy (target w) T epsilon) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            Real.exp (-((T * δ) ^ 2) / 2)) +
        directAdaptiveChoiNearActionPartition target energy n δ := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    gaussian_directAdaptiveStaticChoiTargetShortcut_weightedCrowdingProbability_le
      hd hmax target htarget n hn hT hδ hepsilon hepsilonOne

theorem uniform_directAdaptivePaddedCircuitShortcut_weightedCrowdingProbability_le
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (volume.real
          (⋃ w : PaddedCircuitWord gate s,
            uniformStaticChoiTargetCaptureSet energy (target w) T epsilon) /
              (2 * T)) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            min 1 (T * δ)⁻¹) +
        directAdaptiveChoiNearActionPartition target energy n δ := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    uniform_directAdaptiveStaticChoiTargetShortcut_weightedCrowdingProbability_le
      hd hmax target htarget n hn hT hδ hepsilon hepsilonOne

theorem exists_directAdaptivePaddedCircuitHardTime_of_weightedCrowdingBudget
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            min 1 (T * δ)⁻¹) +
          directAdaptiveChoiNearActionPartition target energy n δ <
        (1 - epsilon ^ 2) ^ n) :
    ∃ t ∈ Set.Ioc (-T) T,
      ∀ w : PaddedCircuitWord gate s,
        t ∉ staticChoiTargetCaptureSet energy (target w) epsilon := by
  have hmain :=
    uniform_directAdaptivePaddedCircuitShortcut_weightedCrowdingProbability_le
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
      ring_nf
    · linarith
  rw [hmeasure, mul_one] at hmain
  exact (not_lt_of_ge hmain) hbudget

end RHTower
