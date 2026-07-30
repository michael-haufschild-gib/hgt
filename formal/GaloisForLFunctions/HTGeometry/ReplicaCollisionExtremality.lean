import GaloisForLFunctions.HTGeometry.FidelityReplicaCharacterCoefficientLaw
import GaloisForLFunctions.HTGeometry.SymmetricTimeAverageCharacterLaw

/-!
# All-order replica-collision extremality

For a finite positive-weight spectrum, every equal-energy pair of replica
multiplicity vectors contributes a positive term to the return moment.
The diagonal pairs give an unavoidable permutation floor.  This file proves
that the floor is attained at every replica order simultaneously exactly
when the energy spectrum has maximal projective rational rank.
-/

open scoped BigOperators Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- Total energy of one replica multiplicity vector. -/
def replicaMultiplicityEnergy
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (p : I → ℕ) : ℝ :=
  ∑ i, (p i : ℝ) * energy i

/-- Unavoidable contribution from equal positive and negative replica
multiplicities. -/
def fidelityReplicaPermutationFloor
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    fidelityReplicaMultiplicityWeight weight p p

/-- Strictly additional contribution from unequal equal-energy replica
multiplicity vectors. -/
def fidelityReplicaResonanceExcess
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      if p ≠ q ∧
          replicaMultiplicityEnergy energy p =
            replicaMultiplicityEnergy energy q
      then fidelityReplicaMultiplicityWeight weight p q
      else 0

/-- Permutation floor plus all nontrivial equal-energy replica
collisions. -/
def fidelityReplicaCollisionMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) : ℝ :=
  fidelityReplicaPermutationFloor weight n +
    fidelityReplicaResonanceExcess weight energy n

/-- Direct resonant-pair form of the replica collision mass. -/
def fidelityReplicaResonantMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      if replicaMultiplicityEnergy energy p =
          replicaMultiplicityEnergy energy q
      then fidelityReplicaMultiplicityWeight weight p q
      else 0

/-- The diagonal-plus-excess decomposition enumerates exactly all resonant
replica pairs. -/
theorem fidelityReplicaResonantMass_eq_collisionMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) :
    fidelityReplicaResonantMass weight energy n =
      fidelityReplicaCollisionMass weight energy n := by
  classical
  unfold fidelityReplicaResonantMass fidelityReplicaCollisionMass
    fidelityReplicaPermutationFloor fidelityReplicaResonanceExcess
  have hsplit (p q : I → ℕ) :
      (if replicaMultiplicityEnergy energy p =
            replicaMultiplicityEnergy energy q
        then fidelityReplicaMultiplicityWeight weight p q
        else 0) =
      (if p = q
        then fidelityReplicaMultiplicityWeight weight p q
        else 0) +
      (if p ≠ q ∧
          replicaMultiplicityEnergy energy p =
            replicaMultiplicityEnergy energy q
        then fidelityReplicaMultiplicityWeight weight p q
        else 0) := by
    by_cases hpq : p = q <;>
      by_cases henergy :
          replicaMultiplicityEnergy energy p =
            replicaMultiplicityEnergy energy q <;>
      simp [hpq, henergy]
  have hinner (p : I → ℕ)
      (hp : p ∈ Finset.univ.piAntidiag n) :
      (∑ q ∈ Finset.univ.piAntidiag n,
        if replicaMultiplicityEnergy energy p =
            replicaMultiplicityEnergy energy q
        then fidelityReplicaMultiplicityWeight weight p q
        else 0) =
      fidelityReplicaMultiplicityWeight weight p p +
        ∑ q ∈ Finset.univ.piAntidiag n,
          if p ≠ q ∧
              replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
          then fidelityReplicaMultiplicityWeight weight p q
          else 0 := by
    simp_rw [hsplit, Finset.sum_add_distrib]
    congr 1
    simp [hp]
  calc
    (∑ p ∈ Finset.univ.piAntidiag n,
      ∑ q ∈ Finset.univ.piAntidiag n,
        if replicaMultiplicityEnergy energy p =
            replicaMultiplicityEnergy energy q
        then fidelityReplicaMultiplicityWeight weight p q
        else 0) =
        ∑ p ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p p +
            ∑ q ∈ Finset.univ.piAntidiag n,
              if p ≠ q ∧
                  replicaMultiplicityEnergy energy p =
                    replicaMultiplicityEnergy energy q
              then fidelityReplicaMultiplicityWeight weight p q
              else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hinner p hp
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]

/-! ## Operational bridge to finite-spectrum quantum return -/

/-- Survival amplitude of a finite weighted real spectrum. -/
def finiteSpectralSurvivalAmplitude
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (t : ℝ) : ℂ :=
  ∑ i, (weight i : ℂ) *
    Complex.exp (((energy i * t : ℝ) : ℂ) * Complex.I)

/-- Survival fidelity of a finite weighted real spectrum. -/
def finiteSpectralSurvivalFidelity
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (t : ℝ) : ℂ :=
  (Complex.normSq
    (finiteSpectralSurvivalAmplitude weight energy t) : ℂ)

/-- Survival fidelity is the product of the forward and backward spectral
phase sums. -/
theorem finiteSpectralSurvivalFidelity_eq_phaseProduct
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (t : ℝ) :
    finiteSpectralSurvivalFidelity weight energy t =
      (∑ i, (weight i : ℂ) *
          Complex.exp (((energy i * t : ℝ) : ℂ) * Complex.I)) *
      (∑ i, (weight i : ℂ) *
          Complex.exp (((-energy i * t : ℝ) : ℂ) * Complex.I)) := by
  classical
  rw [finiteSpectralSurvivalFidelity,
    Complex.normSq_eq_conj_mul_self]
  unfold finiteSpectralSurvivalAmplitude
  rw [map_sum]
  simp_rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have hconj :
      (∑ i, (weight i : ℂ) *
          Complex.exp
            ((starRingEnd ℂ)
              (((energy i * t : ℝ) : ℂ) * Complex.I))) =
        ∑ i, (weight i : ℂ) *
          Complex.exp (((-energy i * t : ℝ) : ℂ) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    push_cast
    simp
  rw [hconj, mul_comm]

/-- Exact all-replica phase expansion of finite-spectrum survival fidelity. -/
theorem finiteSpectralSurvivalFidelity_pow_expansion
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) (t : ℝ) :
    finiteSpectralSurvivalFidelity weight energy t ^ n =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            Complex.exp
              (((t * (replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q) : ℝ) : ℂ) *
                Complex.I) := by
  classical
  rw [finiteSpectralSurvivalFidelity_eq_phaseProduct, mul_pow,
    complexFidelityReplicaMultiplicityExpansion]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hpositive :
      (∏ i, Complex.exp
        (((energy i * t : ℝ) : ℂ) * Complex.I) ^ p i) =
        Complex.exp
          (((t * replicaMultiplicityEnergy energy p : ℝ) : ℂ) *
            Complex.I) := by
    simp_rw [← Complex.exp_nat_mul]
    rw [← Complex.exp_sum]
    congr 1
    unfold replicaMultiplicityEnergy
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hnegative :
      (∏ i, Complex.exp
        (((-energy i * t : ℝ) : ℂ) * Complex.I) ^ q i) =
        Complex.exp
          (((-t * replicaMultiplicityEnergy energy q : ℝ) : ℂ) *
            Complex.I) := by
    simp_rw [← Complex.exp_nat_mul]
    rw [← Complex.exp_sum]
    congr 1
    unfold replicaMultiplicityEnergy
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hpositive, hnegative, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Symmetric-window normalized `n`th survival-fidelity moment of a finite
spectrum. -/
def finiteSpectralSurvivalFidelityMean
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (n : ℕ) (T : ℝ) : ℂ :=
  (2 * T : ℂ)⁻¹ *
    ∫ t : ℝ in -T..T,
      finiteSpectralSurvivalFidelity weight energy t ^ n

/-- Every finite-window return moment is the corresponding weighted sum of
exact sinc phase reporters. -/
theorem finiteSpectralSurvivalFidelityMean_eq_replicaPhaseAverage
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) (T : ℝ) :
    finiteSpectralSurvivalFidelityMean weight energy n T =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            symmetricPhaseAverage T
              (replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q) := by
  classical
  unfold finiteSpectralSurvivalFidelityMean
  simp_rw [finiteSpectralSurvivalFidelity_pow_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [intervalIntegral.integral_const_mul]
      unfold symmetricPhaseAverage
      ring
    · intro q hq
      exact
        (by fun_prop :
          Continuous (fun x : ℝ =>
            (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
              Complex.exp
                (((x * (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q) : ℝ) : ℂ) *
                  Complex.I))).intervalIntegrable
          (μ := MeasureTheory.volume) (-T) T
  · intro p hp
    exact
      (by fun_prop :
        Continuous (fun t : ℝ =>
          ∑ q ∈ Finset.univ.piAntidiag n,
            (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
              Complex.exp
                (((t * (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q) : ℝ) : ℂ) *
                  Complex.I))).intervalIntegrable
        (μ := MeasureTheory.volume) (-T) T

/-- A symmetric time window retains exactly zero detuning and dephases every
nonzero detuning. -/
theorem symmetricPhaseAverage_tendsto_resonanceIndicator
    (detuning : ℝ) :
    Tendsto (fun T : ℝ => symmetricPhaseAverage T detuning) atTop
      (𝓝 (if detuning = 0 then (1 : ℂ) else 0)) := by
  by_cases hd : detuning = 0
  · subst detuning
    simp only [if_pos]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
    rw [symmetricPhaseAverage_eq_sinc T 0 hT]
    simp
  · simp only [if_neg hd]
    have hsinc :
        Tendsto (fun T : ℝ => Real.sinc (T * detuning)) atTop
          (𝓝 0) := by
      rcases lt_or_gt_of_ne hd with hneg | hpos
      · have h :=
          tendsto_real_sinc_atTop_zero.comp
            (tendsto_id.atTop_mul_const (neg_pos.mpr hneg))
        apply h.congr'
        filter_upwards [] with T
        change Real.sinc (T * -detuning) =
          Real.sinc (T * detuning)
        rw [show T * -detuning = -(T * detuning) by ring,
          Real.sinc_neg]
      · exact
          tendsto_real_sinc_atTop_zero.comp
            (tendsto_id.atTop_mul_const hpos)
    have hcomplex :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hsinc
    apply hcomplex.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
    rw [symmetricPhaseAverage_eq_sinc T detuning hT]
    rfl

/-- **Operational collision identity.** The long-time `n`th moment of the
actual finite-spectrum survival fidelity is exactly its replica collision
mass. -/
theorem finiteSpectralSurvivalFidelityMean_tendsto_collisionMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) :
    Tendsto
      (finiteSpectralSurvivalFidelityMean weight energy n)
      atTop
      (𝓝 (fidelityReplicaCollisionMass weight energy n : ℂ)) := by
  have hsum :
      Tendsto
        (fun T : ℝ =>
          ∑ p ∈ Finset.univ.piAntidiag n,
            ∑ q ∈ Finset.univ.piAntidiag n,
              (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
                symmetricPhaseAverage T
                  (replicaMultiplicityEnergy energy p -
                    replicaMultiplicityEnergy energy q))
        atTop
        (𝓝
          (∑ p ∈ Finset.univ.piAntidiag n,
            ∑ q ∈ Finset.univ.piAntidiag n,
              if replicaMultiplicityEnergy energy p =
                  replicaMultiplicityEnergy energy q
              then
                (fidelityReplicaMultiplicityWeight weight p q : ℂ)
              else 0)) := by
    apply tendsto_finsetSum
    intro p hp
    apply tendsto_finsetSum
    intro q hq
    have h :=
      (symmetricPhaseAverage_tendsto_resonanceIndicator
        (replicaMultiplicityEnergy energy p -
          replicaMultiplicityEnergy energy q)).const_mul
        (fidelityReplicaMultiplicityWeight weight p q : ℂ)
    simpa [sub_eq_zero] using h
  rw [← fidelityReplicaResonantMass_eq_collisionMass]
  have hcast :
      (fidelityReplicaResonantMass weight energy n : ℂ) =
        ∑ p ∈ Finset.univ.piAntidiag n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            if replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
            then
              (fidelityReplicaMultiplicityWeight weight p q : ℂ)
            else 0 := by
    unfold fidelityReplicaResonantMass
    push_cast
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    by_cases henergy :
        replicaMultiplicityEnergy energy p =
          replicaMultiplicityEnergy energy q <;>
      simp [henergy]
  rw [hcast]
  apply hsum.congr'
  filter_upwards [] with T
  exact
    (finiteSpectralSurvivalFidelityMean_eq_replicaPhaseAverage
      weight energy n T).symm

/-- At order `n`, equal total replica energies force equal multiplicity
vectors. -/
def ReplicaRigidAt
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) : Prop :=
  ∀ p ∈ Finset.univ.piAntidiag n,
    ∀ q ∈ Finset.univ.piAntidiag n,
      replicaMultiplicityEnergy energy p =
          replicaMultiplicityEnergy energy q →
        p = q

/-- No nonzero balanced integer character annihilates the energy family. -/
def MaximallyProjectiveEnergy
    {I : Type*} [Fintype I]
    (energy : I → ℝ) : Prop :=
  ∀ k : I → ℤ,
    SpectralCharacterBalanced k →
    (∑ i, (k i : ℝ) * energy i) = 0 →
    k = 0

/-- Resonance excess is nonnegative for full-support positive weights. -/
theorem fidelityReplicaResonanceExcess_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (energy : I → ℝ) (n : ℕ) :
    0 ≤ fidelityReplicaResonanceExcess weight energy n := by
  classical
  unfold fidelityReplicaResonanceExcess
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  split_ifs
  · exact le_of_lt
      (fidelityReplicaMultiplicityWeight_pos hweight p q)
  · exact le_rfl

/-- Every finite positive-weight spectrum lies above its permutation
collision floor. -/
theorem fidelityReplicaCollisionMass_floor_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (energy : I → ℝ) (n : ℕ) :
    fidelityReplicaPermutationFloor weight n ≤
      fidelityReplicaCollisionMass weight energy n := by
  unfold fidelityReplicaCollisionMass
  exact le_add_of_nonneg_right
    (fidelityReplicaResonanceExcess_nonneg hweight energy n)

/-- Resonance excess vanishes exactly when the spectrum is replica-rigid at
that order. -/
theorem fidelityReplicaResonanceExcess_eq_zero_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (energy : I → ℝ) (n : ℕ) :
    fidelityReplicaResonanceExcess weight energy n = 0 ↔
      ReplicaRigidAt energy n := by
  classical
  constructor
  · intro hexcess
    unfold ReplicaRigidAt
    intro p hp q hq henergy
    by_contra hpq
    have houter :
        (∑ q ∈ Finset.univ.piAntidiag n,
          if p ≠ q ∧
              replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
          then fidelityReplicaMultiplicityWeight weight p q
          else 0) = 0 := by
      apply
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun p' hp' => by
            apply Finset.sum_nonneg
            intro q' hq'
            split_ifs
            · exact le_of_lt
                (fidelityReplicaMultiplicityWeight_pos
                  hweight p' q')
            · exact le_rfl)).mp hexcess p hp
    have hterm :
        (if p ≠ q ∧
              replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
          then fidelityReplicaMultiplicityWeight weight p q
          else 0) = 0 := by
      apply
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun q' hq' => by
            split_ifs
            · exact le_of_lt
                (fidelityReplicaMultiplicityWeight_pos
                  hweight p q')
            · exact le_rfl)).mp houter q hq
    rw [if_pos ⟨hpq, henergy⟩] at hterm
    exact
      (ne_of_gt
        (fidelityReplicaMultiplicityWeight_pos hweight p q))
        hterm
  · intro hrigid
    unfold ReplicaRigidAt at hrigid
    unfold fidelityReplicaResonanceExcess
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    by_cases hresonant :
        replicaMultiplicityEnergy energy p =
          replicaMultiplicityEnergy energy q
    · have hpq := hrigid p hp q hq hresonant
      simp [hpq]
    · simp [hresonant]

/-- Fixed-order collision mass attains its floor exactly under fixed-order
replica rigidity. -/
theorem fidelityReplicaCollisionMass_eq_floor_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (energy : I → ℝ) (n : ℕ) :
    fidelityReplicaCollisionMass weight energy n =
        fidelityReplicaPermutationFloor weight n ↔
      ReplicaRigidAt energy n := by
  rw [fidelityReplicaCollisionMass]
  constructor
  · intro h
    apply
      (fidelityReplicaResonanceExcess_eq_zero_iff
        hweight energy n).1
    linarith
  · intro h
    rw [(fidelityReplicaResonanceExcess_eq_zero_iff
      hweight energy n).2 h, add_zero]

/-- Rigidity at every finite replica order is exactly maximal projective
rational rank. -/
theorem forall_replicaRigidAt_iff_maximallyProjectiveEnergy
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) :
    (∀ n : ℕ, ReplicaRigidAt energy n) ↔
      MaximallyProjectiveEnergy energy := by
  classical
  constructor
  · intro hall
    unfold MaximallyProjectiveEnergy
    intro k hbalanced henergy
    obtain ⟨p, q, hp, hq, hk⟩ :=
      spectralCharacterReplicaRealizes_positiveMass_of_balanced
        hbalanced
    have hpmem :
        p ∈ Finset.univ.piAntidiag
          (spectralCharacterPositiveMass k) := by
      rw [Finset.mem_piAntidiag]
      exact ⟨hp, fun i hi => Finset.mem_univ i⟩
    have hqmem :
        q ∈ Finset.univ.piAntidiag
          (spectralCharacterPositiveMass k) := by
      rw [Finset.mem_piAntidiag]
      exact ⟨hq, fun i hi => Finset.mem_univ i⟩
    have hpqEnergy :
        replicaMultiplicityEnergy energy p =
          replicaMultiplicityEnergy energy q := by
      apply sub_eq_zero.mp
      calc
        replicaMultiplicityEnergy energy p -
            replicaMultiplicityEnergy energy q =
          ∑ i, ((p i : ℝ) - (q i : ℝ)) *
            energy i := by
              unfold replicaMultiplicityEnergy
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = ∑ i, (k i : ℝ) * energy i := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hk i]
              norm_cast
        _ = 0 := henergy
    have hpq :=
      hall (spectralCharacterPositiveMass k)
        p hpmem q hqmem hpqEnergy
    funext i
    rw [hk i, hpq]
    simp
  · intro hmax n
    unfold ReplicaRigidAt
    intro p hp q hq hpqEnergy
    let k : I → ℤ := replicaMultiplicityCharacter p q
    have hbalanced : SpectralCharacterBalanced k := by
      unfold SpectralCharacterBalanced k
      simp only [replicaMultiplicityCharacter]
      rw [Finset.sum_sub_distrib]
      have hpSum := (Finset.mem_piAntidiag.mp hp).1
      have hqSum := (Finset.mem_piAntidiag.mp hq).1
      have hpSumZ : ∑ i, (p i : ℤ) = (n : ℤ) := by
        exact_mod_cast hpSum
      have hqSumZ : ∑ i, (q i : ℤ) = (n : ℤ) := by
        exact_mod_cast hqSum
      rw [hpSumZ, hqSumZ, sub_self]
    have henergy :
        (∑ i, (k i : ℝ) * energy i) = 0 := by
      calc
        (∑ i, (k i : ℝ) * energy i) =
            ∑ i, ((p i : ℝ) - (q i : ℝ)) *
              energy i := by
                apply Finset.sum_congr rfl
                intro i hi
                simp only [k, replicaMultiplicityCharacter]
                norm_cast
        _ = replicaMultiplicityEnergy energy p -
            replicaMultiplicityEnergy energy q := by
              unfold replicaMultiplicityEnergy
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = 0 := sub_eq_zero.mpr hpqEnergy
    have hkzero := hmax k hbalanced henergy
    funext i
    have hi := congrFun hkzero i
    change (p i : ℤ) - (q i : ℤ) = 0 at hi
    omega

/-- **All-order collision extremality.** Full projective spectral rank is
equivalent to attaining the permutation collision floor at every replica
order simultaneously. -/
theorem all_fidelityReplicaCollisionMass_eq_floor_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (energy : I → ℝ) :
    (∀ n : ℕ,
      fidelityReplicaCollisionMass weight energy n =
        fidelityReplicaPermutationFloor weight n) ↔
      MaximallyProjectiveEnergy energy := by
  rw [← forall_replicaRigidAt_iff_maximallyProjectiveEnergy energy]
  constructor
  · intro hall n
    exact
      (fidelityReplicaCollisionMass_eq_floor_iff
        hweight energy n).1 (hall n)
  · intro hall n
    exact
      (fidelityReplicaCollisionMass_eq_floor_iff
        hweight energy n).2 (hall n)

/-- **Observable all-order extremality law.** For a full-support finite
spectrum, maximal projective rational rank is equivalent to every long-time
survival-fidelity moment converging to its unavoidable permutation floor. -/
theorem
    all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (energy : I → ℝ) :
    (∀ n : ℕ,
      Tendsto
        (finiteSpectralSurvivalFidelityMean weight energy n)
        atTop
        (𝓝 (fidelityReplicaPermutationFloor weight n : ℂ))) ↔
      MaximallyProjectiveEnergy energy := by
  rw [← all_fidelityReplicaCollisionMass_eq_floor_iff
    hweight energy]
  constructor
  · intro hall n
    have hcollision :=
      finiteSpectralSurvivalFidelityMean_tendsto_collisionMass
        weight energy n
    have hfloor := hall n
    have hcast :
        (fidelityReplicaCollisionMass weight energy n : ℂ) =
          (fidelityReplicaPermutationFloor weight n : ℂ) :=
      tendsto_nhds_unique hcollision hfloor
    exact Complex.ofReal_injective hcast
  · intro hall n
    simpa [hall n] using
      (finiteSpectralSurvivalFidelityMean_tendsto_collisionMass
        weight energy n)

/-- Maximal projective rank makes every nonzero ordered energy gap distinct.
Thus second-order local-response poles carry a canonical ordered transition
label. -/
theorem maximallyProjectiveEnergy_orientedGap_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy) :
    Function.Injective
      (fun p : {p : I × I // p.1 ≠ p.2} =>
        energy p.1.1 - energy p.1.2) := by
  intro p q hgap
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases q with ⟨⟨c, d⟩, hcd⟩
  have hrigid : ReplicaRigidAt energy 2 :=
    ((forall_replicaRigidAt_iff_maximallyProjectiveEnergy energy).2 hmax) 2
  let positive : I → ℕ :=
    Pi.single a 1 + Pi.single d 1
  let negative : I → ℕ :=
    Pi.single c 1 + Pi.single b 1
  have hpositive :
      positive ∈ Finset.univ.piAntidiag 2 := by
    rw [Finset.mem_piAntidiag]
    constructor
    · unfold positive
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib,
        Fintype.sum_pi_single', Fintype.sum_pi_single']
    · intro i hi
      exact Finset.mem_univ i
  have hnegative :
      negative ∈ Finset.univ.piAntidiag 2 := by
    rw [Finset.mem_piAntidiag]
    constructor
    · unfold negative
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib,
        Fintype.sum_pi_single', Fintype.sum_pi_single']
    · intro i hi
      exact Finset.mem_univ i
  have henergy :
      replicaMultiplicityEnergy energy positive =
        replicaMultiplicityEnergy energy negative := by
    unfold replicaMultiplicityEnergy positive negative
    simp only [Pi.add_apply, Nat.cast_add]
    simp [Pi.single_apply, Finset.sum_add_distrib, add_mul,
      Finset.sum_ite_eq']
    linarith
  have hpq := hrigid positive hpositive negative hnegative henergy
  have hac : a = c := by
    by_contra hac
    have ha := congrFun hpq a
    simp only [positive, negative, Pi.add_apply] at ha
    by_cases had : a = d
    · subst d
      simp [hac, hab] at ha
    · simp [had, hac, hab] at ha
  have hbd : b = d := by
    by_contra hbd
    have hb := congrFun hpq b
    subst c
    simp only [positive, negative, Pi.add_apply] at hb
    simp [hab, hbd] at hb
  subst c
  subst d
  rfl

end

end GaloisForLFunctions.HTGeometry
