import GaloisForLFunctions.RHTower.MixedStateQutritRecurrenceSeparation

/-!
# Moment-matched mixed-state clocks with different recurrence laws

Two explicit full-rank four-level clocks share one Hamiltonian, one complete
density spectrum, the first two energy moments, Hilbert--Schmidt speed, and
SLD quantum Fisher information. At the common ticks `2πn`, one clock returns
exactly at every tick while the other obeys matching inverse-resolution
recurrence bounds.

Matching the first two moments removes energy expectation as a discriminator.
The remaining separation is the arithmetic distinction between rational
energy support and the irrational gap `√2`.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Positive normalization used by the moment-matched four-level pair. -/
def ququartMomentDenominator : ℝ := 3 * Real.sqrt 2 - 2

/-- Population placed on the irrational energy `√2`. -/
def ququartIrrationalMass : ℝ := 2 / ququartMomentDenominator

/-- Population placed on energy `1` in the periodic clock. -/
def ququartPeriodicUnitMass : ℝ :=
  4 * (Real.sqrt 2 - 1) / ququartMomentDenominator

/-- Populations of the exactly periodic clock, supported on energies `1,2`. -/
def ququartPeriodicWeight : Fin 4 → ℝ :=
  ![0, ququartPeriodicUnitMass, 0, 1 - ququartPeriodicUnitMass]

/-- Populations of the irrational clock, supported on energies `0,√2`. -/
def ququartAperiodicWeight : Fin 4 → ℝ :=
  ![1 - ququartIrrationalMass, 0, ququartIrrationalMass, 0]

/-- Shared energy list `(0,1,√2,2)`. -/
def ququartEnergy : Fin 4 → ℝ := ![0, 1, Real.sqrt 2, 2]

private theorem sqrt_two_gt_one : 1 < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_nonneg 2]

private theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_nonneg 2]

private theorem four_lt_three_mul_sqrt_two :
    4 < 3 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_nonneg 2]

theorem ququartMomentDenominator_pos :
    0 < ququartMomentDenominator := by
  rw [ququartMomentDenominator]
  linarith [sqrt_two_gt_one]

theorem ququartIrrationalMass_pos :
    0 < ququartIrrationalMass := by
  rw [ququartIrrationalMass]
  exact div_pos (by norm_num) ququartMomentDenominator_pos

theorem ququartIrrationalMass_lt_one :
    ququartIrrationalMass < 1 := by
  rw [ququartIrrationalMass]
  apply (div_lt_one ququartMomentDenominator_pos).2
  rw [ququartMomentDenominator]
  linarith [four_lt_three_mul_sqrt_two]

theorem ququartPeriodicUnitMass_pos :
    0 < ququartPeriodicUnitMass := by
  rw [ququartPeriodicUnitMass]
  exact div_pos
    (mul_pos (by norm_num) (by linarith [sqrt_two_gt_one]))
    ququartMomentDenominator_pos

theorem ququartPeriodicUnitMass_lt_one :
    ququartPeriodicUnitMass < 1 := by
  rw [ququartPeriodicUnitMass]
  apply (div_lt_one ququartMomentDenominator_pos).2
  rw [ququartMomentDenominator]
  linarith [sqrt_two_lt_two]

theorem ququartPeriodicWeight_sum :
    ∑ i, ququartPeriodicWeight i = 1 := by
  simp [ququartPeriodicWeight, Fin.sum_univ_four]

theorem ququartAperiodicWeight_sum :
    ∑ i, ququartAperiodicWeight i = 1 := by
  simp [ququartAperiodicWeight, Fin.sum_univ_four]

theorem ququartPeriodicWeight_nonneg :
    ∀ i, 0 ≤ ququartPeriodicWeight i := by
  intro i
  fin_cases i
  · simp [ququartPeriodicWeight]
  · simp [ququartPeriodicWeight]
    exact ququartPeriodicUnitMass_pos.le
  · simp [ququartPeriodicWeight]
  · simp [ququartPeriodicWeight]
    linarith [ququartPeriodicUnitMass_lt_one]

theorem ququartAperiodicWeight_nonneg :
    ∀ i, 0 ≤ ququartAperiodicWeight i := by
  intro i
  fin_cases i
  · simp [ququartAperiodicWeight]
    linarith [ququartIrrationalMass_lt_one]
  · simp [ququartAperiodicWeight]
  · simp [ququartAperiodicWeight]
    exact ququartIrrationalMass_pos.le
  · simp [ququartAperiodicWeight]

private theorem two_sub_ququartPeriodicUnitMass :
    2 - ququartPeriodicUnitMass =
      ququartIrrationalMass * Real.sqrt 2 := by
  rw [ququartPeriodicUnitMass, ququartIrrationalMass,
    ]
  field_simp [ne_of_gt ququartMomentDenominator_pos]
  rw [ququartMomentDenominator]
  ring

private theorem four_sub_three_mul_ququartPeriodicUnitMass :
    4 - 3 * ququartPeriodicUnitMass =
      2 * ququartIrrationalMass := by
  rw [ququartPeriodicUnitMass, ququartIrrationalMass,
    ]
  field_simp [ne_of_gt ququartMomentDenominator_pos]
  rw [ququartMomentDenominator]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The periodic and irrational packets have the same mean energy. -/
theorem ququart_first_energy_moment_eq :
    (∑ i, ququartPeriodicWeight i * ququartEnergy i) =
      ∑ i, ququartAperiodicWeight i * ququartEnergy i := by
  simp [ququartPeriodicWeight, ququartAperiodicWeight,
    ququartEnergy,
    Fin.sum_univ_four]
  nlinarith [two_sub_ququartPeriodicUnitMass]

/-- The periodic and irrational packets have the same second energy moment. -/
theorem ququart_second_energy_moment_eq :
    (∑ i, ququartPeriodicWeight i * ququartEnergy i ^ (2 : ℕ)) =
      ∑ i, ququartAperiodicWeight i * ququartEnergy i ^ (2 : ℕ) := by
  simp [ququartPeriodicWeight, ququartAperiodicWeight,
    ququartEnergy,
    Fin.sum_univ_four]
  nlinarith [four_sub_three_mul_ququartPeriodicUnitMass]

/-- Matching first and second moments give exactly matching variance. -/
theorem ququart_weightedVariance_eq :
    finiteWeightedVariance ququartPeriodicWeight ququartEnergy =
      finiteWeightedVariance ququartAperiodicWeight ququartEnergy := by
  unfold finiteWeightedVariance
  rw [ququart_first_energy_moment_eq, ququart_second_energy_moment_eq]

/-- Phase packet of the periodic clock at tick `2πn`. -/
def ququartPeriodicTickPhase (_n : ℕ) : Fin 4 → ℂ := ![1, 1, 1, 1]

/-- Phase packet of the irrational clock at tick `2πn`. -/
def ququartAperiodicTickPhase (n : ℕ) : Fin 4 → ℂ :=
  ![1, 1, HTGeometry.ee ((n : ℝ) * Real.sqrt 2), 1]

theorem ququartPeriodic_fidelityDeficit_eq_zero (n : ℕ) :
    weightedFidelityDeficit ququartPeriodicWeight
      (ququartPeriodicTickPhase n) = 0 := by
  simp [weightedFidelityDeficit, projectiveWeightedPhaseAmplitude,
    ququartPeriodicWeight, ququartPeriodicTickPhase, Fin.sum_univ_four]

/-- Exact fidelity deficit of the irrational four-level clock. -/
theorem ququartAperiodic_fidelityDeficit_eq (n : ℕ) :
    weightedFidelityDeficit ququartAperiodicWeight
        (ququartAperiodicTickPhase n) =
      ququartIrrationalMass * (1 - ququartIrrationalMass) *
        ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ ^ (2 : ℕ) := by
  let phase := ququartAperiodicTickPhase n
  have hphase : ∀ i, ‖phase i‖ = 1 := by
    intro i
    fin_cases i
    · simp [phase, ququartAperiodicTickPhase]
    · simp [phase, ququartAperiodicTickPhase]
    · simp [phase, ququartAperiodicTickPhase, HTGeometry.norm_ee]
    · simp [phase, ququartAperiodicTickPhase]
  have h := projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit
    ququartAperiodicWeight phase ququartAperiodicWeight_sum hphase
  rw [weightedFidelityDeficit]
  rw [show projectiveWeightedPairwiseEnergy ququartAperiodicWeight phase =
      2 * ququartIrrationalMass * (1 - ququartIrrationalMass) *
        ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ ^ (2 : ℕ) by
    simp [projectiveWeightedPairwiseEnergy, ququartAperiodicWeight,
      phase, ququartAperiodicTickPhase, Fin.sum_univ_four,
      norm_sub_rev]
    ring] at h
  nlinarith

/-- Operational recurrence amplitude for the `b=1/8`, `c=1/2` clocks. -/
def ququartTickRecurrenceAmplitude (w : Fin 4 → ℝ)
    (phase : Fin 4 → ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt (weightedFidelityDeficit w phase)

theorem ququartPeriodic_tickRecurrenceAmplitude_eq_zero (n : ℕ) :
    ququartTickRecurrenceAmplitude ququartPeriodicWeight
      (ququartPeriodicTickPhase n) = 0 := by
  rw [ququartTickRecurrenceAmplitude,
    ququartPeriodic_fidelityDeficit_eq_zero, Real.sqrt_zero, mul_zero]

/-- Exact stroboscopic recurrence amplitude of the irrational clock. -/
theorem ququartAperiodic_tickRecurrenceAmplitude_eq (n : ℕ) :
    ququartTickRecurrenceAmplitude ququartAperiodicWeight
        (ququartAperiodicTickPhase n) =
      (1 / 2 : ℝ) *
        Real.sqrt
          (ququartIrrationalMass * (1 - ququartIrrationalMass)) *
          ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := by
  rw [ququartTickRecurrenceAmplitude,
    ququartAperiodic_fidelityDeficit_eq,
    Real.sqrt_mul (mul_nonneg ququartIrrationalMass_pos.le
      (by linarith [ququartIrrationalMass_lt_one]))]
  rw [Real.sqrt_sq (norm_nonneg _)]
  ring

/-- Every positive tick of the irrational clock remains a fixed multiple of
`1/n` away from recurrence. -/
theorem ququartAperiodic_tickRecurrenceAmplitude_lower
    (n : ℕ) (hn : 0 < n) :
    Real.sqrt
          (ququartIrrationalMass * (1 - ququartIrrationalMass)) /
        (2 * (n : ℝ)) ≤
      ququartTickRecurrenceAmplitude ququartAperiodicWeight
        (ququartAperiodicTickPhase n) := by
  rw [ququartAperiodic_tickRecurrenceAmplitude_eq]
  have hdist := distToInt_nat_mul_sqrt_two_lower n hn
  have hchord :=
    HTGeometry.four_mul_distToInt_le_norm_ee_sub_one
      ((n : ℝ) * Real.sqrt 2)
  have hchordLower :
      1 / (n : ℝ) ≤
        ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := by
    calc
      1 / (n : ℝ) = 4 * (1 / (4 * (n : ℝ))) := by
        field_simp
      _ ≤ 4 * HTGeometry.distToInt ((n : ℝ) * Real.sqrt 2) := by
        gcongr
      _ ≤ ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := hchord
  have hsqrt :
      0 ≤ Real.sqrt
        (ququartIrrationalMass * (1 - ququartIrrationalMass)) :=
    Real.sqrt_nonneg _
  calc
    Real.sqrt
          (ququartIrrationalMass * (1 - ququartIrrationalMass)) /
        (2 * (n : ℝ)) =
        (1 / 2 : ℝ) *
          Real.sqrt
            (ququartIrrationalMass * (1 - ququartIrrationalMass)) *
              (1 / (n : ℝ)) := by ring
    _ ≤ (1 / 2 : ℝ) *
        Real.sqrt
          (ququartIrrationalMass * (1 - ququartIrrationalMass)) *
            ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := by
      gcongr

/-- Every positive horizon `Q` contains a return tick with recurrence
amplitude at most an explicit multiple of `1/Q`. -/
theorem exists_ququartAperiodic_tickRecurrenceAmplitude_upper
    (Q : ℕ) (hQ : 0 < Q) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
      ququartTickRecurrenceAmplitude ququartAperiodicWeight
          (ququartAperiodicTickPhase n) ≤
        Real.pi *
          Real.sqrt
            (ququartIrrationalMass * (1 - ququartIrrationalMass)) /
              (Q : ℝ) := by
  obtain ⟨n, hn, hnQ, r, hr⟩ :=
    exists_fin_simultaneous_integer_approximation_anisotropic
      (fun _ : Fin 1 => Real.sqrt 2) (fun _ : Fin 1 => Q)
      (fun _ => hQ)
  have hnQ' : n ≤ Q := by
    simpa using hnQ
  have happrox :
      |(n : ℝ) * Real.sqrt 2 - (r 0 : ℝ)| ≤ 1 / (Q : ℝ) := by
    simpa using hr 0
  have hchord :
      ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ ≤
        2 * Real.pi * (1 / (Q : ℝ)) :=
    norm_ee_sub_one_le_two_pi_mul_of_integer_approximation
      (r 0) happrox
  refine ⟨n, hn, hnQ', ?_⟩
  rw [ququartAperiodic_tickRecurrenceAmplitude_eq]
  have hsqrt :
      0 ≤ Real.sqrt
        (ququartIrrationalMass * (1 - ququartIrrationalMass)) :=
    Real.sqrt_nonneg _
  calc
    (1 / 2 : ℝ) *
        Real.sqrt
          (ququartIrrationalMass * (1 - ququartIrrationalMass)) *
            ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ ≤
        (1 / 2 : ℝ) *
          Real.sqrt
            (ququartIrrationalMass * (1 - ququartIrrationalMass)) *
              (2 * Real.pi * (1 / (Q : ℝ))) := by
      gcongr
    _ = Real.pi *
        Real.sqrt
          (ququartIrrationalMass * (1 - ququartIrrationalMass)) /
            (Q : ℝ) := by ring

/-- Squared Hilbert--Schmidt speed of the `c=1/2` four-level family. -/
def ququartMixedSpikeHSSpeedSq (w : Fin 4 → ℝ) : ℝ :=
  2 * (1 / 2 : ℝ) ^ (2 : ℕ) * finiteWeightedVariance w ququartEnergy

/-- SLD quantum Fisher information of the `b=1/8`, `c=1/2` family. -/
def ququartMixedSpikeQuantumFisher (w : Fin 4 → ℝ) : ℝ :=
  4 * (1 / 2 : ℝ) ^ (2 : ℕ) / (2 * (1 / 8 : ℝ) + 1 / 2) *
    finiteWeightedVariance w ququartEnergy

theorem ququart_mixedSpikeHSSpeedSq_eq :
    ququartMixedSpikeHSSpeedSq ququartPeriodicWeight =
      ququartMixedSpikeHSSpeedSq ququartAperiodicWeight := by
  rw [ququartMixedSpikeHSSpeedSq, ququartMixedSpikeHSSpeedSq,
    ququart_weightedVariance_eq]

theorem ququartMixedSpikeHSSpeedSq_eq_realized
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian ququartEnergy) (finiteWeightKet w)) =
      ququartMixedSpikeHSSpeedSq w := by
  rw [mixedSpikeUnitaryTangent_hsNormSq (1 / 2)
    (finiteDiagonalHamiltonian ququartEnergy)
    (finiteDiagonalHamiltonian_selfAdjoint ququartEnergy)
    (finiteWeightKet w) (finiteWeightKet_norm_eq_one w hw hsum)]
  rw [finiteWeightKet_diagonal_variance w ququartEnergy hw]
  rfl

theorem ququart_realized_mixedSpikeHSSpeedSq_eq :
    ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian ququartEnergy)
          (finiteWeightKet ququartPeriodicWeight)) =
      ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian ququartEnergy)
          (finiteWeightKet ququartAperiodicWeight)) := by
  rw [ququartMixedSpikeHSSpeedSq_eq_realized ququartPeriodicWeight
      ququartPeriodicWeight_nonneg ququartPeriodicWeight_sum,
    ququartMixedSpikeHSSpeedSq_eq_realized ququartAperiodicWeight
      ququartAperiodicWeight_nonneg ququartAperiodicWeight_sum,
    ququart_mixedSpikeHSSpeedSq_eq]

theorem ququart_mixedSpikeQuantumFisher_eq :
    ququartMixedSpikeQuantumFisher ququartPeriodicWeight =
      ququartMixedSpikeQuantumFisher ququartAperiodicWeight := by
  rw [ququartMixedSpikeQuantumFisher, ququartMixedSpikeQuantumFisher,
    ququart_weightedVariance_eq]

theorem ququartMixedSpikeQuantumFisher_eq_SLD
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    mixedSpikeSLDQuantumFisher (1 / 8) (1 / 2)
        (finiteDiagonalHamiltonian ququartEnergy) (finiteWeightKet w) =
      ququartMixedSpikeQuantumFisher w := by
  rw [mixedSpikeSLDQuantumFisher_eq (1 / 8) (1 / 2) (by norm_num)
    (finiteDiagonalHamiltonian ququartEnergy)
    (finiteDiagonalHamiltonian_selfAdjoint ququartEnergy)
    (finiteWeightKet w) (finiteWeightKet_norm_eq_one w hw hsum)]
  rw [finiteWeightKet_diagonal_variance w ququartEnergy hw]
  rfl

theorem ququart_realized_mixedSpikeSLDQuantumFisher_eq :
    mixedSpikeSLDQuantumFisher (1 / 8) (1 / 2)
        (finiteDiagonalHamiltonian ququartEnergy)
        (finiteWeightKet ququartPeriodicWeight) =
      mixedSpikeSLDQuantumFisher (1 / 8) (1 / 2)
        (finiteDiagonalHamiltonian ququartEnergy)
        (finiteWeightKet ququartAperiodicWeight) := by
  rw [ququartMixedSpikeQuantumFisher_eq_SLD ququartPeriodicWeight
      ququartPeriodicWeight_nonneg ququartPeriodicWeight_sum,
    ququartMixedSpikeQuantumFisher_eq_SLD ququartAperiodicWeight
      ququartAperiodicWeight_nonneg ququartAperiodicWeight_sum,
    ququart_mixedSpikeQuantumFisher_eq]

/-- Both four-level mixed-spike matrices have unit trace. -/
theorem ququart_mixedSpikeMatrix_trace_eq_one :
    Matrix.trace
        (finiteMixedSpikeMatrix (1 / 8) (1 / 2) ququartPeriodicWeight) = 1 ∧
      Matrix.trace
        (finiteMixedSpikeMatrix (1 / 8) (1 / 2) ququartAperiodicWeight) = 1 := by
  constructor
  · rw [finiteMixedSpikeMatrix_trace (1 / 8) (1 / 2)
      ququartPeriodicWeight ququartPeriodicWeight_nonneg,
      ququartPeriodicWeight_sum]
    norm_num
  · rw [finiteMixedSpikeMatrix_trace (1 / 8) (1 / 2)
      ququartAperiodicWeight ququartAperiodicWeight_nonneg,
      ququartAperiodicWeight_sum]
    norm_num

/-- Positive background makes both realized four-level states full rank. -/
theorem ququart_mixedSpikeState_fullRank :
    Function.Injective
        (mixedSpikeState (1 / 8) (1 / 2)
          (finiteWeightKet ququartPeriodicWeight)) ∧
      Function.Injective
        (mixedSpikeState (1 / 8) (1 / 2)
          (finiteWeightKet ququartAperiodicWeight)) := by
  constructor <;>
    exact mixedSpikeState_injective (by norm_num) (by norm_num) _

/-- Both states have spike eigenvalue `5/8` and orthogonal eigenvalue `1/8`. -/
theorem ququart_realized_mixedSpike_common_spectral_action :
    mixedSpikeState (1 / 8) (1 / 2)
        (finiteWeightKet ququartPeriodicWeight)
        (finiteWeightKet ququartPeriodicWeight) =
      (5 / 8 : ℂ) • finiteWeightKet ququartPeriodicWeight ∧
    mixedSpikeState (1 / 8) (1 / 2)
        (finiteWeightKet ququartAperiodicWeight)
        (finiteWeightKet ququartAperiodicWeight) =
      (5 / 8 : ℂ) • finiteWeightKet ququartAperiodicWeight ∧
    (∀ x, inner ℂ (finiteWeightKet ququartPeriodicWeight) x = 0 →
      mixedSpikeState (1 / 8) (1 / 2)
          (finiteWeightKet ququartPeriodicWeight) x = (1 / 8 : ℂ) • x) ∧
    (∀ x, inner ℂ (finiteWeightKet ququartAperiodicWeight) x = 0 →
      mixedSpikeState (1 / 8) (1 / 2)
          (finiteWeightKet ququartAperiodicWeight) x = (1 / 8 : ℂ) • x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      mixedSpikeState (1 / 8) (1 / 2)
          (finiteWeightKet ququartPeriodicWeight)
          (finiteWeightKet ququartPeriodicWeight) =
          ((((1 / 8 : ℝ) + 1 / 2 : ℝ) : ℂ) •
            finiteWeightKet ququartPeriodicWeight) :=
        mixedSpikeState_apply_self (1 / 8) (1 / 2)
          (finiteWeightKet_norm_eq_one ququartPeriodicWeight
            ququartPeriodicWeight_nonneg ququartPeriodicWeight_sum)
      _ = (5 / 8 : ℂ) • finiteWeightKet ququartPeriodicWeight := by norm_num
  · calc
      mixedSpikeState (1 / 8) (1 / 2)
          (finiteWeightKet ququartAperiodicWeight)
          (finiteWeightKet ququartAperiodicWeight) =
          ((((1 / 8 : ℝ) + 1 / 2 : ℝ) : ℂ) •
            finiteWeightKet ququartAperiodicWeight) :=
        mixedSpikeState_apply_self (1 / 8) (1 / 2)
          (finiteWeightKet_norm_eq_one ququartAperiodicWeight
            ququartAperiodicWeight_nonneg ququartAperiodicWeight_sum)
      _ = (5 / 8 : ℂ) • finiteWeightKet ququartAperiodicWeight := by norm_num
  · intro x hx
    calc
      mixedSpikeState (1 / 8) (1 / 2)
          (finiteWeightKet ququartPeriodicWeight) x =
          (((1 / 8 : ℝ) : ℂ) • x) :=
        mixedSpikeState_apply_of_orthogonal (1 / 8) (1 / 2) hx
      _ = (1 / 8 : ℂ) • x := by norm_num
  · intro x hx
    calc
      mixedSpikeState (1 / 8) (1 / 2)
          (finiteWeightKet ququartAperiodicWeight) x =
          (((1 / 8 : ℝ) : ℂ) • x) :=
        mixedSpikeState_apply_of_orthogonal (1 / 8) (1 / 2) hx
      _ = (1 / 8 : ℂ) • x := by norm_num

/--
Capstone moment-matched separation: equal first two energy moments, actual
Hilbert--Schmidt speed, and actual SLD quantum Fisher information coexist
with exact periodicity for one clock and sharp inverse-resolution recurrence
for the other.
-/
theorem ququart_equal_moments_information_global_recurrence_separation :
    (∑ i, ququartPeriodicWeight i * ququartEnergy i) =
        ∑ i, ququartAperiodicWeight i * ququartEnergy i ∧
    (∑ i, ququartPeriodicWeight i * ququartEnergy i ^ (2 : ℕ)) =
        ∑ i, ququartAperiodicWeight i * ququartEnergy i ^ (2 : ℕ) ∧
    ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian ququartEnergy)
          (finiteWeightKet ququartPeriodicWeight)) =
      ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian ququartEnergy)
          (finiteWeightKet ququartAperiodicWeight)) ∧
    mixedSpikeSLDQuantumFisher (1 / 8) (1 / 2)
        (finiteDiagonalHamiltonian ququartEnergy)
        (finiteWeightKet ququartPeriodicWeight) =
      mixedSpikeSLDQuantumFisher (1 / 8) (1 / 2)
        (finiteDiagonalHamiltonian ququartEnergy)
        (finiteWeightKet ququartAperiodicWeight) ∧
    (∀ n : ℕ, ququartTickRecurrenceAmplitude ququartPeriodicWeight
        (ququartPeriodicTickPhase n) = 0) ∧
    (∀ n : ℕ, 0 < n →
      Real.sqrt
          (ququartIrrationalMass * (1 - ququartIrrationalMass)) /
          (2 * (n : ℝ)) ≤
        ququartTickRecurrenceAmplitude ququartAperiodicWeight
          (ququartAperiodicTickPhase n)) ∧
    (∀ Q : ℕ, 0 < Q →
      ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
        ququartTickRecurrenceAmplitude ququartAperiodicWeight
            (ququartAperiodicTickPhase n) ≤
          Real.pi *
            Real.sqrt
              (ququartIrrationalMass * (1 - ququartIrrationalMass)) /
                (Q : ℝ)) := by
  refine ⟨ququart_first_energy_moment_eq,
    ququart_second_energy_moment_eq,
    ququart_realized_mixedSpikeHSSpeedSq_eq,
    ququart_realized_mixedSpikeSLDQuantumFisher_eq, ?_, ?_, ?_⟩
  · exact ququartPeriodic_tickRecurrenceAmplitude_eq_zero
  · exact ququartAperiodic_tickRecurrenceAmplitude_lower
  · exact exists_ququartAperiodic_tickRecurrenceAmplitude_upper

end RHTower
