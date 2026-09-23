import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherenceRecurrence
import GaloisForLFunctions.RHTower.MixedSpikeQuantumFisher
import GaloisForLFunctions.RHTower.FiniteMixedSpikeRealization
import GaloisForLFunctions.HTGeometry.LinearExponentialSum
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne
import Mathlib.NumberTheory.Real.Irrational

/-!
# Equal-information mixed-state clocks with different recurrence laws

Two explicit full-rank qutrit clock states have the same Hamiltonian, density
spectrum, initial Hilbert--Schmidt speed, and elapsed-time quantum Fisher
value.  At the common stroboscopic ticks `2πn`, one state returns exactly at
every tick while the other has a sharp inverse-resolution recurrence law.

The separation is arithmetic rather than local: the second state sees the
irrational gap `√2`.  An elementary quadratic-norm argument gives the lower
bound and one-dimensional Dirichlet approximation gives the matching upper
bound.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Common population parameter for the explicit qutrit pair. -/
def qutritRecurrenceDelta : ℝ := Real.sqrt 2 - 1

/-- Populations of the exactly periodic qutrit clock. -/
def qutritPeriodicWeight : Fin 3 → ℝ :=
  ![1 - qutritRecurrenceDelta, qutritRecurrenceDelta, 0]

/-- Populations of the irrational qutrit clock. -/
def qutritAperiodicWeight : Fin 3 → ℝ :=
  ![1 - 2 * qutritRecurrenceDelta, qutritRecurrenceDelta,
    qutritRecurrenceDelta]

/-- The shared energy list `(0,1,√2)`. -/
def qutritEnergy : Fin 3 → ℝ := ![0, 1, Real.sqrt 2]

/-- Variance of a finite energy list in a real weight packet. -/
def finiteWeightedVariance {d : ℕ}
    (w energy : Fin d → ℝ) : ℝ :=
  (∑ i, w i * energy i ^ (2 : ℕ)) - (∑ i, w i * energy i) ^ (2 : ℕ)

theorem qutritRecurrenceDelta_pos : 0 < qutritRecurrenceDelta := by
  rw [qutritRecurrenceDelta]
  have hs : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  linarith

theorem qutritRecurrenceDelta_lt_half :
    qutritRecurrenceDelta < 1 / 2 := by
  rw [qutritRecurrenceDelta]
  have hs : Real.sqrt 2 < 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  linarith

theorem qutritPeriodicWeight_sum :
    ∑ i, qutritPeriodicWeight i = 1 := by
  simp [qutritPeriodicWeight, Fin.sum_univ_three]

theorem qutritAperiodicWeight_sum :
    ∑ i, qutritAperiodicWeight i = 1 := by
  simp [qutritAperiodicWeight, Fin.sum_univ_three]
  ring

theorem qutritPeriodicWeight_nonneg :
    ∀ i, 0 ≤ qutritPeriodicWeight i := by
  intro i
  fin_cases i
  · simp [qutritPeriodicWeight]
    linarith [qutritRecurrenceDelta_pos,
      qutritRecurrenceDelta_lt_half]
  · simp [qutritPeriodicWeight]
    exact qutritRecurrenceDelta_pos.le
  · simp [qutritPeriodicWeight]

theorem qutritAperiodicWeight_nonneg :
    ∀ i, 0 ≤ qutritAperiodicWeight i := by
  intro i
  fin_cases i
  · simp [qutritAperiodicWeight]
    linarith [qutritRecurrenceDelta_lt_half]
  · simp [qutritAperiodicWeight]
    exact qutritRecurrenceDelta_pos.le
  · simp [qutritAperiodicWeight]
    exact qutritRecurrenceDelta_pos.le

/-- The two qutrit population packets have exactly the same energy variance. -/
theorem qutrit_weightedVariance_eq :
    finiteWeightedVariance qutritPeriodicWeight qutritEnergy =
      finiteWeightedVariance qutritAperiodicWeight qutritEnergy := by
  simp [finiteWeightedVariance, qutritPeriodicWeight,
    qutritAperiodicWeight, qutritEnergy, Fin.sum_univ_three]
  rw [qutritRecurrenceDelta]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Phase packet of the periodic clock at tick `2πn`. -/
def qutritPeriodicTickPhase (_n : ℕ) : Fin 3 → ℂ := ![1, 1, 1]

/-- Phase packet of the irrational clock at tick `2πn`. -/
def qutritAperiodicTickPhase (n : ℕ) : Fin 3 → ℂ :=
  ![1, 1, HTGeometry.ee ((n : ℝ) * Real.sqrt 2)]

/-- Fidelity deficit of a finite weighted phase packet. -/
def weightedFidelityDeficit {d : ℕ}
    (w : Fin d → ℝ) (phase : Fin d → ℂ) : ℝ :=
  1 - ‖projectiveWeightedPhaseAmplitude w phase‖ ^ (2 : ℕ)

theorem qutritPeriodic_fidelityDeficit_eq_zero (n : ℕ) :
    weightedFidelityDeficit qutritPeriodicWeight
      (qutritPeriodicTickPhase n) = 0 := by
  simp [weightedFidelityDeficit, projectiveWeightedPhaseAmplitude,
    qutritPeriodicWeight, qutritPeriodicTickPhase, Fin.sum_univ_three]

/-- Exact fidelity deficit of the irrational qutrit clock. -/
theorem qutritAperiodic_fidelityDeficit_eq (n : ℕ) :
    weightedFidelityDeficit qutritAperiodicWeight
        (qutritAperiodicTickPhase n) =
      qutritRecurrenceDelta * (1 - qutritRecurrenceDelta) *
        ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ ^ (2 : ℕ) := by
  let phase := qutritAperiodicTickPhase n
  have hphase : ∀ i, ‖phase i‖ = 1 := by
    intro i
    fin_cases i
    · simp [phase, qutritAperiodicTickPhase]
    · simp [phase, qutritAperiodicTickPhase]
    · simp [phase, qutritAperiodicTickPhase, HTGeometry.norm_ee]
  have h := projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit
    qutritAperiodicWeight phase qutritAperiodicWeight_sum hphase
  rw [weightedFidelityDeficit]
  rw [show projectiveWeightedPairwiseEnergy qutritAperiodicWeight phase =
      2 * qutritRecurrenceDelta * (1 - qutritRecurrenceDelta) *
        ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ ^ (2 : ℕ) by
    simp [projectiveWeightedPairwiseEnergy, qutritAperiodicWeight,
      phase, qutritAperiodicTickPhase, Fin.sum_univ_three,
      norm_sub_rev]
    ring] at h
  nlinarith

/-- Operational recurrence amplitude of the `b=1/6`, `c=1/2` mixed-spike
clock, equal to one half of the sine distance of its spike directions. -/
def qutritTickRecurrenceAmplitude (w : Fin 3 → ℝ)
    (phase : Fin 3 → ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt (weightedFidelityDeficit w phase)

theorem qutritPeriodic_tickRecurrenceAmplitude_eq_zero (n : ℕ) :
    qutritTickRecurrenceAmplitude qutritPeriodicWeight
      (qutritPeriodicTickPhase n) = 0 := by
  rw [qutritTickRecurrenceAmplitude, qutritPeriodic_fidelityDeficit_eq_zero,
    Real.sqrt_zero, mul_zero]

/-- Exact stroboscopic recurrence amplitude of the irrational qutrit clock. -/
theorem qutritAperiodic_tickRecurrenceAmplitude_eq (n : ℕ) :
    qutritTickRecurrenceAmplitude qutritAperiodicWeight
        (qutritAperiodicTickPhase n) =
      (1 / 2 : ℝ) *
        Real.sqrt (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) *
          ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := by
  rw [qutritTickRecurrenceAmplitude, qutritAperiodic_fidelityDeficit_eq,
    Real.sqrt_mul (mul_nonneg qutritRecurrenceDelta_pos.le
      (by linarith [qutritRecurrenceDelta_lt_half]))]
  rw [Real.sqrt_sq (norm_nonneg _)]
  ring

/-- Elementary bad-approximation bound for integer multiples of `√2`. -/
theorem distToInt_nat_mul_sqrt_two_lower
    (n : ℕ) (hn : 0 < n) :
    1 / (4 * (n : ℝ)) ≤
      HTGeometry.distToInt ((n : ℝ) * Real.sqrt 2) := by
  let x : ℝ := (n : ℝ) * Real.sqrt 2
  let p : ℤ := round x
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ (2 : ℕ) = 2 :=
    Real.sq_sqrt (by norm_num)
  have hslt : Real.sqrt 2 < 3 / 2 := by
    nlinarith
  have hdistHalf : |x - (p : ℝ)| ≤ 1 / 2 := by
    simpa [HTGeometry.distToInt, x, p] using
      HTGeometry.distToInt_le_half x
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hxle : x ≤ 2 * (n : ℝ) := by
    dsimp only [x]
    nlinarith
  have hpabs : |(p : ℝ)| ≤ 2 * (n : ℝ) := by
    have htri : |(p : ℝ)| ≤ |x| + |x - (p : ℝ)| := by
      calc
        |(p : ℝ)| = |x - (x - (p : ℝ))| := by ring_nf
        _ ≤ |x| + |x - (p : ℝ)| := abs_sub _ _
    rw [abs_of_nonneg hx0] at htri
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hirr : Irrational x := by
    dsimp only [x]
    simpa only [Int.cast_natCast] using
      irrational_sqrt_two.intCast_mul
        (show (n : ℤ) ≠ 0 by exact_mod_cast hn.ne')
  let k : ℤ := 2 * (n : ℤ) ^ (2 : ℕ) - p ^ (2 : ℕ)
  have hk : k ≠ 0 := by
    intro hk0
    have hkR : (2 : ℝ) * (n : ℝ) ^ (2 : ℕ) - (p : ℝ) ^ (2 : ℕ) = 0 := by
      exact_mod_cast hk0
    have hsquare : x ^ (2 : ℕ) = (p : ℝ) ^ (2 : ℕ) := by
      dsimp only [x]
      rw [mul_pow, hs2]
      nlinarith
    have hfactor : (x - (p : ℝ)) * (x + (p : ℝ)) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · exact hirr.ne_int p (sub_eq_zero.mp hminus)
    · exact hirr.ne_int (-p) (by
        rw [Int.cast_neg]
        linarith)
  have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
    exact_mod_cast Int.one_le_abs hk
  have hfactorAbs :
      |(k : ℝ)| =
        |x - (p : ℝ)| * |x + (p : ℝ)| := by
    have hkR :
        (k : ℝ) = (x - (p : ℝ)) * (x + (p : ℝ)) := by
      dsimp only [k, x]
      push_cast
      nlinarith [hs2]
    rw [hkR, abs_mul]
  have hplus : |x + (p : ℝ)| ≤ 4 * (n : ℝ) := by
    calc
      |x + (p : ℝ)| ≤ |x| + |(p : ℝ)| := abs_add_le _ _
      _ = x + |(p : ℝ)| := by rw [abs_of_nonneg hx0]
      _ ≤ 4 * (n : ℝ) := by linarith
  have hprod :
      1 ≤ HTGeometry.distToInt x * (4 * (n : ℝ)) := by
    have hdist :
        HTGeometry.distToInt x = |x - (p : ℝ)| := by
      rfl
    rw [hdist]
    calc
      1 ≤ |(k : ℝ)| := hkabs
      _ = |x - (p : ℝ)| * |x + (p : ℝ)| := hfactorAbs
      _ ≤ |x - (p : ℝ)| * (4 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hplus (abs_nonneg _)
  change 1 / (4 * (n : ℝ)) ≤ HTGeometry.distToInt x
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ))).2
    (by simpa [mul_comm] using hprod)

/-- Backward-compatible RHTower name for the generic additive-character chord bound. -/
theorem norm_ee_sub_one_le_two_pi_mul_of_integer_approximation
    {x e : ℝ} (r : ℤ)
    (happrox : |x - (r : ℝ)| ≤ e) :
    ‖HTGeometry.ee x - 1‖ ≤ 2 * Real.pi * e :=
  HTGeometry.norm_ee_sub_one_le_two_pi_mul_of_integer_approximation r happrox

/-- Every positive tick of the irrational qutrit clock is at least a fixed
multiple of `1/n` away from recurrence. -/
theorem qutritAperiodic_tickRecurrenceAmplitude_lower
    (n : ℕ) (hn : 0 < n) :
    Real.sqrt
          (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) /
        (2 * (n : ℝ)) ≤
      qutritTickRecurrenceAmplitude qutritAperiodicWeight
        (qutritAperiodicTickPhase n) := by
  rw [qutritAperiodic_tickRecurrenceAmplitude_eq]
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
        (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) :=
    Real.sqrt_nonneg _
  calc
    Real.sqrt
          (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) /
        (2 * (n : ℝ)) =
        (1 / 2 : ℝ) *
          Real.sqrt
            (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) *
              (1 / (n : ℝ)) := by ring
    _ ≤ (1 / 2 : ℝ) *
        Real.sqrt
          (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) *
            ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := by
      gcongr

/-- Every positive resolution `Q` has a return tick no later than `Q`, with
recurrence amplitude bounded by an explicit constant times `1/Q`. -/
theorem exists_qutritAperiodic_tickRecurrenceAmplitude_upper
    (Q : ℕ) (hQ : 0 < Q) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
      qutritTickRecurrenceAmplitude qutritAperiodicWeight
          (qutritAperiodicTickPhase n) ≤
        Real.pi *
          Real.sqrt
            (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) /
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
  rw [qutritAperiodic_tickRecurrenceAmplitude_eq]
  have hsqrt :
      0 ≤ Real.sqrt
        (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) :=
    Real.sqrt_nonneg _
  calc
    (1 / 2 : ℝ) *
        Real.sqrt
          (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) *
            ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ ≤
        (1 / 2 : ℝ) *
          Real.sqrt
            (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) *
              (2 * Real.pi * (1 / (Q : ℝ))) := by
      gcongr
    _ = Real.pi *
        Real.sqrt
          (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) /
            (Q : ℝ) := by ring

/-- Squared Hilbert--Schmidt speed of the `c=1/2` mixed-spike family. -/
def qutritMixedSpikeHSSpeedSq (w : Fin 3 → ℝ) : ℝ :=
  2 * (1 / 2 : ℝ) ^ (2 : ℕ) * finiteWeightedVariance w qutritEnergy

/-- Standard spectral-formula QFI of the `b=1/6`, `c=1/2` mixed-spike
family for elapsed-time estimation. -/
def qutritMixedSpikeQuantumFisher (w : Fin 3 → ℝ) : ℝ :=
  4 * (1 / 2 : ℝ) ^ (2 : ℕ) / (2 * (1 / 6 : ℝ) + 1 / 2) *
    finiteWeightedVariance w qutritEnergy

theorem qutrit_mixedSpikeHSSpeedSq_eq :
    qutritMixedSpikeHSSpeedSq qutritPeriodicWeight =
      qutritMixedSpikeHSSpeedSq qutritAperiodicWeight := by
  rw [qutritMixedSpikeHSSpeedSq, qutritMixedSpikeHSSpeedSq,
    qutrit_weightedVariance_eq]

/-- The scalar qutrit speed is the actual squared Hilbert--Schmidt tangent norm. -/
theorem qutritMixedSpikeHSSpeedSq_eq_realized
    (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian qutritEnergy) (finiteWeightKet w)) =
      qutritMixedSpikeHSSpeedSq w := by
  rw [mixedSpikeUnitaryTangent_hsNormSq (1 / 2)
    (finiteDiagonalHamiltonian qutritEnergy)
    (finiteDiagonalHamiltonian_selfAdjoint qutritEnergy)
    (finiteWeightKet w) (finiteWeightKet_norm_eq_one w hw hsum)]
  rw [finiteWeightKet_diagonal_variance w qutritEnergy hw]
  rfl

/-- The two realized qutrit clocks have exactly the same initial HS speed. -/
theorem qutrit_realized_mixedSpikeHSSpeedSq_eq :
    ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian qutritEnergy)
          (finiteWeightKet qutritPeriodicWeight)) =
      ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian qutritEnergy)
          (finiteWeightKet qutritAperiodicWeight)) := by
  rw [qutritMixedSpikeHSSpeedSq_eq_realized qutritPeriodicWeight
      qutritPeriodicWeight_nonneg qutritPeriodicWeight_sum,
    qutritMixedSpikeHSSpeedSq_eq_realized qutritAperiodicWeight
      qutritAperiodicWeight_nonneg qutritAperiodicWeight_sum,
    qutrit_mixedSpikeHSSpeedSq_eq]

theorem qutrit_mixedSpikeQuantumFisher_eq :
    qutritMixedSpikeQuantumFisher qutritPeriodicWeight =
      qutritMixedSpikeQuantumFisher qutritAperiodicWeight := by
  rw [qutritMixedSpikeQuantumFisher, qutritMixedSpikeQuantumFisher,
    qutrit_weightedVariance_eq]

/--
The scalar qutrit QFI is the SLD quantum Fisher information of the realized
full-rank mixed-spike state and diagonal Hamiltonian.
-/
theorem qutritMixedSpikeQuantumFisher_eq_SLD
    (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    mixedSpikeSLDQuantumFisher (1 / 6) (1 / 2)
        (finiteDiagonalHamiltonian qutritEnergy) (finiteWeightKet w) =
      qutritMixedSpikeQuantumFisher w := by
  rw [mixedSpikeSLDQuantumFisher_eq (1 / 6) (1 / 2) (by norm_num)
    (finiteDiagonalHamiltonian qutritEnergy)
    (finiteDiagonalHamiltonian_selfAdjoint qutritEnergy)
    (finiteWeightKet w) (finiteWeightKet_norm_eq_one w hw hsum)]
  rw [finiteWeightKet_diagonal_variance w qutritEnergy hw]
  rfl

/--
The two concrete full-rank qutrit clocks have exactly the same operator-level
SLD quantum Fisher information under their shared Hamiltonian.
-/
theorem qutrit_realized_mixedSpikeSLDQuantumFisher_eq :
    mixedSpikeSLDQuantumFisher (1 / 6) (1 / 2)
        (finiteDiagonalHamiltonian qutritEnergy)
        (finiteWeightKet qutritPeriodicWeight) =
      mixedSpikeSLDQuantumFisher (1 / 6) (1 / 2)
        (finiteDiagonalHamiltonian qutritEnergy)
        (finiteWeightKet qutritAperiodicWeight) := by
  rw [qutritMixedSpikeQuantumFisher_eq_SLD qutritPeriodicWeight
      qutritPeriodicWeight_nonneg qutritPeriodicWeight_sum,
    qutritMixedSpikeQuantumFisher_eq_SLD qutritAperiodicWeight
      qutritAperiodicWeight_nonneg qutritAperiodicWeight_sum,
    qutrit_mixedSpikeQuantumFisher_eq]

/-- Both explicit qutrit mixed-spike matrices have unit trace. -/
theorem qutrit_mixedSpikeMatrix_trace_eq_one :
    Matrix.trace
        (finiteMixedSpikeMatrix (1 / 6) (1 / 2) qutritPeriodicWeight) = 1 ∧
      Matrix.trace
        (finiteMixedSpikeMatrix (1 / 6) (1 / 2) qutritAperiodicWeight) = 1 := by
  constructor
  · rw [finiteMixedSpikeMatrix_trace (1 / 6) (1 / 2)
      qutritPeriodicWeight qutritPeriodicWeight_nonneg,
      qutritPeriodicWeight_sum]
    norm_num
  · rw [finiteMixedSpikeMatrix_trace (1 / 6) (1 / 2)
      qutritAperiodicWeight qutritAperiodicWeight_nonneg,
      qutritAperiodicWeight_sum]
    norm_num

/-- Positive background makes both realized qutrit state operators full rank. -/
theorem qutrit_mixedSpikeState_fullRank :
    Function.Injective
        (mixedSpikeState (1 / 6) (1 / 2)
          (finiteWeightKet qutritPeriodicWeight)) ∧
      Function.Injective
        (mixedSpikeState (1 / 6) (1 / 2)
          (finiteWeightKet qutritAperiodicWeight)) := by
  constructor <;>
    exact mixedSpikeState_injective (by norm_num) (by norm_num) _

theorem qutrit_common_variance_pos :
    0 < finiteWeightedVariance qutritPeriodicWeight qutritEnergy := by
  simp [finiteWeightedVariance, qutritPeriodicWeight, qutritEnergy,
    Fin.sum_univ_three]
  have hd0 := qutritRecurrenceDelta_pos
  have hd1 : qutritRecurrenceDelta < 1 := by
    linarith [qutritRecurrenceDelta_lt_half]
  nlinarith

theorem qutrit_common_speed_sq_pos :
    0 < qutritMixedSpikeHSSpeedSq qutritPeriodicWeight := by
  rw [qutritMixedSpikeHSSpeedSq]
  norm_num
  exact qutrit_common_variance_pos

theorem qutrit_common_quantumFisher_pos :
    0 < qutritMixedSpikeQuantumFisher qutritPeriodicWeight := by
  rw [qutritMixedSpikeQuantumFisher]
  norm_num
  exact qutrit_common_variance_pos

/-- The explicit qutrit spike values are normalized and strictly positive. -/
theorem qutrit_mixedSpike_spectral_values :
    (1 / 6 : ℝ) + 1 / 2 = 2 / 3 ∧
      3 * (1 / 6 : ℝ) + 1 / 2 = 1 ∧
      (0 : ℝ) < 1 / 6 := by
  norm_num

/-- Both realized qutrit states have spike eigenvalue `2/3` and orthogonal
eigenvalue `1/6`. -/
theorem qutrit_realized_mixedSpike_common_spectral_action :
    mixedSpikeState (1 / 6) (1 / 2)
        (finiteWeightKet qutritPeriodicWeight)
        (finiteWeightKet qutritPeriodicWeight) =
      (2 / 3 : ℂ) • finiteWeightKet qutritPeriodicWeight ∧
    mixedSpikeState (1 / 6) (1 / 2)
        (finiteWeightKet qutritAperiodicWeight)
        (finiteWeightKet qutritAperiodicWeight) =
      (2 / 3 : ℂ) • finiteWeightKet qutritAperiodicWeight ∧
    (∀ x, inner ℂ (finiteWeightKet qutritPeriodicWeight) x = 0 →
      mixedSpikeState (1 / 6) (1 / 2)
          (finiteWeightKet qutritPeriodicWeight) x = (1 / 6 : ℂ) • x) ∧
    (∀ x, inner ℂ (finiteWeightKet qutritAperiodicWeight) x = 0 →
      mixedSpikeState (1 / 6) (1 / 2)
          (finiteWeightKet qutritAperiodicWeight) x = (1 / 6 : ℂ) • x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      mixedSpikeState (1 / 6) (1 / 2)
          (finiteWeightKet qutritPeriodicWeight)
          (finiteWeightKet qutritPeriodicWeight) =
          ((((1 / 6 : ℝ) + 1 / 2 : ℝ) : ℂ) •
            finiteWeightKet qutritPeriodicWeight) :=
        mixedSpikeState_apply_self (1 / 6) (1 / 2)
          (finiteWeightKet_norm_eq_one qutritPeriodicWeight
            qutritPeriodicWeight_nonneg qutritPeriodicWeight_sum)
      _ = (2 / 3 : ℂ) • finiteWeightKet qutritPeriodicWeight := by norm_num
  · calc
      mixedSpikeState (1 / 6) (1 / 2)
          (finiteWeightKet qutritAperiodicWeight)
          (finiteWeightKet qutritAperiodicWeight) =
          ((((1 / 6 : ℝ) + 1 / 2 : ℝ) : ℂ) •
            finiteWeightKet qutritAperiodicWeight) :=
        mixedSpikeState_apply_self (1 / 6) (1 / 2)
          (finiteWeightKet_norm_eq_one qutritAperiodicWeight
            qutritAperiodicWeight_nonneg qutritAperiodicWeight_sum)
      _ = (2 / 3 : ℂ) • finiteWeightKet qutritAperiodicWeight := by norm_num
  · intro x hx
    calc
      mixedSpikeState (1 / 6) (1 / 2)
          (finiteWeightKet qutritPeriodicWeight) x =
          (((1 / 6 : ℝ) : ℂ) • x) :=
        mixedSpikeState_apply_of_orthogonal (1 / 6) (1 / 2) hx
      _ = (1 / 6 : ℂ) • x := by norm_num
  · intro x hx
    calc
      mixedSpikeState (1 / 6) (1 / 2)
          (finiteWeightKet qutritAperiodicWeight) x =
          (((1 / 6 : ℝ) : ℂ) • x) :=
        mixedSpikeState_apply_of_orthogonal (1 / 6) (1 / 2) hx
      _ = (1 / 6 : ℂ) • x := by norm_num

/--
Capstone separation theorem.  The two full-rank qutrit clocks share their
Hamiltonian, complete state spectrum, Hilbert--Schmidt speed, and SLD quantum
Fisher information, yet one returns at every tick while the other obeys
matching inverse-resolution lower and upper recurrence laws.
-/
theorem qutrit_equal_information_global_recurrence_separation :
    ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian qutritEnergy)
          (finiteWeightKet qutritPeriodicWeight)) =
      ContinuousLinearMap.hsNormSq
        (mixedSpikeUnitaryTangent (1 / 2)
          (finiteDiagonalHamiltonian qutritEnergy)
          (finiteWeightKet qutritAperiodicWeight)) ∧
    mixedSpikeSLDQuantumFisher (1 / 6) (1 / 2)
        (finiteDiagonalHamiltonian qutritEnergy)
        (finiteWeightKet qutritPeriodicWeight) =
      mixedSpikeSLDQuantumFisher (1 / 6) (1 / 2)
        (finiteDiagonalHamiltonian qutritEnergy)
        (finiteWeightKet qutritAperiodicWeight) ∧
    (∀ n : ℕ, qutritTickRecurrenceAmplitude qutritPeriodicWeight
        (qutritPeriodicTickPhase n) = 0) ∧
    (∀ n : ℕ, 0 < n →
      Real.sqrt
          (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) /
          (2 * (n : ℝ)) ≤
        qutritTickRecurrenceAmplitude qutritAperiodicWeight
          (qutritAperiodicTickPhase n)) ∧
    (∀ Q : ℕ, 0 < Q →
      ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
        qutritTickRecurrenceAmplitude qutritAperiodicWeight
            (qutritAperiodicTickPhase n) ≤
          Real.pi *
            Real.sqrt
              (qutritRecurrenceDelta * (1 - qutritRecurrenceDelta)) /
                (Q : ℝ)) := by
  refine ⟨qutrit_realized_mixedSpikeHSSpeedSq_eq,
    qutrit_realized_mixedSpikeSLDQuantumFisher_eq, ?_, ?_, ?_⟩
  · exact qutritPeriodic_tickRecurrenceAmplitude_eq_zero
  · exact qutritAperiodic_tickRecurrenceAmplitude_lower
  · exact exists_qutritAperiodic_tickRecurrenceAmplitude_upper

end RHTower
