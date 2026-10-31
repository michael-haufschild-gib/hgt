import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeGeneratorOrthogonalRows
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.SharpPrimeSector

/-!
# Arithmetic source charge at vanishing adjunction energy

An explicit normalized coherent prime packet carries any prescribed
constant generator charge at arbitrarily small adjunction energy.
Its remaining output tends to zero in complete-period square mean.
The actual harmonic pole projection preserves this phenomenon at every
finite horizon.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SelectiveMultiscaleArithmeticPositivity

theorem primePoleResponse_const_mul (Q : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    primePoleResponse Q (fun p => t * a p) = t * primePoleResponse Q a := by
  simp only [primePoleResponse, mul_sum]
  exact sum_congr rfl fun p _ => by ring

theorem primeAdjunctionMass_primeOnly_const_mul (Q : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    primeAdjunctionMass Q (primeOnly (fun p => t * a p)) =
      t ^ 2 * primeAdjunctionMass Q (primeOnly a) := by
  simp only [primeAdjunctionMass_primeOnly, mul_pow, mul_sum]
  exact sum_congr rfl fun p _ => by ring

/-- Exact charge and energy of a normalized coherent prime packet. -/
theorem normalizedPrimeCharge_response_and_energy {Q : ℕ} (hQ : 2 ≤ Q) (t : ℝ) :
    primePoleResponse Q (fun p => (t / primePoleScale Q) * primePoleWitness p) = t ∧
      primeAdjunctionMass Q
        (primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p)) =
          t ^ 2 / primePoleScale Q := by
  have hB := (primePoleScale_pos hQ).ne'
  constructor
  · rw [primePoleResponse_const_mul, (primePoleWitness_response_and_energy Q).1,
      div_mul_cancel₀ _ hB]
  · rw [primeAdjunctionMass_primeOnly_const_mul,
      (primePoleWitness_response_and_energy Q).2]
    field_simp [hB]

/-- Any constant source charge can survive arbitrarily small adjunction energy,
with arbitrarily small nonconstant output, on every actual harmonic pole hyperplane. -/
theorem exists_harmonic_neutral_arbitrarily_small_energy_charge
    (R : ℕ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, R ≤ Q ∧ 2 ≤ Q ∧ ∀ N : ℕ, 1 ≤ N → ∃ a : ℕ → ℝ,
      harmonicSum N (conductorHorizonProfile Q a) = 0 ∧
      primeAdjunctionMass Q a < ε ∧
      packetMean Q (arithmeticPrimeGenerator Q a) = t ∧
      packetMean Q (fun n => (arithmeticPrimeGenerator Q a n - t) ^ 2) < ε := by
  let k : ℝ := Real.log 2 / 2
  have hk : 0 ≤ k := div_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num)
  have hlarge := (tendsto_atTop.mp primePoleScale_tendsto_atTop)
    ((1 + k) * t ^ 2 / ε + 1)
  obtain ⟨Q, hQR, hQ2, hBlarge⟩ :=
    ((eventually_ge_atTop R).and ((eventually_ge_atTop 2).and hlarge)).exists
  have hB := primePoleScale_pos hQ2
  let b : ℕ → ℝ := fun p => (t / primePoleScale Q) * primePoleWitness p
  have hb := normalizedPrimeCharge_response_and_energy hQ2 t
  have hsmall : (1 + k) * (t ^ 2 / primePoleScale Q) < ε := by
    have hmul := mul_le_mul_of_nonneg_right hBlarge hε.le
    rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at hmul
    rw [← mul_div_assoc, div_lt_iff₀ hB]
    nlinarith only [hmul, hε]
  have hnonneg : 0 ≤ t ^ 2 / primePoleScale Q := div_nonneg (sq_nonneg _) hB.le
  have henergy : t ^ 2 / primePoleScale Q < ε :=
    (show t ^ 2 / primePoleScale Q ≤ (1 + k) * (t ^ 2 / primePoleScale Q) by
      nlinarith only [mul_nonneg hk hnonneg]).trans_lt hsmall
  have hcenter : k * (t ^ 2 / primePoleScale Q) < ε :=
    (show k * (t ^ 2 / primePoleScale Q) ≤ (1 + k) * (t ^ 2 / primePoleScale Q) by
      linarith only [hnonneg]).trans_lt hsmall
  refine ⟨Q, hQR, hQ2, ?_⟩
  intro N hN
  refine ⟨harmonicCenteredCoefficients Q N (primeOnly b),
    harmonicSum_centeredCoefficients (by omega : 1 ≤ Q) hN _, ?_, ?_, ?_⟩
  · rw [primeAdjunctionMass_harmonicCentered]
    exact hb.2.trans_lt henergy
  · change packetMean Q (fun n => arithmeticPrimeGenerator Q
      (harmonicCenteredCoefficients Q N (primeOnly b)) n) = t
    simp only [arithmeticPrimeGenerator_harmonicCentered]
    rw [packetMean_arithmeticPrimeGenerator_primeOnly]
    exact hb.1
  · simp only [arithmeticPrimeGenerator_harmonicCentered]
    have h := primeCenteredGenerator_period_sq_le Q b
    rw [show primePoleResponse Q b = t from hb.1,
      show primeAdjunctionMass Q (primeOnly b) = t ^ 2 / primePoleScale Q from hb.2] at h
    exact h.trans_lt hcenter

#print axioms normalizedPrimeCharge_response_and_energy
#print axioms exists_harmonic_neutral_arbitrarily_small_energy_charge

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
