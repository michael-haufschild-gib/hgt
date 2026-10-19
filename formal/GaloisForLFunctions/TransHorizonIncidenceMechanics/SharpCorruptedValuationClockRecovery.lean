import GaloisForLFunctions.TransHorizonIncidenceMechanics.ValuationTraceCoprimeCompletionAndObservationState
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ValuationTraceErrorsErasuresAndRecoveryClock

/-!
# Sharp recovery clock for corrupted horizon-state observations

Observe the literal finite multiplicative state at consecutive times. With at
most e corrupted symbols and s erased positions, the phase is uniquely determined
exactly when the window reaches the maximum, over admitted prime powers q, of

  (e + s / 2) * q + (if Even s then q.totient else q).

Both sufficiency and an ambiguity witness below this threshold are unconditional.
The empty maximum handles horizons zero and one within the same theorem.
-/

set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section

/-- Every received window with at most e errors and s erasures determines the horizon phase uniquely. -/
def horizonObservationFaultRecovery (N W e s : ℕ) : Prop :=
  ∀ (E : Finset (Fin W)), E.card ≤ s → ∀ (z : Fin W → ℕ) (k l : ℕ),
    observationErrorCount E z (fun t => horizonObservationState N (k + (t : ℕ))) ≤ e →
    observationErrorCount E z (fun t => horizonObservationState N (l + (t : ℕ))) ≤ e →
    horizonObservationPhase N k = horizonObservationPhase N l

/-- Maximum of the exact prime-power mixed-fault clocks over admitted prime powers; empty maximum is zero. -/
def horizonFaultRecoveryClock (N e s : ℕ) : ℕ :=
  ((Icc 1 N).filter IsPrimePow).sup (fun q => primePowerFaultRecoveryClock q e s)

/-- Literal-state recovery is equivalent to GCD trace separation at distance budget 2e+s. -/
theorem horizonObservationFaultRecovery_iff_distance_separation (N W e s : ℕ) :
    horizonObservationFaultRecovery N W e s ↔
      ∀ k l, valuationTraceDistance (horizonObservationModulus N) W k l ≤ 2 * e + s →
        Nat.ModEq (horizonObservationModulus N) k l := by
  constructor
  · intro h k l hdist
    have hp : hammingDist
        (fun t : Fin W => horizonObservationState N (k + (t : ℕ)))
        (fun t : Fin W => horizonObservationState N (l + (t : ℕ))) ≤ 2 * e + s := by
      simpa only [horizonObservationState_eq_gcd, valuationTraceDistance] using hdist
    obtain ⟨E, hE, z, hk, hl⟩ :=
      (shared_faulty_observation_iff_hammingDist_le _ _ e s).mpr hp
    exact h E hE z k l hk hl
  · intro h E hE z k l hk hl
    apply h k l
    have hp := (shared_faulty_observation_iff_hammingDist_le
      (fun t : Fin W => horizonObservationState N (k + (t : ℕ)))
      (fun t : Fin W => horizonObservationState N (l + (t : ℕ))) e s).mp
      ⟨E, hE, z, hk, hl⟩
    simpa only [horizonObservationState_eq_gcd, valuationTraceDistance] using hp

private theorem recovery_clock_mono_of_dvd {q r : ℕ} (hr : 0 < r)
    (hqr : q ∣ r) (e s : ℕ) :
    primePowerFaultRecoveryClock q e s ≤ primePowerFaultRecoveryClock r e s := by
  have hle := Nat.le_of_dvd hr hqr
  have hphi := Nat.le_of_dvd (Nat.totient_pos.mpr hr) (Nat.totient_dvd_of_dvd hqr)
  unfold primePowerFaultRecoveryClock
  split_ifs
  · exact Nat.add_le_add (Nat.mul_le_mul_left _ hle) hphi
  · exact Nat.add_le_add (Nat.mul_le_mul_left _ hle) hle

/-- Sharp mixed-fault recovery theorem for every horizon, window, error budget, and erasure budget. -/
theorem horizonObservationFaultRecovery_iff_clock_le (N W e s : ℕ) :
    horizonObservationFaultRecovery N W e s ↔ horizonFaultRecoveryClock N e s ≤ W := by
  rw [horizonObservationFaultRecovery_iff_distance_separation,
    valuationTraceDistance_phase_separation_iff (horizonObservationModulus_pos N)]
  constructor
  · intro h
    apply Finset.sup_le
    intro q hq
    obtain ⟨hqI, hqPrime⟩ := Finset.mem_filter.mp hq
    obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff q).mp hqPrime
    have hd : p ^ a ∣ horizonObservationModulus N :=
      (prime_pow_dvd_horizonObservationModulus_iff hp ha N).mpr (Finset.mem_Icc.mp hqI).2
    have hab := (hp.pow_dvd_iff_le_factorization (horizonObservationModulus_pos N).ne').mp hd
    have hmax := h p hp (by omega)
    have hclock := (primePowerTraceDistanceFloor_gt_iff_clock_le
      (pow_pos hp.pos _) W e s).mp hmax
    exact (recovery_clock_mono_of_dvd (pow_pos hp.pos _) (pow_dvd_pow p hab) e s).trans hclock
  · intro h p hp ha
    apply (primePowerTraceDistanceFloor_gt_iff_clock_le (pow_pos hp.pos _) W e s).mpr
    refine (Finset.le_sup (f := fun q => primePowerFaultRecoveryClock q e s) ?_).trans h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨pow_pos hp.pos _, ?_⟩, hp.isPrimePow.pow (by omega)⟩
    exact (prime_pow_dvd_horizonObservationModulus_iff hp ha N).mp
      (Nat.ordProj_dvd (horizonObservationModulus N) p)

/-- Below the exact clock, two distinct phases admit the same received data within both fault budgets. -/
theorem exists_faulty_horizonObservation_collision_of_lt {N W e s : ℕ}
    (hW : W < horizonFaultRecoveryClock N e s) :
    ∃ (E : Finset (Fin W)), E.card ≤ s ∧ ∃ (z : Fin W → ℕ) (k l : ℕ),
      observationErrorCount E z (fun t => horizonObservationState N (k + (t : ℕ))) ≤ e ∧
      observationErrorCount E z (fun t => horizonObservationState N (l + (t : ℕ))) ≤ e ∧
      horizonObservationPhase N k ≠ horizonObservationPhase N l := by
  have hnot : ¬ horizonObservationFaultRecovery N W e s := by
    rw [horizonObservationFaultRecovery_iff_clock_le]
    omega
  unfold horizonObservationFaultRecovery at hnot
  push Not at hnot
  exact hnot

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
