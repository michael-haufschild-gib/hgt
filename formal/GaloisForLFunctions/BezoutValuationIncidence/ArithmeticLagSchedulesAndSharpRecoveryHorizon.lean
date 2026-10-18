import GaloisForLFunctions.BezoutValuationIncidence.TrueTranslationPredictionAndExactCompression

/-!
# Exact arithmetic recovery schedules

Literal shifted observations recover precisely the modes whose visibility
clocks divide a chosen lag. Every uncovered mode has an explicit nonzero
invisible signal. This classifies arbitrary finite schedules, their sharp
consecutive horizon, and the modulus of all successful single observation times.
The same pure modes exhibit one-step erasure followed by true-shift recovery.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- An actual divisor weight carrying one unit Selberg mode, if that mode is active. -/
def sieveModeWeight (N q : ℕ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff (fun r => if r = q then 1 else 0) N

/-- A literal single-mode probe reads the exact lag coefficient times the source coordinate. -/
theorem sieveLagPair_mode_probe (N h q : ℕ) (c : ℕ → ℝ) :
    sieveLagPair N h (sieveModeWeight N q) c =
      if q ∈ Icc 1 N then ramanujanLagCoefficient q h * selbergMultiplesCoord N c q else 0 := by
  classical
  rw [sieveLagPair_eq_ramanujan_diagonal]
  calc
    _ = ∑ r ∈ Icc 1 N, if r = q then
        ramanujanLagCoefficient r h * selbergMultiplesCoord N c r else 0 := by
      apply sum_congr rfl
      intro r hr
      rw [sieveModeWeight, selbergMultiplesCoord_ramanujan_inverse, if_pos hr]
      split_ifs <;> simp
    _ = _ := by simp

/-- Equality of all literal divisor-probe observations at the selected integer lags. -/
def SieveLagObservationsEqual (N : ℕ) (H : Finset ℕ) (c b : ℕ → ℝ) : Prop :=
  ∀ h ∈ H, ∀ a : ℕ → ℝ, sieveLagPair N h a c = sieveLagPair N h a b

/-- Exact information retained by an arbitrary finite schedule of true shifts. -/
theorem sieveLagObservationsEqual_iff (N : ℕ) (H : Finset ℕ) (c b : ℕ → ℝ) :
    SieveLagObservationsEqual N H c b ↔
      ∀ q ∈ Icc 1 N, (∃ h ∈ H, lagVisibilityClock q ∣ h) →
        selbergMultiplesCoord N c q = selbergMultiplesCoord N b q := by
  constructor
  · intro he q hq hv
    obtain ⟨h, hh, hD⟩ := hv
    have hp := he h hh (sieveModeWeight N q)
    rw [sieveLagPair_mode_probe, sieveLagPair_mode_probe, if_pos hq, if_pos hq] at hp
    have hq0 : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
    exact mul_left_cancel₀ ((ramanujanLagCoefficient_ne_zero_iff q h).mpr ⟨hq0, hD⟩) hp
  · intro he h hh a
    rw [sieveLagPair_eq_ramanujan_diagonal, sieveLagPair_eq_ramanujan_diagonal]
    apply sum_congr rfl
    intro q hq
    by_cases hv : lagVisibilityClock q ∣ h
    · rw [he q hq ⟨h, hh, hv⟩]
    · have hz : ramanujanLagCoefficient q h = 0 := by
        by_contra hn
        exact hv ((ramanujanLagCoefficient_ne_zero_iff q h).mp hn).2
      simp [hz]

/-- The optimal predictors and the literal observations retain exactly the same information. -/
theorem sieveLagObservationsEqual_iff_predictors (N : ℕ) (H : Finset ℕ) (c b : ℕ → ℝ) :
    SieveLagObservationsEqual N H c b ↔
      ∀ h ∈ H, ∀ d ∈ Icc 1 N,
        sieveTranslationPredictor N h c d = sieveTranslationPredictor N h b d := by
  rw [sieveLagObservationsEqual_iff]
  constructor
  · intro he h hh
    apply (sieve_active_coefficients_eq_iff N _ _).mpr
    intro q hq
    rw [selbergMultiplesCoord_translationPredictor, selbergMultiplesCoord_translationPredictor,
      if_pos hq, if_pos hq]
    by_cases hv : sieveLagMultiplier q h = 0
    · simp [hv]
    · rw [he q hq ⟨h, hh, ((sieveLagMultiplier_ne_zero_iff q h).mp hv).2⟩]
  · intro he q hq hv
    obtain ⟨h, hh, hD⟩ := hv
    have hp := (sieve_active_coefficients_eq_iff N _ _).mp (he h hh) q hq
    rw [selbergMultiplesCoord_translationPredictor, selbergMultiplesCoord_translationPredictor,
      if_pos hq, if_pos hq] at hp
    have hq0 : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
    exact mul_left_cancel₀ ((sieveLagMultiplier_ne_zero_iff q h).mpr ⟨hq0, hD⟩) hp

/-- A schedule recovers all active arithmetic coefficients of every real signal. -/
def SieveLagScheduleRecovers (N : ℕ) (H : Finset ℕ) : Prop :=
  ∀ c b : ℕ → ℝ, SieveLagObservationsEqual N H c b → ∀ d ∈ Icc 1 N, c d = b d

/-- Complete classification of recovering schedules, with no restriction on the chosen lags. -/
theorem sieveLagScheduleRecovers_iff (N : ℕ) (H : Finset ℕ) :
    SieveLagScheduleRecovers N H ↔
      ∀ q ∈ Icc 1 N, ∃ h ∈ H, lagVisibilityClock q ∣ h := by
  constructor
  · intro hr q hq
    by_contra hmiss
    have he : SieveLagObservationsEqual N H (sieveModeWeight N q) (fun _ => 0) := by
      apply (sieveLagObservationsEqual_iff N H _ _).mpr
      intro r hr hv
      have hrq : r ≠ q := by
        intro heq
        subst r
        exact hmiss hv
      rw [sieveModeWeight, selbergMultiplesCoord_ramanujan_inverse, if_pos hr, if_neg hrq]
      simp [selbergMultiplesCoord]
    have hz := (sieve_active_coefficients_eq_iff N _ _).mp (hr _ _ he) q hq
    rw [sieveModeWeight, selbergMultiplesCoord_ramanujan_inverse, if_pos hq] at hz
    simp [selbergMultiplesCoord] at hz
  · intro hc c b he
    apply (sieve_active_coefficients_eq_iff N c b).mpr
    intro q hq
    exact (sieveLagObservationsEqual_iff N H c b).mp he q hq (hc q hq)

/-- The sharp number of consecutive positive lags required for complete recovery. -/
def sieveLagRecoveryHorizon (N : ℕ) : ℕ := (Icc 1 N).sup lagVisibilityClock

/-- Consecutive positive observations recover every signal exactly from this horizon onward. -/
theorem sieveLagScheduleRecovers_initial_iff (N T : ℕ) :
    SieveLagScheduleRecovers N (Icc 1 T) ↔ sieveLagRecoveryHorizon N ≤ T := by
  rw [sieveLagScheduleRecovers_iff, sieveLagRecoveryHorizon, Finset.sup_le_iff]
  apply forall_congr'
  intro q
  apply forall_congr'
  intro hq
  have hq0 : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
  have hD : 0 < lagVisibilityClock q := Nat.pos_of_ne_zero
    (fun hz => hq0 ((lagVisibilityClock_eq_zero_iff q).mp hz))
  constructor
  · rintro ⟨h, hh, hd⟩
    exact (Nat.le_of_dvd (mem_Icc.mp hh).1 hd).trans (mem_Icc.mp hh).2
  · intro hT
    exact ⟨lagVisibilityClock q, mem_Icc.mpr ⟨hD, hT⟩, dvd_rfl⟩

/-- Every successful single observation time is a multiple of this arithmetic modulus. -/
def sieveLagRecoveryModulus (N : ℕ) : ℕ := (Icc 1 N).lcm lagVisibilityClock

/-- Exact set of single-lag recovery times, including lag zero. -/
theorem sieveLagScheduleRecovers_singleton_iff (N h : ℕ) :
    SieveLagScheduleRecovers N {h} ↔ sieveLagRecoveryModulus N ∣ h := by
  rw [sieveLagScheduleRecovers_iff, sieveLagRecoveryModulus, Finset.lcm_dvd_iff]
  simp

/-- A pure mode is visible in actual translated data at precisely its arithmetic recovery times. -/
theorem sieveModeWeight_true_shift_visible_iff (N q h : ℕ) :
    (∃ a : ℕ → ℝ, sieveLagPair N h a (sieveModeWeight N q) ≠ 0) ↔
      q ∈ Icc 1 N ∧ lagVisibilityClock q ∣ h := by
  have hpair (a : ℕ → ℝ) : sieveLagPair N h a (sieveModeWeight N q) =
      if q ∈ Icc 1 N then ramanujanLagCoefficient q h * selbergMultiplesCoord N a q else 0 := by
    rw [← sieveLagPair_mode_probe N h q a]
    rw [sieveLagPair_eq_ramanujan_diagonal, sieveLagPair_eq_ramanujan_diagonal]
    apply sum_congr rfl
    intro r _
    ring
  constructor
  · rintro ⟨a, ha⟩
    rw [hpair] at ha
    split_ifs at ha with hq
    · exact ⟨hq, ((ramanujanLagCoefficient_ne_zero_iff q h).mp
        ((mul_ne_zero_iff.mp ha).1)).2⟩
    · exact (ha rfl).elim
  · rintro ⟨hq, hD⟩
    refine ⟨sieveModeWeight N q, ?_⟩
    rw [hpair, if_pos hq]
    simpa [sieveModeWeight, selbergMultiplesCoord_ramanujan_inverse, hq] using
      (ramanujanLagCoefficient_ne_zero_iff q h).mpr
      ⟨by have := (mem_Icc.mp hq).1; omega, hD⟩

/-- One-step prediction erases exactly the inactive or nonsquarefree pure modes. -/
theorem sieveModeWeight_successor_erased_iff (N q : ℕ) :
    sieveSuccessorPredictor N (sieveModeWeight N q) = (fun _ => 0) ↔
      q ∉ Icc 1 N ∨ ¬Squarefree q := by
  have hz : sieveSuccessorPredictor N (fun _ => 0) = (fun _ => 0) := by
    funext d
    simp [sieveSuccessorPredictor]
  rw [← hz, sieveSuccessorPredictor_eq_iff]
  constructor
  · intro he
    by_cases hq : q ∈ Icc 1 N
    · right
      intro hs
      have hc := he q hq hs
      rw [sieveModeWeight, selbergMultiplesCoord_ramanujan_inverse, if_pos hq] at hc
      simp [selbergMultiplesCoord] at hc
    · exact Or.inl hq
  · intro he r hr hs
    have hrq : r ≠ q := by
      intro h
      subst r
      rcases he with he | he
      · exact he hr
      · exact he hs
    rw [sieveModeWeight, selbergMultiplesCoord_ramanujan_inverse, if_pos hr, if_neg hrq]
    simp [selbergMultiplesCoord]

/-- Once a pure mode is erased, every positive iterate remains zero; true shifts obey a different law. -/
theorem sieveModeWeight_iterated_successor_erased_iff (N q : ℕ) :
    (∀ r : ℕ, (sieveSuccessorPredictor N)^[r + 1] (sieveModeWeight N q) = (fun _ => 0)) ↔
      q ∉ Icc 1 N ∨ ¬Squarefree q := by
  rw [← sieveModeWeight_successor_erased_iff N q]
  constructor
  · intro he
    simpa using he 0
  · intro he r
    have hz : sieveSuccessorPredictor N (fun _ => 0) = (fun _ => 0) := by
      funext d
      simp [sieveSuccessorPredictor]
    have hi : ∀ m : ℕ, (sieveSuccessorPredictor N)^[m] (fun _ => 0) = (fun _ => 0) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply, hz, ih]
    rw [Function.iterate_succ_apply, he, hi]

end
end GaloisForLFunctions.BezoutValuationIncidence
