import GaloisForLFunctions.ArithmeticDefectRigidity.FixedSuccessorsDisappearFromEscapingProfiles
import GaloisForLFunctions.ArithmeticDefectRigidity.ForcingScaleSeparation

/-!
# Energy quantiles retain diffuse receiver escape

Each actual receiver cell contributes at most one unit of pronic energy. The first crossing
of a prescribed fraction of the horizon energy therefore overshoots by at most one. Differences
of crossing energies approximate prescribed fractions with the same absolute error. This
gives energy coordinates whose normalized error vanishes on escape, without assuming that
energy concentrates in a fixed window or a finite collection of packets.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Fractions of a finite receiver's total energy. -/
abbrev EnergyFraction := {r : ℝ // 0 ≤ r ∧ r ≤ 1}

theorem receiverEnergy_zero (ε : ℝ) : dampedMobiusEnergy ε 0 = 0 := by
  simp only [dampedMobiusEnergy, pmPowerDampedDivisorDiscreteEnergy_eq_range, sum_range_zero]

/-- The actual prefix is bounded by the number of its unit-bounded increments. -/
theorem abs_receiver_le_cell (ε : SubcriticalDamping) (n : ℕ) :
    |pmPowerDampedCenteredDivisorPrefix ε n| ≤ (n : ℝ) := by
  simpa only [Nat.zero_add,
    ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
    sub_zero] using abs_receiver_shift_sub_le ε 0 n

/-- One new cell costs at most one unit of actual receiver energy. -/
theorem receiverEnergy_succ_le (ε : SubcriticalDamping) (n : ℕ) :
    dampedMobiusEnergy ε (n + 1) ≤ dampedMobiusEnergy ε n + 1 := by
  have hsq := pow_le_pow_left₀ (abs_nonneg _) (abs_receiver_le_cell ε (n + 1)) 2
  rw [sq_abs] at hsq
  have hcell : pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    push_cast at hsq
    nlinarith
  simp only [dampedMobiusEnergy, pmPowerDampedDivisorDiscreteEnergy_eq_range,
    sum_range_succ]
  exact add_le_add (le_refl _) hcell

/-- A block of `k` newly entering cells costs at most `k` units of energy. -/
theorem receiverEnergy_shift_le (ε : SubcriticalDamping) (n k : ℕ) :
    dampedMobiusEnergy ε (n + k) ≤ dampedMobiusEnergy ε n + (k : ℝ) := by
  induction k with
  | zero => simp only [Nat.add_zero, Nat.cast_zero, add_zero, le_refl]
  | succ k ih =>
    have h := receiverEnergy_succ_le ε (n + k)
    rw [Nat.add_succ, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    linarith

private theorem exists_receiverEnergy_crossing (ε : SubcriticalDamping) (T : ℕ)
    (r : EnergyFraction) : ∃ n, (r : ℝ) * dampedMobiusEnergy ε T ≤ dampedMobiusEnergy ε n := by
  refine ⟨T, ?_⟩
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right r.property.2 (dampedMobiusEnergy_nonneg ε T)

/-- The first source cell crossing a prescribed energy fraction. -/
def receiverEnergyQuantile (ε : SubcriticalDamping) (T : ℕ) (r : EnergyFraction) : ℕ :=
  Nat.find (exists_receiverEnergy_crossing ε T r)

theorem receiverEnergyQuantile_le_horizon (ε : SubcriticalDamping) (T : ℕ)
    (r : EnergyFraction) : receiverEnergyQuantile ε T r ≤ T := by
  apply Nat.find_min'
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right r.property.2 (dampedMobiusEnergy_nonneg ε T)

/-- Every crossing retains its requested energy, with an absolute overshoot at most one. -/
theorem receiverEnergyQuantile_bounds (ε : SubcriticalDamping) (T : ℕ)
    (r : EnergyFraction) :
    (r : ℝ) * dampedMobiusEnergy ε T ≤ dampedMobiusEnergy ε (receiverEnergyQuantile ε T r) ∧
      dampedMobiusEnergy ε (receiverEnergyQuantile ε T r) ≤
        (r : ℝ) * dampedMobiusEnergy ε T + 1 := by
  refine ⟨Nat.find_spec (exists_receiverEnergy_crossing ε T r), ?_⟩
  cases hq : receiverEnergyQuantile ε T r with
  | zero =>
    rw [receiverEnergy_zero]
    exact add_nonneg (mul_nonneg r.property.1 (dampedMobiusEnergy_nonneg ε T)) zero_le_one
  | succ n =>
    have hmin : ¬ (r : ℝ) * dampedMobiusEnergy ε T ≤ dampedMobiusEnergy ε n :=
      Nat.find_min (exists_receiverEnergy_crossing ε T r) (by
        change n < receiverEnergyQuantile ε T r
        omega)
    have hinc := receiverEnergy_succ_le ε n
    have hlt := lt_of_not_ge hmin
    exact hinc.trans (by linarith)

/-- Energy coordinates respect the ordering of the requested fractions. -/
theorem monotone_receiverEnergyQuantile (ε : SubcriticalDamping) (T : ℕ) :
    Monotone (receiverEnergyQuantile ε T) := by
  intro r s hrs
  apply Nat.find_min'
  exact (mul_le_mul_of_nonneg_right hrs (dampedMobiusEnergy_nonneg ε T)).trans
    (receiverEnergyQuantile_bounds ε T s).1

/-- The signed energy of any quantile interval differs from its target by at most one. -/
theorem abs_receiverEnergyQuantile_interval_error_le (ε : SubcriticalDamping) (T : ℕ)
    (r s : EnergyFraction) :
    |(dampedMobiusEnergy ε (receiverEnergyQuantile ε T s) -
        dampedMobiusEnergy ε (receiverEnergyQuantile ε T r)) -
      ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε T| ≤ 1 := by
  obtain ⟨hr0, hr1⟩ := receiverEnergyQuantile_bounds ε T r
  obtain ⟨hs0, hs1⟩ := receiverEnergyQuantile_bounds ε T s
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- At a positive horizon the relative quantile error is at most the reciprocal total energy. -/
theorem abs_normalized_receiverEnergyQuantile_error_le (ε : SubcriticalDamping) (T : ℕ)
    (r s : EnergyFraction) :
    |(dampedMobiusEnergy ε (receiverEnergyQuantile ε (T + 1) s) -
        dampedMobiusEnergy ε (receiverEnergyQuantile ε (T + 1) r)) /
        dampedMobiusEnergy ε (T + 1) - ((s : ℝ) - (r : ℝ))| ≤
      1 / dampedMobiusEnergy ε (T + 1) := by
  have hE := receiverEnergy_succ_pos ε T
  have heq : (dampedMobiusEnergy ε (receiverEnergyQuantile ε (T + 1) s) -
        dampedMobiusEnergy ε (receiverEnergyQuantile ε (T + 1) r)) /
        dampedMobiusEnergy ε (T + 1) - ((s : ℝ) - (r : ℝ)) =
      ((dampedMobiusEnergy ε (receiverEnergyQuantile ε (T + 1) s) -
        dampedMobiusEnergy ε (receiverEnergyQuantile ε (T + 1) r)) -
        ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε (T + 1)) /
        dampedMobiusEnergy ε (T + 1) := by field_simp [hE.ne']; ring
  rw [heq, abs_div, abs_of_pos hE]
  exact div_le_div_of_nonneg_right (abs_receiverEnergyQuantile_interval_error_le ε (T + 1) r s) hE.le

/-- On escape every fixed quantile interval retains exactly its prescribed fraction of energy. -/
theorem admits_or_quantile_interval_error_vanishes (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ r s : EnergyFraction,
      Tendsto (fun T => |(dampedMobiusEnergy ε (receiverEnergyQuantile ε (T + 1) s) -
          dampedMobiusEnergy ε (receiverEnergyQuantile ε (T + 1) r)) /
          dampedMobiusEnergy ε (T + 1) - ((s : ℝ) - (r : ℝ))|) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun r s => squeeze_zero (fun T => abs_nonneg _)
      (fun T => abs_normalized_receiverEnergyQuantile_error_le ε T r s) ?_
    exact tendsto_const_nhds.div_atTop (hE.comp (tendsto_add_atTop_nat 1))

end GaloisForLFunctions.ArithmeticDefectRigidity
