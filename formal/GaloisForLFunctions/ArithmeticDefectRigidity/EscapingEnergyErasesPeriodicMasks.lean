import GaloisForLFunctions.ArithmeticDefectRigidity.FixedSuccessorsDisappearFromEscapingProfiles
import GaloisForLFunctions.ArithmeticDefectRigidity.ForcingScaleSeparation
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations

/-!+# Periodic masks of the actual receiver energy

The centered divisor prefix has unit-bounded increments and grows at most linearly.
Its pronic energy density therefore has total variation bounded by four times the
square root of its total energy, plus one. Summation by parts makes every bounded
primitive invisible after normalization by escaping receiver energy.

The residue discrepancy is uniform even for horizon-dependent moduli. A fixed
residue projection leaves exactly its Bernoulli variance outside the receiver line.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The energy of the positive cell `n + 1`. -/
def receiverEnergyCell (ε : ℝ) (n : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ 2 /
    (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem receiverEnergyCell_nonneg (ε : ℝ) (n : ℕ) :
    0 ≤ receiverEnergyCell ε n := by
  unfold receiverEnergyCell
  positivity

theorem sum_receiverEnergyCell (ε : ℝ) (T : ℕ) :
    ∑ n ∈ range T, receiverEnergyCell ε n = dampedMobiusEnergy ε T := by
  rw [dampedMobiusEnergy, pmPowerDampedDivisorDiscreteEnergy_eq_range]
  rfl

private theorem abs_receiver_le_nat (ε : SubcriticalDamping) (n : ℕ) :
    |pmPowerDampedCenteredDivisorPrefix ε n| ≤ (n : ℝ) := by
  simpa only [Nat.zero_add,
    ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
    sub_zero] using abs_receiver_shift_sub_le ε 0 n

theorem receiverEnergyCell_le_one (ε : SubcriticalDamping) (n : ℕ) :
    receiverEnergyCell ε n ≤ 1 := by
  have ha := abs_receiver_le_nat ε (n + 1)
  push_cast at ha
  have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
  rw [sq_abs] at hs
  unfold receiverEnergyCell
  apply (div_le_one (by positivity)).mpr
  nlinarith only [hs, Nat.cast_nonneg (α := ℝ) n]

private theorem abs_pronic_step_le {a b x : ℝ} (hx : 0 < x)
    (ha : |a| ≤ x) (hd : |b - a| ≤ 1) :
    |b ^ 2 / ((x + 1) * (x + 2)) - a ^ 2 / (x * (x + 1))| ≤
      (4 * |a| + 1) / (x * (x + 1)) := by
  have hx1 : 0 < x + 1 := by linarith only [hx]
  have hx2 : 0 < x + 2 := by linarith only [hx]
  have hdif : |b ^ 2 - a ^ 2| ≤ 2 * |a| + 1 := by
    rw [show b ^ 2 - a ^ 2 = (b - a) * (b + a) by ring, abs_mul]
    have hsum : |b + a| ≤ 2 * |a| + 1 := by
      calc |b + a| = |(b - a) + (a + a)| := by congr 1; ring
        _ ≤ |b - a| + (|a| + |a|) := (abs_add_le _ _).trans
          (add_le_add le_rfl (abs_add_le a a))
        _ ≤ 2 * |a| + 1 := by linarith only [hd]
    exact (mul_le_mul hd hsum (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have ha2 : a ^ 2 ≤ |a| * (x + 2) := by
    calc a ^ 2 = |a| * |a| := by rw [← pow_two, sq_abs]
      _ ≤ |a| * (x + 2) := mul_le_mul_of_nonneg_left
        (by linarith only [ha]) (abs_nonneg a)
  have heq : b ^ 2 / ((x + 1) * (x + 2)) - a ^ 2 / (x * (x + 1)) =
      (b ^ 2 - a ^ 2) / ((x + 1) * (x + 2)) -
        2 * a ^ 2 / (x * (x + 1) * (x + 2)) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(b ^ 2 - a ^ 2) / ((x + 1) * (x + 2))| +
        |2 * a ^ 2 / (x * (x + 1) * (x + 2))| := by
      rw [sub_eq_add_neg]
      exact (_root_.abs_add_le _ _).trans (by rw [_root_.abs_neg])
    _ = |b ^ 2 - a ^ 2| / ((x + 1) * (x + 2)) +
        2 * a ^ 2 / (x * (x + 1) * (x + 2)) := by
      rw [abs_div, abs_of_pos (mul_pos hx1 hx2),
        abs_of_nonneg (show 0 ≤ 2 * a ^ 2 / (x * (x + 1) * (x + 2)) by positivity)]
    _ ≤ (2 * |a| + 1) / ((x + 1) * (x + 2)) +
        2 * (|a| * (x + 2)) / (x * (x + 1) * (x + 2)) :=
      add_le_add (div_le_div_of_nonneg_right hdif (by positivity))
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha2 (by norm_num))
          (by positivity))
    _ ≤ (2 * |a| + 1) / (x * (x + 1)) +
        2 * (|a| * (x + 2)) / (x * (x + 1) * (x + 2)) := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_left (by positivity) (mul_pos hx hx1)
      nlinarith only [hx]
    _ = (4 * |a| + 1) / (x * (x + 1)) := by
      field_simp
      ring

/-- Unit arithmetic increments control the variation of each energy cell. -/
theorem abs_receiverEnergyCell_succ_sub_le (ε : SubcriticalDamping) (n : ℕ) :
    |receiverEnergyCell ε (n + 1) - receiverEnergyCell ε n| ≤
      (4 * |pmPowerDampedCenteredDivisorPrefix ε (n + 1)| + 1) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have ha := abs_receiver_le_nat ε (n + 1)
  have hd := abs_receiver_shift_sub_le ε (n + 1) 1
  push_cast at ha hd
  have h := abs_pronic_step_le (by positivity : 0 < (n : ℝ) + 1) ha hd
  simpa only [receiverEnergyCell, Nat.cast_add, Nat.cast_one, add_assoc,
    show (1 : ℝ) + 1 = 2 by norm_num] using h

private theorem sum_shift_eq_Icc (f : ℕ → ℝ) (T : ℕ) :
    ∑ n ∈ range T, f (n + 1) = ∑ n ∈ Icc 1 T, f n := by
  induction T with
  | zero => simp only [range_zero, sum_empty, Icc_eq_empty_of_lt (by omega : 0 < 1)]
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

private theorem receiver_weighted_abs_sum_le (ε : SubcriticalDamping) (T : ℕ) :
    ∑ n ∈ Icc 1 T, |pmPowerDampedCenteredDivisorPrefix ε n| /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤ Real.sqrt (dampedMobiusEnergy ε T) := by
  have h := sum_mul_div_le_pronicNorm T
    (fun n => |pmPowerDampedCenteredDivisorPrefix ε n|) (fun _ => 1)
  have habs : pronicNorm T (fun n => |pmPowerDampedCenteredDivisorPrefix ε n|) =
      pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) := by
    simp only [pronicNorm, sq_abs]
  simp only [mul_one] at h
  rw [habs, pronicNorm_centeredPrefix] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (pronicNorm_one_le T)
    (Real.sqrt_nonneg _)).trans_eq (mul_one _))

/-- The total variation of the energy density costs only its square-root energy. -/
theorem sum_abs_receiverEnergyCell_diff_le (ε : SubcriticalDamping) (T : ℕ) :
    ∑ n ∈ range T, |receiverEnergyCell ε (n + 1) - receiverEnergyCell ε n| ≤
      4 * Real.sqrt (dampedMobiusEnergy ε T) + 1 := by
  have hone : (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ (1 : ℝ) := by
    have h := pow_le_pow_left₀ (pronicNorm_nonneg T (fun _ => 1)) (pronicNorm_one_le T) 2
    simpa only [pronicNorm_sq, one_pow] using h
  calc
    _ ≤ ∑ n ∈ range T,
        (4 * |pmPowerDampedCenteredDivisorPrefix ε (n + 1)| + 1) /
          (((n : ℝ) + 1) * ((n : ℝ) + 2)) :=
      sum_le_sum fun n _ => abs_receiverEnergyCell_succ_sub_le ε n
    _ = ∑ n ∈ Icc 1 T,
        (4 * |pmPowerDampedCenteredDivisorPrefix ε n| + 1) /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
        show (1 : ℝ) + 1 = 2 by norm_num] using
        sum_shift_eq_Icc (fun n => (4 * |pmPowerDampedCenteredDivisorPrefix ε n| + 1) /
          ((n : ℝ) * ((n : ℝ) + 1))) T
    _ = 4 * (∑ n ∈ Icc 1 T, |pmPowerDampedCenteredDivisorPrefix ε n| /
          ((n : ℝ) * ((n : ℝ) + 1))) +
        ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ 4 * Real.sqrt (dampedMobiusEnergy ε T) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (receiver_weighted_abs_sum_le ε T)
        (by norm_num)) hone

private theorem abs_receiverEnergy_weighted_sum_le (ε : SubcriticalDamping)
    (g : ℕ → ℝ) {B : ℝ} (hB : ∀ k, |∑ n ∈ range k, g n| ≤ B) (T : ℕ) :
    |∑ n ∈ range T, receiverEnergyCell ε n * g n| ≤
      B * (4 * Real.sqrt (dampedMobiusEnergy ε T) + 2) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h := sum_range_by_parts (receiverEnergyCell ε) g T
  simp only [smul_eq_mul] at h
  rw [h]
  have htail : ∑ n ∈ range (T - 1),
      |receiverEnergyCell ε (n + 1) - receiverEnergyCell ε n| ≤
      4 * Real.sqrt (dampedMobiusEnergy ε T) + 1 := by
    exact (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le T 1))
      (fun n _ _ => abs_nonneg _)).trans (sum_abs_receiverEnergyCell_diff_le ε T)
  calc
    _ ≤ |receiverEnergyCell ε (T - 1) * ∑ n ∈ range T, g n| +
        |∑ n ∈ range (T - 1), (receiverEnergyCell ε (n + 1) - receiverEnergyCell ε n) *
          ∑ j ∈ range (n + 1), g j| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (receiverEnergyCell ε (T - 1) * ∑ n ∈ range T, g n)
        (∑ n ∈ range (T - 1), (receiverEnergyCell ε (n + 1) - receiverEnergyCell ε n) *
          ∑ j ∈ range (n + 1), g j)
    _ ≤ B + (∑ n ∈ range (T - 1),
        |receiverEnergyCell ε (n + 1) - receiverEnergyCell ε n|) * B := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (receiverEnergyCell_nonneg ε _)]
        exact (mul_le_mul (receiverEnergyCell_le_one ε _) (hB T)
          (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
      · rw [sum_mul]
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _))
    _ ≤ B + (4 * Real.sqrt (dampedMobiusEnergy ε T) + 1) * B :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right htail hB0)
    _ = B * (4 * Real.sqrt (dampedMobiusEnergy ε T) + 2) := by ring

/-- Energy in one residue class, with the same horizon as the total receiver energy. -/
def receiverResidueEnergy (ε : ℝ) (q : ℕ+) (r : Fin (q : ℕ)) (T : ℕ) : ℝ :=
  ∑ n ∈ range T, if (n + 1) % (q : ℕ) = r then receiverEnergyCell ε n else 0

private def centeredResidueMask (q : ℕ+) (r : Fin (q : ℕ)) (n : ℕ) : ℝ :=
  (if n % (q : ℕ) = r then 1 else 0) - 1 / (q : ℝ)

private theorem centeredResidueMask_periodic (q : ℕ+) (r : Fin (q : ℕ)) :
    Function.Periodic (centeredResidueMask q r) (q : ℕ) := by
  intro n
  simp only [centeredResidueMask, Nat.add_mod_right]

private theorem residueMask_sum_period (q : ℕ+) (r : Fin (q : ℕ)) :
    (∑ n ∈ range (q : ℕ), (if n % (q : ℕ) = r then (1 : ℝ) else 0)) = 1 := by
  calc
    _ = ∑ n ∈ range (q : ℕ), (if n = r then (1 : ℝ) else 0) :=
      sum_congr rfl fun n hn => by rw [Nat.mod_eq_of_lt (mem_range.mp hn)]
    _ = 1 := by simp only [Finset.sum_ite_eq', mem_range, r.isLt, if_true]

private theorem centeredResidueMask_sum_period (q : ℕ+) (r : Fin (q : ℕ)) :
    ∑ n ∈ range (q : ℕ), centeredResidueMask q r n = 0 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast q.property.ne'
  simp only [centeredResidueMask, sum_sub_distrib, residueMask_sum_period,
    sum_const, card_range, nsmul_eq_mul]
  rw [mul_one_div_cancel hq, sub_self]

private theorem centeredResidueMask_abs_sum_period_le (q : ℕ+) (r : Fin (q : ℕ)) :
    ∑ n ∈ range (q : ℕ), |centeredResidueMask q r n| ≤ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast q.property.ne'
  calc
    _ ≤ ∑ n ∈ range (q : ℕ),
        ((if n % (q : ℕ) = r then (1 : ℝ) else 0) + 1 / (q : ℝ)) := by
      apply sum_le_sum
      intro n _
      unfold centeredResidueMask
      have h := norm_sub_le (if n % (q : ℕ) = r then (1 : ℝ) else 0) (1 / (q : ℝ))
      simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤
        (if n % (q : ℕ) = r then 1 else 0) by split_ifs <;> norm_num),
        abs_of_nonneg (show 0 ≤ 1 / (q : ℝ) by positivity)] using h
    _ = 2 := by
      rw [sum_add_distrib, residueMask_sum_period]
      simp only [sum_const, card_range, nsmul_eq_mul]
      rw [mul_one_div_cancel hq]
      norm_num

private theorem centeredResidueMask_partial_sum_le (q : ℕ+) (r : Fin (q : ℕ)) (T : ℕ) :
    |∑ n ∈ range T, centeredResidueMask q r (n + 1)| ≤ 2 := by
  have hp := centeredResidueMask_periodic q r
  have hshift : ∀ n, centeredResidueMask q r (n + (q : ℕ) + 1) =
      centeredResidueMask q r (n + 1) := fun n => by
    rw [show n + (q : ℕ) + 1 = (n + 1) + (q : ℕ) by omega, hp]
  have hzero : ∑ n ∈ range (q : ℕ), centeredResidueMask q r (n + 1) = 0 := by
    have h := RenormalizedBiarithmeticGeometry.sum_range_shift_of_periodic hp 1
    rw [centeredResidueMask_sum_period] at h
    simpa only [Nat.add_comm] using h
  have h := RenormalizedBiarithmeticGeometry.abs_sum_range_le_of_periodic
    q.property hshift hzero T
  have habs := RenormalizedBiarithmeticGeometry.sum_range_shift_of_periodic
    (p := fun n => |centeredResidueMask q r n|) (q := (q : ℕ))
    (fun n => congrArg abs (hp n)) 1
  have habs' : ∑ n ∈ range (q : ℕ), |centeredResidueMask q r (n + 1)| =
      ∑ n ∈ range (q : ℕ), |centeredResidueMask q r n| := by
    simpa only [Nat.add_comm] using habs
  exact h.trans (habs'.trans_le (centeredResidueMask_abs_sum_period_le q r))

/-- The residue discrepancy is bounded uniformly in both modulus and residue. -/
theorem abs_receiverResidueEnergy_sub_mean_le (ε : SubcriticalDamping)
    (q : ℕ+) (r : Fin (q : ℕ)) (T : ℕ) :
    |receiverResidueEnergy ε q r T - dampedMobiusEnergy ε T / (q : ℝ)| ≤
      8 * Real.sqrt (dampedMobiusEnergy ε T) + 4 := by
  have heq : receiverResidueEnergy ε q r T - dampedMobiusEnergy ε T / (q : ℝ) =
      ∑ n ∈ range T, receiverEnergyCell ε n * centeredResidueMask q r (n + 1) := by
    rw [receiverResidueEnergy, ← sum_receiverEnergyCell, sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    unfold centeredResidueMask
    split_ifs <;> ring
  rw [heq]
  have h := abs_receiverEnergy_weighted_sum_le ε
    (fun n => centeredResidueMask q r (n + 1)) (centeredResidueMask_partial_sum_le q r) T
  convert h using 1; ring

/-- Squared distance from a residue-masked receiver to a scalar multiple of the receiver. -/
def receiverResidueProjectionError (ε : ℝ) (q : ℕ+) (r : Fin (q : ℕ))
    (T : ℕ) (c : ℝ) : ℝ :=
  ∑ n ∈ range T, ((if (n + 1) % (q : ℕ) = r then (1 : ℝ) else 0) - c) ^ 2 *
    receiverEnergyCell ε n

/-- The projection error is an exact quadratic in the scalar coefficient. -/
theorem receiverResidueProjectionError_eq (ε : ℝ) (q : ℕ+) (r : Fin (q : ℕ))
    (T : ℕ) (c : ℝ) :
    receiverResidueProjectionError ε q r T c =
      c ^ 2 * dampedMobiusEnergy ε T + (1 - 2 * c) * receiverResidueEnergy ε q r T := by
  rw [receiverResidueProjectionError, ← sum_receiverEnergyCell, receiverResidueEnergy,
    mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by split_ifs <;> ring

/-- Orthogonal projection onto the receiver line leaves the Bernoulli variance of its
normalized residue mass. -/
theorem normalized_receiverResidueProjectionError_eq (ε : ℝ) (q : ℕ+)
    (r : Fin (q : ℕ)) (T : ℕ) :
    receiverResidueProjectionError ε q r T
        (receiverResidueEnergy ε q r T / dampedMobiusEnergy ε T) / dampedMobiusEnergy ε T =
      receiverResidueEnergy ε q r T / dampedMobiusEnergy ε T -
        (receiverResidueEnergy ε q r T / dampedMobiusEnergy ε T) ^ 2 := by
  rw [receiverResidueProjectionError_eq]
  by_cases hE : dampedMobiusEnergy ε T = 0
  · simp only [hE, div_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero]
  · field_simp
    ring

/-- The normalized residue mass gives the exact minimizing scalar coefficient. -/
theorem receiverResidueProjectionError_min (ε : SubcriticalDamping) (q : ℕ+)
    (r : Fin (q : ℕ)) (T : ℕ) (c : ℝ) :
    receiverResidueProjectionError ε q r (T + 1)
        (receiverResidueEnergy ε q r (T + 1) / dampedMobiusEnergy ε (T + 1)) ≤
      receiverResidueProjectionError ε q r (T + 1) c := by
  have he := receiverEnergy_succ_pos ε T
  have heq : receiverResidueProjectionError ε q r (T + 1) c -
      receiverResidueProjectionError ε q r (T + 1)
        (receiverResidueEnergy ε q r (T + 1) / dampedMobiusEnergy ε (T + 1)) =
      (c - receiverResidueEnergy ε q r (T + 1) / dampedMobiusEnergy ε (T + 1)) ^ 2 *
        dampedMobiusEnergy ε (T + 1) := by
    rw [receiverResidueProjectionError_eq, receiverResidueProjectionError_eq]
    field_simp
    ring
  have hnonneg := mul_nonneg
    (sq_nonneg (c - receiverResidueEnergy ε q r (T + 1) / dampedMobiusEnergy ε (T + 1))) he.le
  rw [← heq] at hnonneg
  exact sub_nonneg.mp hnonneg

private theorem tendsto_residue_budget_div_energy (ε : SubcriticalDamping)
    (hE : Tendsto (dampedMobiusEnergy (ε : ℝ)) atTop atTop) :
    Tendsto (fun T => (8 * Real.sqrt (dampedMobiusEnergy ε (T + 1)) + 4) /
      dampedMobiusEnergy ε (T + 1)) atTop (𝓝 0) := by
  have hE' := hE.comp (tendsto_add_atTop_nat 1)
  have hroot := Real.tendsto_sqrt_atTop.comp hE'
  have h1 : Tendsto (fun T => (8 : ℝ) / Real.sqrt (dampedMobiusEnergy ε (T + 1)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hroot
  have h2 : Tendsto (fun T => (4 : ℝ) / dampedMobiusEnergy ε (T + 1))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hE'
  have heq (T : ℕ) : (8 * Real.sqrt (dampedMobiusEnergy ε (T + 1)) + 4) /
      dampedMobiusEnergy ε (T + 1) =
      8 / Real.sqrt (dampedMobiusEnergy ε (T + 1)) +
        4 / dampedMobiusEnergy ε (T + 1) := by
    have he := receiverEnergy_succ_pos ε T
    have hs := Real.sqrt_pos.mpr he
    have hsq := Real.sq_sqrt he.le
    field_simp
    nlinarith only [hsq]
  simp_rw [heq]
  simpa only [add_zero] using h1.add h2

/-- On escape, even a horizon-dependent residue class has its uniform energy share,
up to an error tending to zero. Neither the modulus nor the residue must be fixed. -/
theorem admits_or_moving_residue_energies_equidistribute (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ (q : ℕ → ℕ+) (r : (T : ℕ) → Fin (q T : ℕ)),
      Tendsto (fun T => receiverResidueEnergy ε (q T) (r T) (T + 1) /
        dampedMobiusEnergy ε (T + 1) - 1 / (q T : ℝ)) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun q r => (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    refine squeeze_zero (fun T => abs_nonneg _) ?_
      (tendsto_residue_budget_div_energy ε hE)
    intro T
    have he := receiverEnergy_succ_pos ε T
    have heq : receiverResidueEnergy ε (q T) (r T) (T + 1) /
        dampedMobiusEnergy ε (T + 1) - 1 / (q T : ℝ) =
        (receiverResidueEnergy ε (q T) (r T) (T + 1) -
          dampedMobiusEnergy ε (T + 1) / (q T : ℝ)) /
          dampedMobiusEnergy ε (T + 1) := by
      field_simp
    dsimp only [Function.comp_apply]
    rw [heq, abs_div, abs_of_pos he]
    exact div_le_div_of_nonneg_right
      (abs_receiverResidueEnergy_sub_mean_le ε (q T) (r T) (T + 1)) he.le

/-- A fixed residue projection loses exactly `q⁻¹(1-q⁻¹)` of unit energy outside the
receiver line on escape. For `q > 1`, residue projection does not preserve that line. -/
theorem admits_or_residue_projection_leakage (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ (q : ℕ+) (r : Fin (q : ℕ)),
      Tendsto (fun T => receiverResidueProjectionError ε q r (T + 1)
          (receiverResidueEnergy ε q r (T + 1) / dampedMobiusEnergy ε (T + 1)) /
          dampedMobiusEnergy ε (T + 1))
        atTop (𝓝 ((1 / (q : ℝ)) * (1 - 1 / (q : ℝ)))) := by
  rcases admits_or_moving_residue_energies_equidistribute ε with h | h
  · exact Or.inl h
  · refine Or.inr fun q r => ?_
    have hR : Tendsto (fun T => receiverResidueEnergy ε q r (T + 1) /
        dampedMobiusEnergy ε (T + 1)) atTop (𝓝 (1 / (q : ℝ))) := by
      have h' := (h (fun _ => q) (fun _ => r)).add_const (1 / (q : ℝ))
      simpa only [sub_add_cancel, zero_add] using h'
    simp_rw [normalized_receiverResidueProjectionError_eq]
    rw [show (1 / (q : ℝ)) * (1 - 1 / (q : ℝ)) =
      1 / (q : ℝ) - (1 / (q : ℝ)) ^ 2 by ring]
    simpa only [pow_two] using hR.sub (hR.mul hR)

end GaloisForLFunctions.ArithmeticDefectRigidity
