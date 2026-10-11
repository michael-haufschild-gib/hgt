import GaloisForLFunctions.RHTower.WeilLogShiftCenteredCharacteristic
import GaloisForLFunctions.RHTower.WeilLogShiftFluctuationResidual

/-! The full joint phase law is Gaussian on the common index/correction fluctuation direction. -/

open scoped BigOperators
open Filter Topology

noncomputable section
namespace RHTower

def finiteWeilCanonicalFluctuationResidualValue (r k : ℕ) (i : Fin (r + 1)) : ℝ :=
  ((r + 1 : ℕ) : ℝ) *
    (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k) -
    (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k)

theorem finiteWeilCanonicalFluctuationResidual_first_moment_bound (r k : ℕ)
    (hwidth : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    (∑ i, finiteWeilCanonicalEdgeMass r k i * |finiteWeilCanonicalFluctuationResidualValue r k i|) ≤ 1 := by
  let m := finiteWeilCanonicalEdgeMass r k
  let D := finiteWeilCanonicalFluctuationResidualValue r k
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin (r + 1)))
    (r := fun i => m i * |D i|) (f := fun i => m i * D i ^ 2) (g := m)
    (fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (sq_nonneg _))
    (fun i _ => (finiteWeilCanonicalEdgeMass_pos r k i).le)
    (fun i _ => le_of_eq (by rw [mul_pow, sq_abs]; ring))
  change (∑ i, m i * |D i|) ^ 2 ≤ finiteWeilCanonicalFluctuationResidual r k *
    (∑ i, finiteWeilCanonicalEdgeMass r k i) at hcs
  rw [finiteWeilCanonicalEdgeMass_sum, mul_one] at hcs
  have hb := finiteWeilCanonicalFluctuationResidual_bound r k hwidth
  have hn : 0 ≤ ∑ i, m i * |D i| := Finset.sum_nonneg fun i _ =>
    mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (abs_nonneg _)
  change (∑ i, m i * |D i|) ≤ 1
  nlinarith only [hcs, hb, hn]

def finiteWeilCanonicalJointCharacteristic (r k : ℕ) (a b : ℝ) : ℂ :=
  ∑ i : Fin (r + 1), (finiteWeilCanonicalEdgeMass r k i : ℂ) *
    finiteWeilPhase ((a * (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) +
      b * (((r + 1 : ℕ) : ℝ) *
        (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k))) /
      Real.sqrt ((r + 1 : ℕ) : ℝ))

theorem finiteWeilCanonicalJointCharacteristic_centered_bound (r k : ℕ) (a b : ℝ)
    (hwidth : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    ‖finiteWeilCanonicalJointCharacteristic r k a b -
      finiteWeilCanonicalCenteredCharacteristic r k ((a + b) / Real.sqrt ((r + 1 : ℕ) : ℝ))‖ ≤
      |b| / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
  let s := Real.sqrt ((r + 1 : ℕ) : ℝ)
  let X := fun i : Fin (r + 1) => ((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k
  let Y := fun i : Fin (r + 1) => ((r + 1 : ℕ) : ℝ) *
    (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k)
  let D := finiteWeilCanonicalFluctuationResidualValue r k
  have hs : 0 < s := by dsimp [s]; positivity
  have hid (i : Fin (r + 1)) : (a * X i + b * Y i) / s - ((a + b) / s) * X i = b * D i / s := by
    dsimp [X, Y, D, finiteWeilCanonicalFluctuationResidualValue]
    ring
  calc
    _ ≤ ∑ i, |finiteWeilCanonicalEdgeMass r k i| * |(a * X i + b * Y i) / s - ((a + b) / s) * X i| :=
      finiteWeilPhase_phase_error _ _ _
    _ = (|b| / s) * ∑ i, finiteWeilCanonicalEdgeMass r k i * |D i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_pos (finiteWeilCanonicalEdgeMass_pos r k i), hid, abs_div, abs_mul, abs_of_pos hs]
      ring
    _ ≤ (|b| / s) * 1 := mul_le_mul_of_nonneg_left
      (finiteWeilCanonicalFluctuationResidual_first_moment_bound r k hwidth) (div_nonneg (abs_nonneg _) hs.le)
    _ = _ := mul_one _

theorem finiteWeilCanonicalJointCharacteristic_quadratic_bound (r t : ℕ) (a b : ℝ) :
    ‖finiteWeilCanonicalJointCharacteristic r (2 * (r + 1) ^ 2 + t) a b -
      finiteWeilCanonicalCenteredCharacteristic r (2 * (r + 1) ^ 2 + t)
        ((a + b) / Real.sqrt ((r + 1 : ℕ) : ℝ))‖ ≤ |b| / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
  apply finiteWeilCanonicalJointCharacteristic_centered_bound
  push_cast
  nlinarith only [sq_nonneg ((r : ℝ) + 1), (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]

theorem tendsto_finiteWeilCanonicalJointCharacteristic_gaussian (t : ℕ → ℕ) (a b : ℝ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalJointCharacteristic r (2 * (r + 1) ^ 2 + t r) a b)
      atTop (𝓝 ((Real.exp (-((a + b) ^ 2 / 8)) : ℝ) : ℂ)) := by
  apply (tendsto_finiteWeilCanonicalCenteredCharacteristic_gaussian t (a + b)).congr_dist
  apply squeeze_zero (g := fun r : ℕ => |b| * (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹) (fun r => dist_nonneg)
  · intro r
    rw [dist_eq_norm, norm_sub_rev]
    calc
      _ ≤ |b| / Real.sqrt ((r + 1 : ℕ) : ℝ) := finiteWeilCanonicalJointCharacteristic_quadratic_bound r (t r) a b
      _ = _ := by ring
  · simpa only [mul_zero] using tendsto_finiteWeil_inverse_sqrt_succ.const_mul |b|

end RHTower
