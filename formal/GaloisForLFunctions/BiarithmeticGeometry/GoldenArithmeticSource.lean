import GaloisForLFunctions.BiarithmeticGeometry.GoldenInverseSeries
import GaloisForLFunctions.BiarithmeticGeometry.GeometricTowerDigitReceiver
import GaloisForLFunctions.BiarithmeticGeometry.PaidSourcePerturbations

/-!
# The actual golden arithmetic source

The inverse of the golden zeta series is read on powers of five. Its larger real root
supplies one geometric tower; the unit and the smaller tower form a critical Wiener
perturbation. Their removal preserves the entire repairing ideal.
-/

noncomputable section
open PowerSeries GaloisForLFunctions
open ArithmeticCastelnuovoSeveri ArithmeticOrientationTheory TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.BiarithmeticGeometry

def goldenPrimaryRoot : ℝ := (5 + Real.sqrt 5) / 2

def goldenSecondaryRoot : ℝ := (5 - Real.sqrt 5) / 2

theorem golden_alpha_zero_real : goldenDatum.alpha 0 = (goldenPrimaryRoot : ℂ) := by
  unfold goldenPrimaryRoot
  push_cast
  linear_combination (1 / 2 : ℂ) * goldenDatum_alpha_sum + (1 / 2 : ℂ) * golden_alpha_sub

theorem golden_alpha_one_real : goldenDatum.alpha 1 = (goldenSecondaryRoot : ℂ) := by
  unfold goldenSecondaryRoot
  push_cast
  linear_combination (1 / 2 : ℂ) * goldenDatum_alpha_sum - (1 / 2 : ℂ) * golden_alpha_sub

private theorem sqrt_five_bounds : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  constructor <;> nlinarith only [hs, hp]

theorem golden_root_bounds :
    0 < goldenPrimaryRoot ∧ goldenPrimaryRoot < 5 ∧
    0 < goldenSecondaryRoot ∧ goldenSecondaryRoot < Real.sqrt 5 := by
  obtain ⟨h2, h3⟩ := sqrt_five_bounds
  dsimp [goldenPrimaryRoot, goldenSecondaryRoot]
  constructor
  · linarith only [h2]
  constructor
  · linarith only [h3]
  constructor <;> linarith only [h2, h3]

theorem golden_roots_sum : goldenPrimaryRoot + goldenSecondaryRoot = 5 := by
  unfold goldenPrimaryRoot goldenSecondaryRoot
  ring

theorem golden_roots_sub : goldenPrimaryRoot - goldenSecondaryRoot = Real.sqrt 5 := by
  unfold goldenPrimaryRoot goldenSecondaryRoot
  ring

theorem golden_roots_mul : goldenPrimaryRoot * goldenSecondaryRoot = 5 := by
  calc
    _ = (25 - Real.sqrt 5 ^ 2) / 4 := by unfold goldenPrimaryRoot goldenSecondaryRoot; ring
    _ = 5 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num

/-- Norm-lattice coefficients of the actual inverse series, extended by zero off the lattice. -/
def goldenArithmeticSource (t : ℝ) (n : ℕ) : ℝ :=
  if 5 ^ Nat.log 5 n = n then
    (coeff (Nat.log 5 n) (goldenInverseSeriesAt (t : ℂ))).re else 0

theorem goldenArithmeticSource_pow (t : ℝ) (r : ℕ) :
    goldenArithmeticSource t (5 ^ r) = (coeff r (goldenInverseSeriesAt (t : ℂ))).re := by
  simp [goldenArithmeticSource, Nat.log_pow (by omega : 1 < 5)]

/-- Every coefficient is exactly the unit minus the normalized difference of two towers. -/
theorem goldenArithmeticSource_eq_towers (t : ℝ) :
    goldenArithmeticSource t = fun n =>
      -(1 / Real.sqrt 5) * localFactorInverse 5 (goldenPrimaryRoot * t) n +
        (unitKernel n + (1 / Real.sqrt 5) *
          localFactorInverse 5 (goldenSecondaryRoot * t) n) := by
  funext n
  by_cases hn : ∃ r, n = 5 ^ r
  · obtain ⟨r, rfl⟩ := hn
    rw [goldenArithmeticSource_pow, localFactorInverse_pow (by omega : 1 < 5),
      localFactorInverse_pow (by omega : 1 < 5)]
    by_cases hr : r = 0
    · subst r
      rw [coeff_zero_eq_constantCoeff_apply, goldenInverseSeriesAt_constantCoeff]
      simp [unitKernel]
    · have hne : 5 ^ r ≠ 1 := (one_lt_pow' (by omega : 1 < 5) hr).ne'
      rw [goldenInverseSeriesAt_coeff _ r hr, golden_alpha_zero_real, golden_alpha_one_real]
      simp only [← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
        ← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re, unitKernel,
        hne, if_false, zero_add]
      ring
  · have hnot : ∀ r, n ≠ 5 ^ r := fun r hr => hn ⟨r, hr⟩
    have hne : n ≠ 1 := fun h => hnot 0 (by simpa using h)
    have hlog : 5 ^ Nat.log 5 n ≠ n := Ne.symm (hnot _)
    simp only [goldenArithmeticSource, hlog, if_false,
      localFactorInverse_eq_zero _ hnot, unitKernel, hne, mul_zero, add_zero]

private theorem golden_primary_damped_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |goldenPrimaryRoot * t| < 5 := by
  rw [abs_of_nonneg (mul_nonneg golden_root_bounds.1.le ht0)]
  exact (mul_le_of_le_one_right golden_root_bounds.1.le ht1).trans_lt golden_root_bounds.2.1

private theorem golden_secondary_damped_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |goldenSecondaryRoot * t| < Real.sqrt 5 := by
  rw [abs_of_nonneg (mul_nonneg golden_root_bounds.2.2.1.le ht0)]
  exact (mul_le_of_le_one_right golden_root_bounds.2.2.1.le ht1).trans_lt golden_root_bounds.2.2.2

/-- The unit and secondary tower form a critical Wiener source throughout the damping interval. -/
theorem golden_remainder_criticalWiener (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    CriticalWiener (fun n => unitKernel n + (1 / Real.sqrt 5) *
      localFactorInverse 5 (goldenSecondaryRoot * t) n) := by
  have hb := (criticalWiener_localFactorInverse_iff (by norm_num : Nat.Prime 5)
    (goldenSecondaryRoot * t)).mpr (golden_secondary_damped_bound t ht0 ht1)
  refine (criticalWiener_unitKernel.add (hb.mul_left |1 / Real.sqrt 5|)).of_nonneg_of_le
    (fun n => by positivity) (fun n => ?_)
  calc
    _ ≤ (|unitKernel n| + |(1 / Real.sqrt 5) *
        localFactorInverse 5 (goldenSecondaryRoot * t) n|) *
          (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)
    _ = _ := by rw [abs_mul]; ring

/-- The arithmetic source has an absolutely convergent mean at every allowed damping. -/
theorem summable_abs_goldenArithmeticSource_div (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Summable (fun n : ℕ => |goldenArithmeticSource t n / n|) := by
  rw [goldenArithmeticSource_eq_towers]
  exact summable_abs_add_div
    (summable_abs_smul_div (summable_abs_fiveTower_div _
      (golden_primary_damped_bound t ht0 ht1)) _)
    (golden_remainder_criticalWiener t ht0 ht1).summable_abs_div

/-- The arithmetic residue mean of the damped golden inverse. -/
def goldenArithmeticMean (t : ℝ) : ℝ := (5 - 6 * t + t ^ 2) / (5 - 5 * t + t ^ 2)

private theorem hasSum_unitKernel_div : HasSum (fun n : ℕ => unitKernel n / n) (1 : ℝ) := by
  have he : (fun n : ℕ => unitKernel n / n) = fun n => if n = 1 then (1 : ℝ) else 0 := by
    funext n
    by_cases hn : n = 1 <;> simp [unitKernel, hn]
  rw [he]
  exact hasSum_ite_eq 1 1

theorem hasSum_goldenArithmeticSource_div (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasSum (fun n : ℕ => goldenArithmeticSource t n / n)
      (-(1 / Real.sqrt 5) * (5 / (5 - goldenPrimaryRoot * t)) +
        (1 + (1 / Real.sqrt 5) * (5 / (5 - goldenSecondaryRoot * t)))) := by
  have ha := hasSum_fiveTower_div _ (golden_primary_damped_bound t ht0 ht1)
  have hb5 : |goldenSecondaryRoot * t| < 5 :=
    (golden_secondary_damped_bound t ht0 ht1).trans (by linarith only [sqrt_five_bounds.2])
  have hb := hasSum_fiveTower_div _ hb5
  refine ((ha.mul_left (-(1 / Real.sqrt 5))).add
    (hasSum_unitKernel_div.add (hb.mul_left (1 / Real.sqrt 5)))).congr_fun fun n => ?_
  rw [goldenArithmeticSource_eq_towers]
  ring

private theorem combine_fiveTower_means (x y s : ℝ) (hx : 5 - x ≠ 0)
    (hy : 5 - y ≠ 0) (hs : s ≠ 0) :
    -(1 / s) * (5 / (5 - x)) + (1 + (1 / s) * (5 / (5 - y))) =
      1 - 5 * (x - y) / (s * ((5 - x) * (5 - y))) := by
  field_simp [hx, hy, hs]
  ring

/-- The exact source mean is the inverse golden zeta value at the counting pole. -/
theorem goldenArithmeticSource_mean (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑' n : ℕ, goldenArithmeticSource t n / n) = goldenArithmeticMean t := by
  rw [(hasSum_goldenArithmeticSource_div t ht0 ht1).tsum_eq]
  have ha : goldenPrimaryRoot * t < 5 :=
    (le_abs_self _).trans_lt (golden_primary_damped_bound t ht0 ht1)
  have hb : goldenSecondaryRoot * t < 5 :=
    (le_abs_self _).trans_lt ((golden_secondary_damped_bound t ht0 ht1).trans
      (by linarith only [sqrt_five_bounds.2]))
  have ha0 : 5 - goldenPrimaryRoot * t ≠ 0 := sub_ne_zero.mpr ha.ne'
  have hb0 : 5 - goldenSecondaryRoot * t ≠ 0 := sub_ne_zero.mpr hb.ne'
  have hs : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  have hD : 5 - 5 * t + t ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [sq_nonneg (t - 1), ht1])
  have hp : (5 - goldenPrimaryRoot * t) * (5 - goldenSecondaryRoot * t) =
      5 * (5 - 5 * t + t ^ 2) := by
    calc
      _ = 25 - 5 * t * (goldenPrimaryRoot + goldenSecondaryRoot) +
          t ^ 2 * (goldenPrimaryRoot * goldenSecondaryRoot) := by ring
      _ = _ := by rw [golden_roots_sum, golden_roots_mul]; ring
  have hd : goldenPrimaryRoot * t - goldenSecondaryRoot * t = Real.sqrt 5 * t := by
    rw [← sub_mul, golden_roots_sub]
  calc
    _ = 1 - 5 * (goldenPrimaryRoot * t - goldenSecondaryRoot * t) /
        (Real.sqrt 5 * ((5 - goldenPrimaryRoot * t) * (5 - goldenSecondaryRoot * t))) :=
      combine_fiveTower_means _ _ _ ha0 hb0 hs
    _ = 1 - t / (5 - 5 * t + t ^ 2) := by
      rw [hd, hp]
      field_simp [hs, hD]
    _ = goldenArithmeticMean t := by
      unfold goldenArithmeticMean
      calc
        _ = ((5 - 5 * t + t ^ 2) - t) / (5 - 5 * t + t ^ 2) := by
          rw [sub_div, div_self hD]
        _ = _ := by congr 1; ring

/-- The complete golden repairing ideal is exactly that of its primary geometric tower. -/
theorem paidIdeal_goldenArithmeticSource (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    paidIdeal (goldenArithmeticSource t) (summable_abs_goldenArithmeticSource_div t ht0 ht1) =
      paidIdeal (localFactorInverse 5 (goldenPrimaryRoot * t))
        (summable_abs_fiveTower_div _ (golden_primary_damped_bound t ht0 ht1)) := by
  let hc := summable_abs_fiveTower_div _ (golden_primary_damped_bound t ht0 ht1)
  let hd := golden_remainder_criticalWiener t ht0 ht1
  have hne : -(1 / Real.sqrt 5) ≠ 0 := neg_ne_zero.mpr
    (one_div_ne_zero (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne')
  calc
    _ = paidIdeal (fun n => -(1 / Real.sqrt 5) *
        localFactorInverse 5 (goldenPrimaryRoot * t) n +
          (unitKernel n + (1 / Real.sqrt 5) * localFactorInverse 5 (goldenSecondaryRoot * t) n))
        (summable_abs_add_div (summable_abs_smul_div hc _) hd.summable_abs_div) := by
      ext k
      exact mem_paidIdeal_congr (goldenArithmeticSource_eq_towers t) _ _ k
    _ = _ := paidIdeal_smul_add_criticalWiener _ _ hc hd _ hne

end GaloisForLFunctions.BiarithmeticGeometry
