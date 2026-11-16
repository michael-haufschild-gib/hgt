import GaloisForLFunctions.HTGeometry.InfiniteHorizonNormalizationLaw
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Convergence of the regularized Coulomb partial waves

The square-root and logarithmic summands in equations (68) and (181) of
*Zeta function in Coulomb background*, https://arxiv.org/abs/2611.12294,
are dominated by a shifted inverse-square series. Rationalizing the
square-root remainder proves convergence without an asymptotic expansion.
The bounds are uniform when the mass ranges over a bounded set.
For arbitrary families the regularized remainder is summable exactly when
the original family is square-summable. Thus this bounded regularization
preserves the inverse-horizon normalization domain.
-/

noncomputable section
namespace RHTower.Coulomb

/-- Subtracting the constant asymptotic term from the reciprocal square root. -/
def sqrtRemainder (x : ℝ) : ℝ := 1 - 1 / Real.sqrt (1 + x ^ 2)

/-- Rationalization exposes the full quadratic cancellation. -/
theorem sqrtRemainder_eq (x : ℝ) :
    sqrtRemainder x = x ^ 2 /
      (Real.sqrt (1 + x ^ 2) * (Real.sqrt (1 + x ^ 2) + 1)) := by
  have hs : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  unfold sqrtRemainder
  field_simp
  nlinarith only [hsq]

/-- The subtracted square-root term is nonnegative and at most half the squared argument. -/
theorem sqrtRemainder_bounds (x : ℝ) :
    0 ≤ sqrtRemainder x ∧ sqrtRemainder x ≤ x ^ 2 / 2 := by
  rw [sqrtRemainder_eq]
  have hs : 1 ≤ Real.sqrt (1 + x ^ 2) := Real.one_le_sqrt.mpr (by linarith [sq_nonneg x])
  have hd : 2 ≤ Real.sqrt (1 + x ^ 2) * (Real.sqrt (1 + x ^ 2) + 1) := by
    nlinarith only [hs, sq_nonneg (Real.sqrt (1 + x ^ 2) - 1)]
  constructor
  · positivity
  · exact div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num) hd

/-- The angular momentum is shifted by one half. -/
def angularMomentum (n : ℕ) : ℝ := n + 1 / 2

theorem angularMomentum_half_le (n : ℕ) : 1 / 2 ≤ angularMomentum n := by
  unfold angularMomentum
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem angularMomentum_pos (n : ℕ) : 0 < angularMomentum n :=
  lt_of_lt_of_le (by norm_num) (angularMomentum_half_le n)

/-- The common majorant has a convergent series. -/
theorem summable_inverse_angularMomentum_sq :
    Summable (fun n => 1 / angularMomentum n ^ 2) := by
  have h := (Real.summable_one_div_nat_add_rpow (1 / 2) 2).mpr (by norm_num)
  simpa only [angularMomentum, Real.rpow_two, sq_abs] using h

/-- The square-root partial wave in the regularized Coulomb sum. -/
def rootWave (m : ℝ) (n : ℕ) : ℝ := sqrtRemainder (m / angularMomentum n)

/-- The logarithmic partial wave in the regularized Coulomb sum. -/
def logWave (m : ℝ) (n : ℕ) : ℝ :=
  Real.log (1 + (m / angularMomentum n) ^ 2) / angularMomentum n

theorem rootWave_bounds (m : ℝ) (n : ℕ) :
    0 ≤ rootWave m n ∧ rootWave m n ≤ (m ^ 2 / 2) * (1 / angularMomentum n ^ 2) := by
  have h := sqrtRemainder_bounds (m / angularMomentum n)
  constructor
  · exact h.1
  · calc
      rootWave m n ≤ (m / angularMomentum n) ^ 2 / 2 := h.2
      _ = _ := by ring

theorem logWave_bounds (m : ℝ) (n : ℕ) :
    0 ≤ logWave m n ∧ logWave m n ≤ (2 * m ^ 2) * (1 / angularMomentum n ^ 2) := by
  have hv := angularMomentum_pos n
  have hv' := angularMomentum_half_le n
  have hl : 0 ≤ Real.log (1 + (m / angularMomentum n) ^ 2) :=
    Real.log_nonneg (by linarith [sq_nonneg (m / angularMomentum n)])
  have hu : Real.log (1 + (m / angularMomentum n) ^ 2) ≤
      (m / angularMomentum n) ^ 2 := by
    simpa only [add_sub_cancel_left] using
      Real.log_le_sub_one_of_pos (show 0 < 1 + (m / angularMomentum n) ^ 2 by positivity)
  constructor
  · exact div_nonneg hl hv.le
  · calc
      _ ≤ (m / angularMomentum n) ^ 2 / angularMomentum n :=
        div_le_div_of_nonneg_right hu hv.le
      _ ≤ (m / angularMomentum n) ^ 2 / (1 / 2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hv'
      _ = _ := by ring

/-- The regularized square-root sum converges for every real mass. -/
theorem summable_rootWave (m : ℝ) : Summable (rootWave m) :=
  Summable.of_nonneg_of_le (fun n => (rootWave_bounds m n).1)
    (fun n => (rootWave_bounds m n).2)
    (summable_inverse_angularMomentum_sq.mul_left (m ^ 2 / 2))

/-- The regularized logarithmic sum converges for every real mass. -/
theorem summable_logWave (m : ℝ) : Summable (logWave m) :=
  Summable.of_nonneg_of_le (fun n => (logWave_bounds m n).1)
    (fun n => (logWave_bounds m n).2)
    (summable_inverse_angularMomentum_sq.mul_left (2 * m ^ 2))

/-- The complete series part of equation (181), with arbitrary real coupling. -/
theorem summable_regularizedCoulomb (α m : ℝ) :
    Summable (fun n => α * (rootWave m n / 4 + logWave m n / (48 * Real.pi))) := by
  exact ((summable_rootWave m).div_const 4 |>.add
    ((summable_logWave m).div_const (48 * Real.pi))).mul_left α

/-- The whole root sum vanishes at least quadratically as the mass tends to zero. -/
theorem rootWave_tsum_bounds (m : ℝ) :
    0 ≤ ∑' n, rootWave m n ∧
      (∑' n, rootWave m n) ≤ (m ^ 2 / 2) * ∑' n, 1 / angularMomentum n ^ 2 := by
  constructor
  · exact tsum_nonneg (fun n => (rootWave_bounds m n).1)
  · rw [← tsum_mul_left]
    exact (summable_rootWave m).tsum_le_tsum (fun n => (rootWave_bounds m n).2)
      (summable_inverse_angularMomentum_sq.mul_left (m ^ 2 / 2))

theorem continuous_rootWave (n : ℕ) : Continuous (fun m => rootWave m n) := by
  unfold rootWave sqrtRemainder angularMomentum
  fun_prop (disch := intro x; positivity)

theorem continuous_logWave (n : ℕ) : Continuous (fun m => logWave m n) := by
  unfold logWave angularMomentum
  fun_prop (disch := intro x; positivity)

/-- Local uniform domination makes the infinite root sum continuous in mass. -/
theorem continuous_rootWave_tsum : Continuous (fun m => ∑' n, rootWave m n) := by
  apply continuous_iff_continuousAt.mpr
  intro m
  let M := |m| + 1
  have hcont : ContinuousOn (fun x => ∑' n, rootWave x n) (Set.Icc (-M) M) := by
    apply continuousOn_tsum (fun n => (continuous_rootWave n).continuousOn)
      (summable_inverse_angularMomentum_sq.mul_left (M ^ 2 / 2))
    intro n x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (rootWave_bounds x n).1]
    have hxM : x ^ 2 ≤ M ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
    exact (rootWave_bounds x n).2.trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  apply hcont.continuousAt
  apply Icc_mem_nhds <;> dsimp [M] <;> linarith [neg_abs_le m, le_abs_self m]

/-- The logarithmic partial-wave sum is continuous in mass as well. -/
theorem continuous_logWave_tsum : Continuous (fun m => ∑' n, logWave m n) := by
  apply continuous_iff_continuousAt.mpr
  intro m
  let M := |m| + 1
  have hcont : ContinuousOn (fun x => ∑' n, logWave x n) (Set.Icc (-M) M) := by
    apply continuousOn_tsum (fun n => (continuous_logWave n).continuousOn)
      (summable_inverse_angularMomentum_sq.mul_left (2 * M ^ 2))
    intro n x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (logWave_bounds x n).1]
    have hxM : x ^ 2 ≤ M ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
    exact (logWave_bounds x n).2.trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  apply hcont.continuousAt
  apply Icc_mem_nhds <;> dsimp [M] <;> linarith [neg_abs_le m, le_abs_self m]

/-- In the small-remainder regime, rationalization also gives a lower quadratic bound. -/
theorem sq_le_six_mul_sqrtRemainder (x : ℝ) (hx : sqrtRemainder x ≤ 1 / 2) :
    x ^ 2 ≤ 6 * sqrtRemainder x := by
  let s := Real.sqrt (1 + x ^ 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hr : (1 / 2 : ℝ) ≤ 1 / s := by
    change 1 - 1 / s ≤ 1 / 2 at hx
    linarith
  have hs2 : s ≤ 2 := by
    have := (le_div_iff₀ hs).mp hr
    linarith
  have hd : s * (s + 1) ≤ 6 := by
    nlinarith only [hs2, mul_nonneg hs.le (sub_nonneg.mpr hs2)]
  have he : sqrtRemainder x * (s * (s + 1)) = x ^ 2 :=
    (eq_div_iff (by positivity : s * (s + 1) ≠ 0)).mp (sqrtRemainder_eq x)
  calc
    x ^ 2 = sqrtRemainder x * (s * (s + 1)) := he.symm
    _ ≤ sqrtRemainder x * 6 := mul_le_mul_of_nonneg_left hd (sqrtRemainder_bounds x).1
    _ = _ := mul_comm _ _

/-- Bounded square-root regularization preserves the square-summability
domain on every index set. Summability forces all but finitely many
remainders into the regime where the reverse quadratic bound applies. -/
theorem summable_sqrtRemainder_iff {ι : Type*} (x : ι → ℝ) :
    Summable (fun i => sqrtRemainder (x i)) ↔ Summable (fun i => (x i) ^ 2) := by
  constructor
  · intro h
    have hev : ∀ᶠ i in Filter.cofinite, sqrtRemainder (x i) < 1 / 2 :=
      h.tendsto_cofinite_zero (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    apply (h.mul_left 6).of_norm_bounded_eventually
    filter_upwards [hev] with i hi
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_six_mul_sqrtRemainder (x i) hi.le
  · intro h
    apply Summable.of_nonneg_of_le (fun i => (sqrtRemainder_bounds (x i)).1)
      (fun i => (sqrtRemainder_bounds (x i)).2)
    exact h.div_const 2

/-- The existing inverse-horizon domain has an equivalent bounded regularized test. -/
theorem coulomb_inverseHorizon_iff {ι : Type*} (h z : ι → ℂ) :
    Summable (fun i => sqrtRemainder ‖z i / h i‖) ↔
      GaloisForLFunctions.HTGeometry.InverseHorizonSquareSummable h z :=
  summable_sqrtRemainder_iff _

/-- Regularizing a normalized horizon ray still admits exactly its zero vector. -/
theorem coulomb_horizon_ray_iff {ι : Type*} [Infinite ι]
    (h : ι → ℂ) (hh : ∀ i, h i ≠ 0) (c : ℂ) :
    Summable (fun i => sqrtRemainder ‖(c * h i) / h i‖) ↔ c = 0 := by
  rw [coulomb_inverseHorizon_iff]
  exact GaloisForLFunctions.HTGeometry.inverseHorizonSquareSummable_ray_iff h hh c

#print axioms sqrtRemainder_bounds
#print axioms summable_regularizedCoulomb
#print axioms rootWave_tsum_bounds
#print axioms continuous_rootWave_tsum
#print axioms continuous_logWave_tsum
#print axioms summable_sqrtRemainder_iff
#print axioms coulomb_horizon_ray_iff
end RHTower.Coulomb
