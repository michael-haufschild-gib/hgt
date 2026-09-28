import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryRateConstants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Wallis integrals and the arcsine-mixture density

`J_n = ∫_0^{π/2} cos^n` satisfies `J_{n+2} = (n+1)/(n+2) J_n`, hence the Wallis product
`(n+1) J_n J_{n+1} = π/2`.  Expanding `1/(1 - a cos s)` gives `I(a) = Σ J_n a^n`.  The density
`h(a) = Σ c_n a^n`, `c_n = (n+1) J_{n+1}/π` (so `h = I'/π`), has mass `∫_0^x h = (I(x) - π/2)/π`, and

* `∫_0^b log(a/2) h(a) da = log(b/2) (I(b) - π/2)/π + (1/π) ∫_0^{π/2} log(1 - b cos s) ds`;
* (Abel identity) `∫_0^t A(a,t) h(a) da = -log(1-t)/2` for the arcsine excess
  `A(a,t) = log(max(a,t) + √(t²-a²)) - log a`, from `∫_0^1 x^n A(x,1) dx = J_n/(n+1)` and the
  Wallis product.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-! ### Two integration tools -/

/-- Termwise integration of a series over an interval, given summable integrals of the norms. -/
theorem hasSum_intervalIntegral_of_summable_norm {f : ℕ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ n, IntervalIntegrable (f n) volume a b)
    (hs : Summable fun n => ∫ x in a..b, ‖f n x‖) :
    HasSum (fun n => ∫ x in a..b, f n x) (∫ x in a..b, ∑' n, f n x) := by
  have hint : ∀ n, Integrable (f n) (volume.restrict (Ioc a b)) := fun n => (hf n).1
  have hs' : Summable fun n => ∫ x in Ioc a b, ‖f n x‖ := by
    simpa only [intervalIntegral.integral_of_le hab] using hs
  have hsum : Summable fun n => ∫ x in a..b, f n x := by
    refine Summable.of_norm_bounded hs fun n => ?_
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    exact norm_integral_le_integral_norm _
  have := integral_tsum_of_summable_integral_norm hint hs'
  rw [intervalIntegral.integral_of_le hab, ← this]
  simpa only [intervalIntegral.integral_of_le hab] using hsum.hasSum

/-- The fundamental theorem of calculus for a continuous primitive with nonnegative derivative:
the derivative is integrable, even with singular endpoints. -/
theorem intervalIntegrable_and_integral_eq_of_deriv_nonneg {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hnn : ∀ x ∈ Ioo a b, 0 ≤ f' x) :
    IntervalIntegrable f' volume a b ∧ ∫ x in a..b, f' x = f b - f a := by
  have hi : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (integrableOn_deriv_of_nonneg hcont hderiv hnn)
  exact ⟨hi, integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hi⟩

/-! ### Wallis integrals -/

/-- The Wallis integral `J_n = ∫_0^{π/2} cos^n s ds`. -/
def wallisJ (n : ℕ) : ℝ := ∫ s in (0 : ℝ)..π / 2, Real.cos s ^ n

theorem wallisJ_zero : wallisJ 0 = π / 2 := by simp [wallisJ]

theorem wallisJ_one : wallisJ 1 = 1 := by simp [wallisJ, integral_cos]

theorem wallisJ_add_two (n : ℕ) : wallisJ (n + 2) = (n + 1) / (n + 2) * wallisJ n := by
  rw [wallisJ, integral_cos_pow, Real.cos_pi_div_two, Real.sin_zero]
  simp [wallisJ]

theorem wallisJ_pos (n : ℕ) : 0 < wallisJ n := by
  refine intervalIntegral_pos_of_pos_on ((by fun_prop : Continuous fun s => Real.cos s ^ n)
    |>.intervalIntegrable _ _) (fun s hs => pow_pos (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩) n) (by positivity)

theorem wallisJ_le (n : ℕ) : wallisJ n ≤ π / 2 := by
  have h := intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ π / 2)
    ((by fun_prop : Continuous fun s => Real.cos s ^ n).intervalIntegrable 0 (π / 2))
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun s hs =>
      pow_le_one₀ (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩)
        (Real.cos_le_one s)
  simpa [wallisJ] using h

/-- **The Wallis product** `(n+1) J_n J_{n+1} = π/2`. -/
theorem wallisJ_mul (n : ℕ) : ((n : ℝ) + 1) * wallisJ n * wallisJ (n + 1) = π / 2 := by
  induction n with
  | zero => simp [wallisJ_zero, wallisJ_one]
  | succ n ih =>
    have h2 := wallisJ_add_two n
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    calc ((↑(n + 1) : ℝ) + 1) * wallisJ (n + 1) * wallisJ (n + 1 + 1)
        = ((n : ℝ) + 2) * wallisJ (n + 1) * ((n + 1) / (n + 2) * wallisJ n) := by
          rw [show n + 1 + 1 = n + 2 from rfl, h2]; push_cast; ring
      _ = ((n : ℝ) + 1) * wallisJ n * wallisJ (n + 1) := by field_simp
      _ = π / 2 := ih

theorem wallisJ_eq_sin (n : ℕ) : wallisJ n = ∫ s in (0 : ℝ)..π / 2, Real.sin s ^ n := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2)
    (fun s => Real.cos s ^ n) (π / 2)
  simp only [Real.cos_pi_div_two_sub, sub_zero, sub_self] at h
  rw [h, wallisJ]

/-! ### The series of `I` and of `-∫ log(1 - b cos)` -/

theorem abs_mul_cos_lt_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (s : ℝ) :
    |a * Real.cos s| < 1 := by
  rw [abs_mul, abs_of_nonneg ha0]
  calc a * |Real.cos s| ≤ a * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one s) ha0
    _ < 1 := by linarith

theorem integral_mul_cos_pow (a : ℝ) (n : ℕ) :
    ∫ s in (0 : ℝ)..π / 2, (a * Real.cos s) ^ n = wallisJ n * a ^ n := by
  simp only [mul_pow, wallisJ]
  rw [intervalIntegral.integral_const_mul]; ring

theorem integral_norm_mul_cos_pow {a : ℝ} (ha0 : 0 ≤ a) (n : ℕ) :
    ∫ s in (0 : ℝ)..π / 2, ‖(a * Real.cos s) ^ n‖ = wallisJ n * a ^ n := by
  rw [← integral_mul_cos_pow]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ π / 2)] at hs
  have hc : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
  simp only [Real.norm_eq_abs]
  exact abs_of_nonneg (pow_nonneg (mul_nonneg ha0 hc) n)

theorem summable_wallisJ_mul_pow {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable fun n => wallisJ n * a ^ n :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (wallisJ_pos n).le (pow_nonneg ha0 n))
    (fun n => mul_le_mul_of_nonneg_right (wallisJ_le n) (pow_nonneg ha0 n))
    ((summable_geometric_of_lt_one ha0 ha1).mul_left _)

/-- **`I(a) = Σ J_n a^n`** for `0 ≤ a < 1`. -/
theorem hasSum_recoveryI {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun n => wallisJ n * a ^ n) (recoveryI a) := by
  have h := hasSum_intervalIntegral_of_summable_norm (f := fun n s => (a * Real.cos s) ^ n)
    (by positivity : (0 : ℝ) ≤ π / 2)
    (fun n => (by fun_prop : Continuous fun s => (a * Real.cos s) ^ n).intervalIntegrable _ _)
    (by simpa only [integral_norm_mul_cos_pow ha0] using summable_wallisJ_mul_pow ha0 ha1)
  have e2 : ∫ s in (0 : ℝ)..π / 2, ∑' n, (a * Real.cos s) ^ n = recoveryI a := by
    unfold recoveryI
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [tsum_geometric_of_abs_lt_one (abs_mul_cos_lt_one ha0 ha1 s), one_div]
  simpa only [integral_mul_cos_pow, e2] using h

/-- `Σ J_{n+1} b^{n+1}/(n+1) = -∫_0^{π/2} log(1 - b cos s) ds` for `0 ≤ b < 1`. -/
theorem hasSum_wallisJ_log {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    HasSum (fun n : ℕ => wallisJ (n + 1) * b ^ (n + 1) / (n + 1))
      (-∫ s in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos s)) := by
  have hval : ∀ n : ℕ, ∫ s in (0 : ℝ)..π / 2, (b * Real.cos s) ^ (n + 1) / (n + 1) =
      wallisJ (n + 1) * b ^ (n + 1) / (n + 1) := fun n => by
    rw [intervalIntegral.integral_div, integral_mul_cos_pow]
  have hnorm : ∀ n : ℕ, ∫ s in (0 : ℝ)..π / 2, ‖(b * Real.cos s) ^ (n + 1) / (n + 1)‖ =
      wallisJ (n + 1) * b ^ (n + 1) / (n + 1) := fun n => by
    rw [← hval]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ π / 2)] at hs
    have hc : 0 ≤ Real.cos s :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
    simp only [Real.norm_eq_abs]
    exact abs_of_nonneg (div_nonneg (pow_nonneg (mul_nonneg hb0 hc) _) (by positivity))
  have hsum : Summable fun n : ℕ => wallisJ (n + 1) * b ^ (n + 1) / (n + 1) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (mul_nonneg (wallisJ_pos _).le
      (pow_nonneg hb0 _)) (by positivity))
      (fun n => div_le_self (mul_nonneg (wallisJ_pos _).le (pow_nonneg hb0 _))
        (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
      ((summable_nat_add_iff 1).mpr (summable_wallisJ_mul_pow hb0 hb1))
  have h := hasSum_intervalIntegral_of_summable_norm
    (f := fun (n : ℕ) s => (b * Real.cos s) ^ (n + 1) / (n + 1))
    (by positivity : (0 : ℝ) ≤ π / 2)
    (fun n => (by fun_prop : Continuous fun s => (b * Real.cos s) ^ (n + 1) / (n + 1))
      |>.intervalIntegrable _ _) (by simpa only [hnorm] using hsum)
  have e2 : ∫ s in (0 : ℝ)..π / 2, ∑' n : ℕ, (b * Real.cos s) ^ (n + 1) / (n + 1) =
      -∫ s in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos s) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact (Real.hasSum_pow_div_log_of_abs_lt_one (abs_mul_cos_lt_one hb0 hb1 s)).tsum_eq
  simpa only [hval, e2] using h

/-! ### The mixture density -/

/-- The coefficient `c_n = (n+1) J_{n+1}/π`. -/
def recoveryDensityCoeff (n : ℕ) : ℝ := ((n : ℝ) + 1) * wallisJ (n + 1) / π

/-- The arcsine-mixture density `h(a) = Σ c_n a^n` (it equals `I'(a)/π`). -/
def recoveryDensity (a : ℝ) : ℝ := ∑' n : ℕ, recoveryDensityCoeff n * a ^ n

theorem recoveryDensityCoeff_nonneg (n : ℕ) : 0 ≤ recoveryDensityCoeff n :=
  div_nonneg (mul_nonneg (by positivity) (wallisJ_pos _).le) Real.pi_pos.le

theorem recoveryDensityCoeff_le (n : ℕ) : recoveryDensityCoeff n ≤ ((n : ℝ) + 1) / 2 := by
  unfold recoveryDensityCoeff
  rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ) < 2)]
  have := wallisJ_le (n + 1)
  nlinarith [Real.pi_pos, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem summable_succ_mul_geometric {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) / 2 * c ^ n := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
    (by rwa [Real.norm_eq_abs, abs_of_nonneg hc0] : ‖c‖ < 1)
  have h2 := summable_geometric_of_lt_one hc0 hc1
  refine ((h1.add h2).div_const 2).congr fun n => ?_
  simp only [pow_one]; ring

theorem summable_recoveryDensity {a : ℝ} (ha : |a| < 1) :
    Summable fun n => recoveryDensityCoeff n * a ^ n := by
  refine Summable.of_norm_bounded (summable_succ_mul_geometric (abs_nonneg a) ha) fun n => ?_
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (recoveryDensityCoeff_nonneg n)]
  exact mul_le_mul_of_nonneg_right (recoveryDensityCoeff_le n) (pow_nonneg (abs_nonneg a) n)

theorem continuousOn_recoveryDensity {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ContinuousOn recoveryDensity (Icc (-c) c) := by
  refine continuousOn_tsum (fun n => (by fun_prop : Continuous fun a =>
    recoveryDensityCoeff n * a ^ n).continuousOn) (summable_succ_mul_geometric hc0 hc1)
    fun n a ha => ?_
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (recoveryDensityCoeff_nonneg n)]
  exact mul_le_mul (recoveryDensityCoeff_le n) (pow_le_pow_left₀ (abs_nonneg a)
    (abs_le.mpr ha) n) (pow_nonneg (abs_nonneg a) n) (by positivity)

theorem recoveryDensity_ge {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) : 1 / π ≤ recoveryDensity a := by
  have hs := summable_recoveryDensity (a := a) (by rwa [abs_of_nonneg ha0])
  have := hs.le_tsum 0 fun j _ => mul_nonneg (recoveryDensityCoeff_nonneg j) (pow_nonneg ha0 j)
  simpa [recoveryDensity, recoveryDensityCoeff, wallisJ_one] using this

theorem recoveryDensity_pos {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) : 0 < recoveryDensity a :=
  lt_of_lt_of_le (by positivity) (recoveryDensity_ge ha0 ha1)

theorem integral_recoveryDensityCoeff_mul_pow (n : ℕ) (x : ℝ) :
    ∫ a in (0 : ℝ)..x, recoveryDensityCoeff n * a ^ n = wallisJ (n + 1) * x ^ (n + 1) / π := by
  rw [intervalIntegral.integral_const_mul, integral_pow, recoveryDensityCoeff]
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  simp

/-- **The mass function** `∫_0^x h = (I(x) - π/2)/π` for `0 ≤ x < 1`. -/
theorem integral_recoveryDensity {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∫ a in (0 : ℝ)..x, recoveryDensity a = (recoveryI x - π / 2) / π := by
  have hnorm : ∀ n, ∫ a in (0 : ℝ)..x, ‖recoveryDensityCoeff n * a ^ n‖ =
      wallisJ (n + 1) * x ^ (n + 1) / π := fun n => by
    rw [← integral_recoveryDensityCoeff_mul_pow]
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [uIcc_of_le hx0] at ha
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (recoveryDensityCoeff_nonneg n)
      (pow_nonneg ha.1 n))]
  have hshift : HasSum (fun n => wallisJ (n + 1) * x ^ (n + 1)) (recoveryI x - π / 2) := by
    have := (hasSum_nat_add_iff' 1).mpr (hasSum_recoveryI hx0 hx1)
    simpa [wallisJ_zero] using this
  have h := hasSum_intervalIntegral_of_summable_norm
    (f := fun n a => recoveryDensityCoeff n * a ^ n) hx0
    (fun n => (by fun_prop : Continuous fun a => recoveryDensityCoeff n * a ^ n)
      |>.intervalIntegrable _ _) (by simpa only [hnorm] using (hshift.div_const π).summable)
  simp only [integral_recoveryDensityCoeff_mul_pow] at h
  exact h.unique (hshift.div_const π)

/-! ### The logarithmic moment -/

/-- `∫_0^b a^n log(a/2) da = b^{n+1} log(b/2)/(n+1) - b^{n+1}/(n+1)²` for `0 < b ≤ 2`. -/
theorem integral_pow_mul_log_half {b : ℝ} (hb0 : 0 < b) (hb2 : b ≤ 2) (n : ℕ) :
    IntervalIntegrable (fun a => a ^ n * Real.log (a / 2)) volume 0 b ∧
    ∫ a in (0 : ℝ)..b, a ^ n * Real.log (a / 2) =
      b ^ (n + 1) * Real.log (b / 2) / (n + 1) - b ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  set P : ℝ → ℝ := fun a => -(a ^ (n + 1) * Real.log (a / 2) / (n + 1) -
    a ^ (n + 1) / ((n : ℝ) + 1) ^ 2) with hP
  have hcont : Continuous P := by
    have hml : Continuous fun a : ℝ => a ^ (n + 1) * Real.log (a / 2) := by
      have : (fun a : ℝ => a ^ (n + 1) * Real.log (a / 2)) =
          fun a => 2 * a ^ n * ((a / 2) * Real.log (a / 2)) := by
        funext a; ring
      rw [this]
      exact (continuous_const.mul (continuous_pow n)).mul
        (Real.continuous_mul_log.comp (continuous_id.div_const 2))
    exact ((hml.div_const _).sub ((continuous_pow _).div_const _)).neg
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt P (-(x ^ n * Real.log (x / 2))) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h1 : HasDerivAt (fun a : ℝ => a ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * x ^ n) x := by
      simpa using hasDerivAt_pow (n + 1) x
    have h2 : HasDerivAt (fun a : ℝ => Real.log (a / 2)) (1 / x) x := by
      have := ((hasDerivAt_id x).div_const 2).log (div_ne_zero hx0 two_ne_zero)
      simp only [id] at this
      convert this using 1; field_simp
    have := (((h1.mul h2).div_const ((n : ℝ) + 1)).sub (h1.div_const (((n : ℝ) + 1) ^ 2))).neg
    refine this.congr_deriv ?_
    push_cast
    field_simp
    ring
  have hnn : ∀ x ∈ Ioo (0 : ℝ) b, 0 ≤ -(x ^ n * Real.log (x / 2)) := fun x hx => by
    have hlog : Real.log (x / 2) ≤ 0 :=
      Real.log_nonpos (div_nonneg hx.1.le (by norm_num)) (by rw [div_le_one (by norm_num)]; linarith [hx.2])
    nlinarith [pow_nonneg hx.1.le n]
  obtain ⟨hi, hint⟩ :=
    intervalIntegrable_and_integral_eq_of_deriv_nonneg hb0.le hcont.continuousOn hderiv hnn
  refine ⟨by convert hi.neg using 1; funext x; simp, ?_⟩
  rw [intervalIntegral.integral_neg] at hint
  have h0 : P 0 = 0 := by simp [hP]
  rw [h0, sub_zero, hP] at hint
  linarith

/-- **The logarithmic moment of `h`.** For `0 < b < 1`,
`∫_0^b log(a/2) h(a) da = log(b/2) (I(b) - π/2)/π + (1/π) ∫_0^{π/2} log(1 - b cos s) ds`. -/
theorem integral_log_half_mul_recoveryDensity {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∫ a in (0 : ℝ)..b, Real.log (a / 2) * recoveryDensity a =
      Real.log (b / 2) * ((recoveryI b - π / 2) / π) +
        (1 / π) * ∫ s in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos s) := by
  have hb2 : b ≤ 2 := by linarith [hb.2]
  have hmom := fun n => integral_pow_mul_log_half hb.1 hb2 n
  set L := Real.log (b / 2) with hL
  have hLneg : L ≤ 0 :=
    Real.log_nonpos (by linarith [hb.1]) (by rw [div_le_one (by norm_num)]; linarith [hb.2])
  -- the termwise integrals
  have hval : ∀ n : ℕ, ∫ a in (0 : ℝ)..b, Real.log (a / 2) * (recoveryDensityCoeff n * a ^ n) =
      L * (wallisJ (n + 1) * b ^ (n + 1) / π) -
        (1 / π) * (wallisJ (n + 1) * b ^ (n + 1) / (n + 1)) := fun n => by
    have : (fun a => Real.log (a / 2) * (recoveryDensityCoeff n * a ^ n)) =
        fun a => recoveryDensityCoeff n * (a ^ n * Real.log (a / 2)) := by
      funext a; ring
    rw [this, intervalIntegral.integral_const_mul, (hmom n).2, recoveryDensityCoeff]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hnorm : ∀ n : ℕ, ∫ a in (0 : ℝ)..b,
      ‖Real.log (a / 2) * (recoveryDensityCoeff n * a ^ n)‖ =
      -(L * (wallisJ (n + 1) * b ^ (n + 1) / π) -
        (1 / π) * (wallisJ (n + 1) * b ^ (n + 1) / (n + 1))) := fun n => by
    rw [← hval, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun a ha => ?_)
    rw [uIoc_of_le hb.1.le] at ha
    have hlog : Real.log (a / 2) ≤ 0 :=
      Real.log_nonpos (by linarith [ha.1]) (by rw [div_le_one (by norm_num)]; linarith [ha.2])
    rw [Real.norm_eq_abs, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hlog
      (mul_nonneg (recoveryDensityCoeff_nonneg n) (pow_nonneg ha.1.le n)))]
  have hS1 : HasSum (fun n => wallisJ (n + 1) * b ^ (n + 1) / π) ((recoveryI b - π / 2) / π) := by
    have := (hasSum_nat_add_iff' 1).mpr (hasSum_recoveryI hb.1.le hb.2)
    simpa [wallisJ_zero] using this.div_const π
  have hS2 := hasSum_wallisJ_log hb.1.le hb.2
  have htot := (hS1.mul_left L).sub (hS2.mul_left (1 / π))
  have h := hasSum_intervalIntegral_of_summable_norm
    (f := fun n a => Real.log (a / 2) * (recoveryDensityCoeff n * a ^ n)) hb.1.le
    (fun n => by
      have := (hmom n).1.const_mul (recoveryDensityCoeff n)
      convert this using 1; funext a; ring)
    (by simpa only [hnorm] using htot.summable.neg)
  simp only [hval] at h
  have e : ∫ a in (0 : ℝ)..b, ∑' n, Real.log (a / 2) * (recoveryDensityCoeff n * a ^ n) =
      ∫ a in (0 : ℝ)..b, Real.log (a / 2) * recoveryDensity a := by
    refine intervalIntegral.integral_congr fun a _ => ?_
    simp only [recoveryDensity]
    exact tsum_mul_left
  rw [e] at h
  rw [h.unique htot]
  ring

/-! ### The Abel identity -/

/-- The arcsine excess `A(a,t) = log(max(a,t) + √(t² - a²)) - log a`: for `0 < a` the arcsine law
on `[-a, a]` has potential `log(a/2) + A(a,t)` at `t ≥ 0`. -/
def arcsineExcess (a t : ℝ) : ℝ :=
  Real.log (max a t + Real.sqrt (t ^ 2 - a ^ 2)) - Real.log a

theorem arcsineExcess_nonneg {a t : ℝ} (ha : 0 < a) : 0 ≤ arcsineExcess a t := by
  unfold arcsineExcess
  have : a ≤ max a t + Real.sqrt (t ^ 2 - a ^ 2) :=
    le_add_of_le_of_nonneg (le_max_left _ _) (Real.sqrt_nonneg _)
  linarith [Real.log_le_log ha this]

theorem arcsineExcess_of_le {a t : ℝ} (hta : t ≤ a) (ht : 0 ≤ t) : arcsineExcess a t = 0 := by
  unfold arcsineExcess
  rw [max_eq_left hta, Real.sqrt_eq_zero'.mpr (by nlinarith), add_zero, sub_self]

theorem arcsineExcess_one {x : ℝ} (hx1 : x ≤ 1) :
    arcsineExcess x 1 = Real.log (1 + Real.sqrt (1 - x ^ 2)) - Real.log x := by
  simp [arcsineExcess, max_eq_right hx1]

theorem arcsineExcess_scale {t x : ℝ} (ht : 0 < t) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    arcsineExcess (t * x) t = arcsineExcess x 1 := by
  rw [arcsineExcess_one hx1, arcsineExcess, max_eq_right (by nlinarith)]
  have hs : Real.sqrt (t ^ 2 - (t * x) ^ 2) = t * Real.sqrt (1 - x ^ 2) := by
    rw [show t ^ 2 - (t * x) ^ 2 = t ^ 2 * (1 - x ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  rw [hs, show t + t * Real.sqrt (1 - x ^ 2) = t * (1 + Real.sqrt (1 - x ^ 2)) by ring,
    Real.log_mul ht.ne' (by positivity), Real.log_mul ht.ne' hx0.ne']
  ring

/-- `∫_0^1 x^n A(x,1) dx = J_n/(n+1)`, via the primitive
`(x^{n+1}(log(1+√(1-x²)) - log x) + ∫_0^{arcsin x} sin^n)/(n+1)`. -/
theorem arcsineExcess_moment (n : ℕ) :
    IntervalIntegrable (fun x => x ^ n * arcsineExcess x 1) volume 0 1 ∧
    ∫ x in (0 : ℝ)..1, x ^ n * arcsineExcess x 1 = wallisJ n / (n + 1) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  set S : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, Real.sin v ^ n with hS
  have hSd : ∀ u, HasDerivAt S (Real.sin u ^ n) u := fun u =>
    ((by fun_prop : Continuous fun v => Real.sin v ^ n).integral_hasStrictDerivAt 0 u).hasDerivAt
  have hScont : Continuous S := continuous_iff_continuousAt.2 fun u => (hSd u).continuousAt
  set G : ℝ → ℝ := fun x => (x ^ (n + 1) * Real.log (1 + Real.sqrt (1 - x ^ 2)) -
    x ^ (n + 1) * Real.log x + S (Real.arcsin x)) / (n + 1) with hG
  have hcont : Continuous G := by
    have h1 : Continuous fun x : ℝ => x ^ (n + 1) * Real.log (1 + Real.sqrt (1 - x ^ 2)) :=
      (continuous_pow _).mul (Continuous.log (by fun_prop) fun x => by positivity)
    have h2 : Continuous fun x : ℝ => x ^ (n + 1) * Real.log x := by
      have : (fun x : ℝ => x ^ (n + 1) * Real.log x) = fun x => x ^ n * (x * Real.log x) := by
        funext x; ring
      rw [this]
      exact (continuous_pow n).mul Real.continuous_mul_log
    exact ((h1.sub h2).add (hScont.comp Real.continuous_arcsin)).div_const _
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (x ^ n * arcsineExcess x 1) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h1x : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    set s := Real.sqrt (1 - x ^ 2) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr h1x
    have hs2 : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt h1x.le
    have hsq : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2)) (-x / s) x := by
      have := ((hasDerivAt_pow 2 x).const_sub 1).sqrt h1x.ne'
      convert this using 1
      rw [← hs]; field_simp; norm_num; ring
    have hlog1 : HasDerivAt (fun y : ℝ => Real.log (1 + Real.sqrt (1 - y ^ 2)))
        ((-x / s) / (1 + s)) x :=
      (hsq.const_add 1).log (by positivity)
    have hp : HasDerivAt (fun y : ℝ => y ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * x ^ n) x := by
      simpa using hasDerivAt_pow (n + 1) x
    have harc : HasDerivAt Real.arcsin (1 / s) x := by
      have := Real.hasDerivAt_arcsin (x := x) (by linarith [hx.1]) hx.2.ne
      simpa [hs] using this
    have hSa : HasDerivAt (fun y => S (Real.arcsin y)) (Real.sin (Real.arcsin x) ^ n * (1 / s)) x :=
      (hSd (Real.arcsin x)).comp x harc
    have htot := (((hp.mul hlog1).sub (hp.mul (Real.hasDerivAt_log hx0))).add hSa).div_const
      ((n : ℝ) + 1)
    refine htot.congr_deriv ?_
    rw [Real.sin_arcsin (by linarith [hx.1]) hx.2.le, arcsineExcess_one hx.2.le, ← hs]
    have key : x ^ (n + 1) * (-x / s / (1 + s)) - x ^ (n + 1) * x⁻¹ + x ^ n * (1 / s) = 0 := by
      have h1s : 1 + s ≠ 0 := by positivity
      field_simp
      linear_combination (-(x * x ^ n)) * hs2
    rw [div_eq_iff hn]
    push_cast
    linear_combination key
  have hnn : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ x ^ n * arcsineExcess x 1 := fun x hx =>
    mul_nonneg (pow_nonneg hx.1.le n) (arcsineExcess_nonneg hx.1)
  obtain ⟨hi, hint⟩ :=
    intervalIntegrable_and_integral_eq_of_deriv_nonneg zero_le_one hcont.continuousOn hderiv hnn
  refine ⟨hi, ?_⟩
  rw [hint, hG]
  simp only [one_pow, sub_self, Real.sqrt_zero, add_zero, Real.log_one, mul_zero,
    Real.arcsin_one, zero_pow (Nat.succ_ne_zero n), zero_mul, Real.arcsin_zero, hS,
    intervalIntegral.integral_same, zero_div, sub_zero, zero_add]
  rw [wallisJ_eq_sin]

/-- **The Abel identity**, normalized form: `∫_0^1 A(x,1) h(t x) dx = -log(1-t)/(2t)`. -/
theorem integral_arcsineExcess_mul_recoveryDensity_scaled {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ x in (0 : ℝ)..1, arcsineExcess x 1 * recoveryDensity (t * x) =
      -Real.log (1 - t) / (2 * t) := by
  have hmom := arcsineExcess_moment
  have hval : ∀ n : ℕ, ∫ x in (0 : ℝ)..1,
      arcsineExcess x 1 * (recoveryDensityCoeff n * (t * x) ^ n) = t ^ n / (2 * (n + 1)) :=
      fun n => by
    have : (fun x => arcsineExcess x 1 * (recoveryDensityCoeff n * (t * x) ^ n)) =
        fun x => (recoveryDensityCoeff n * t ^ n) * (x ^ n * arcsineExcess x 1) := by
      funext x; rw [mul_pow]; ring
    rw [this, intervalIntegral.integral_const_mul, (hmom n).2, recoveryDensityCoeff]
    have hw := wallisJ_mul n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hπ := Real.pi_pos.ne'
    field_simp
    linear_combination 2 * hw
  have hnorm : ∀ n : ℕ, ∫ x in (0 : ℝ)..1,
      ‖arcsineExcess x 1 * (recoveryDensityCoeff n * (t * x) ^ n)‖ = t ^ n / (2 * (n + 1)) :=
      fun n => by
    rw [← hval]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (arcsineExcess_nonneg hx.1)
      (mul_nonneg (recoveryDensityCoeff_nonneg n) (pow_nonneg (mul_nonneg ht0.le hx.1.le) n)))]
  have hlog : HasSum (fun n : ℕ => t ^ n / (2 * (n + 1))) (-Real.log (1 - t) / (2 * t)) := by
    have := (Real.hasSum_pow_div_log_of_abs_lt_one (x := t)
      (by rw [abs_of_pos ht0]; exact ht1)).div_const (2 * t)
    refine this.congr_fun fun n => ?_
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have h := hasSum_intervalIntegral_of_summable_norm
    (f := fun n x => arcsineExcess x 1 * (recoveryDensityCoeff n * (t * x) ^ n)) zero_le_one
    (fun n => by
      have := (hmom n).1.const_mul (recoveryDensityCoeff n * t ^ n)
      convert this using 1; funext x; rw [mul_pow]; ring)
    (by simpa only [hnorm] using hlog.summable)
  simp only [hval] at h
  have e : ∫ x in (0 : ℝ)..1, ∑' n, arcsineExcess x 1 * (recoveryDensityCoeff n * (t * x) ^ n) =
      ∫ x in (0 : ℝ)..1, arcsineExcess x 1 * recoveryDensity (t * x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [recoveryDensity]
    exact tsum_mul_left
  rw [e] at h
  exact h.unique hlog

/-- **The Abel identity** `∫_0^t A(a,t) h(a) da = -log(1-t)/2` for `0 < t < 1`: the mixture of
arcsine laws with density `h` balances the field `-½ log(1-t)` on its support. -/
theorem integral_arcsineExcess_mul_recoveryDensity {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ a in (0 : ℝ)..t, arcsineExcess a t * recoveryDensity a = -Real.log (1 - t) / 2 := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun a => arcsineExcess a t * recoveryDensity a) ht0.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  have e : ∫ x in (0 : ℝ)..1, arcsineExcess (t * x) t * recoveryDensity (t * x) =
      ∫ x in (0 : ℝ)..1, arcsineExcess x 1 * recoveryDensity (t * x) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le zero_le_one] at hx
    rw [arcsineExcess_scale ht0 hx.1 hx.2]
  rw [e, integral_arcsineExcess_mul_recoveryDensity_scaled ht0 ht1] at h
  have ht := ht0.ne'
  field_simp at h
  linarith

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
