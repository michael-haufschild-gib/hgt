import Mathlib.Probability.Distributions.Poisson.Basic
import GaloisForLFunctions.HTGeometry.CountableRelativeEntropyValue
import GaloisForLFunctions.HTGeometry.ConstitutiveApertureInformationProjection

/-!
# Poisson occupancy split: relative entropy of the count, the occupancy and the excess history

A Poisson formation of rate `x` splits into a Boolean occupancy report of parameter
`1 - e^{-x}` and, conditionally on nonvacuum, an excess-count history with masses
`x^{n+1}/((n+1)!(e^x-1))`.  This module computes the exact relative entropy of the Poisson count
law and of the excess-count law from the countable atom series.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

/-! ## Exponential series moments -/

/-- The exponential series. -/
theorem hasSum_pow_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x

/-- The first moment of the exponential series. -/
theorem hasSum_nat_mul_pow_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (x ^ n / (n.factorial : ℝ))) (x * Real.exp x) := by
  have hbase : HasSum (fun n : ℕ => x * (x ^ n / (n.factorial : ℝ))) (x * Real.exp x) :=
    (hasSum_pow_div_factorial x).mul_left x
  have hshift : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℝ) * (x ^ (n + 1) / ((n + 1).factorial : ℝ))
        = x * (x ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [Nat.factorial_succ]
    push_cast
    have hn : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    field_simp
    ring
  have hsucc : HasSum (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * (x ^ (n + 1) / ((n + 1).factorial : ℝ))) (x * Real.exp x) := by
    simpa only [hshift] using hbase
  have := (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) * (x ^ n / (n.factorial : ℝ))) 1).1
    (by simpa using hsucc)
  simpa using this

/-- The excess-count series: shifting the exponential series removes the vacuum atom. -/
theorem hasSum_pow_succ_div_factorial_succ (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (n + 1) / (((n + 1).factorial : ℕ) : ℝ)) (Real.exp x - 1) := by
  have h := (hasSum_nat_add_iff' (f := fun n : ℕ => x ^ n / (n.factorial : ℝ)) 1).2
    (hasSum_pow_div_factorial x)
  simpa using h

/-- The first moment of the excess-count series. -/
theorem hasSum_succ_mul_pow_succ_div_factorial_succ (x : ℝ) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * (x ^ (n + 1) / (((n + 1).factorial : ℕ) : ℝ)))
      (x * Real.exp x) := by
  have h := (hasSum_nat_add_iff'
    (f := fun n : ℕ => (n : ℝ) * (x ^ n / (n.factorial : ℝ))) 1).2
    (hasSum_nat_mul_pow_div_factorial x)
  simpa using h

/-! ## Affine atom series -/

/-- An affine observable is absolutely summable against a summable weight with a first moment. -/
theorem summable_weight_mul_abs_affine {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hw : Summable w)
    (hwn : Summable fun n => w n * (n : ℝ)) (c d : ℝ) :
    Summable fun n => w n * |c + d * (n : ℝ)| := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hw0 n) (abs_nonneg _)) (fun n => ?_)
    ((hw.mul_right |c|).add ((hwn.mul_left |d|)))
  calc w n * |c + d * (n : ℝ)| ≤ w n * (|c| + |d| * (n : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (hw0 n)
        calc |c + d * (n : ℝ)| ≤ |c| + |d * (n : ℝ)| := abs_add_le _ _
          _ = |c| + |d| * (n : ℝ) := by rw [abs_mul, Nat.abs_cast]
    _ = w n * |c| + |d| * (w n * (n : ℝ)) := by ring

/-- The atom series of an affine observable. -/
theorem hasSum_weight_mul_affine {w : ℕ → ℝ} {S M : ℝ} (hw : HasSum w S)
    (hwn : HasSum (fun n => w n * (n : ℝ)) M) (c d : ℝ) :
    HasSum (fun n => w n * (c + d * (n : ℝ))) (c * S + d * M) := by
  have h := (hw.mul_right c).add (hwn.mul_left d)
  have heq : (fun n => w n * (c + d * (n : ℝ))) = fun n => w n * c + d * (w n * (n : ℝ)) := by
    funext n; ring
  rw [heq, show c * S + d * M = S * c + d * M from by ring]
  exact h

/-! ## Relative entropy of Poisson count laws -/

theorem poissonMeasure_singleton_toReal (r : ℝ≥0) (n : ℕ) :
    (Po(r) {n}).toReal = Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) := by
  rw [poissonMeasure_singleton, ENNReal.toReal_ofReal (by positivity)]

theorem poissonMeasure_singleton_ne_zero {r : ℝ≥0} (hr : 0 < r) (n : ℕ) : Po(r) {n} ≠ 0 := by
  have hr' : (0 : ℝ) < (r : ℝ) := hr
  rw [poissonMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

/-- The Poisson mean, read off the atom series. -/
theorem hasSum_poissonMeasure_mean (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Po(r) {n}).toReal * (n : ℝ)) (r : ℝ) := by
  have hbase := (hasSum_nat_mul_pow_div_factorial (r : ℝ)).mul_left (Real.exp (-(r : ℝ)))
  have hval : Real.exp (-(r : ℝ)) * ((r : ℝ) * Real.exp (r : ℝ)) = (r : ℝ) := by
    rw [show Real.exp (-(r : ℝ)) * ((r : ℝ) * Real.exp (r : ℝ))
      = (r : ℝ) * (Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ))) from by ring, ← Real.exp_add]
    simp
  rw [hval] at hbase
  refine hbase.congr_fun fun n => ?_
  rw [poissonMeasure_singleton_toReal]
  ring

theorem log_poissonMeasure_singleton_ratio {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Real.log ((Po(a) {n}).toReal / (Po(b) {n}).toReal)
      = ((b : ℝ) - (a : ℝ)) + (n : ℝ) * Real.log ((a : ℝ) / (b : ℝ)) := by
  have ha' : (0 : ℝ) < (a : ℝ) := ha
  have hb' : (0 : ℝ) < (b : ℝ) := hb
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  rw [poissonMeasure_singleton_toReal, poissonMeasure_singleton_toReal]
  rw [show Real.exp (-(a : ℝ)) * (a : ℝ) ^ n / (n.factorial : ℝ) /
      (Real.exp (-(b : ℝ)) * (b : ℝ) ^ n / (n.factorial : ℝ))
      = (Real.exp (-(a : ℝ)) / Real.exp (-(b : ℝ))) * ((a : ℝ) / (b : ℝ)) ^ n from by
    rw [div_pow]
    field_simp]
  rw [Real.log_mul (by positivity) (by positivity), ← Real.exp_sub, Real.log_exp,
    Real.log_pow]
  ring

theorem summable_poisson_abs_logRatio {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    Summable fun n : ℕ => (Po(a) {n}).toReal *
      |Real.log ((Po(a) {n}).toReal / (Po(b) {n}).toReal)| := by
  have hrw : (fun n : ℕ => (Po(a) {n}).toReal *
      |Real.log ((Po(a) {n}).toReal / (Po(b) {n}).toReal)|)
      = fun n : ℕ => (Po(a) {n}).toReal *
        |((b : ℝ) - (a : ℝ)) + Real.log ((a : ℝ) / (b : ℝ)) * (n : ℝ)| := by
    funext n
    rw [log_poissonMeasure_singleton_ratio ha hb n, mul_comm ((n : ℝ))]
  rw [hrw]
  refine summable_weight_mul_abs_affine (fun n => ENNReal.toReal_nonneg) ?_
    (hasSum_poissonMeasure_mean a).summable _ _
  refine (hasSum_one_poissonMeasure a).summable.congr fun n => ?_
  rw [poissonMeasure_singleton_toReal]

/-- **Poisson relative entropy.** -/
theorem toReal_klDiv_poissonMeasure {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    (klDiv Po(a) Po(b)).toReal
      = ((b : ℝ) - (a : ℝ)) + (a : ℝ) * Real.log ((a : ℝ) / (b : ℝ)) := by
  have hw : HasSum (fun n : ℕ => (Po(a) {n}).toReal) 1 := by
    refine (hasSum_one_poissonMeasure a).congr_fun fun n => ?_
    rw [poissonMeasure_singleton_toReal]
  rw [toReal_klDiv_of_countable (fun n => poissonMeasure_singleton_ne_zero hb n)
    (summable_poisson_abs_logRatio ha hb)]
  have hval := (hasSum_weight_mul_affine hw (hasSum_poissonMeasure_mean a)
    ((b : ℝ) - (a : ℝ)) (Real.log ((a : ℝ) / (b : ℝ)))).tsum_eq
  rw [show (fun n : ℕ => (Po(a) {n}).toReal *
      Real.log ((Po(a) {n}).toReal / (Po(b) {n}).toReal))
      = fun n : ℕ => (Po(a) {n}).toReal *
        (((b : ℝ) - (a : ℝ)) + Real.log ((a : ℝ) / (b : ℝ)) * (n : ℝ)) from by
    funext n
    rw [log_poissonMeasure_singleton_ratio ha hb n, mul_comm ((n : ℝ))], hval]
  ring

theorem klDiv_poissonMeasure_ne_top {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    klDiv Po(a) Po(b) ≠ ⊤ :=
  klDiv_ne_top_of_summable_log_singleton_ratio
    (fun n => poissonMeasure_singleton_ne_zero hb n) (summable_poisson_abs_logRatio ha hb)

/-! ## The excess-count history law -/

/-- Excess-count mass of a Poisson formation of rate `x`, conditional on nonvacuum. -/
def excessCountWeight (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 1) / (((n + 1).factorial : ℝ) * (Real.exp x - 1))

/-- The excess-count history law of a Poisson formation of rate `x`. -/
def excessCountMeasure (x : ℝ) : Measure ℕ :=
  Measure.sum fun n => ENNReal.ofReal (excessCountWeight x n) • Measure.dirac n

theorem exp_sub_one_pos {x : ℝ} (hx : 0 < x) : 0 < Real.exp x - 1 := by
  have := Real.add_one_lt_exp hx.ne'
  linarith

theorem excessCountWeight_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < excessCountWeight x n := by
  have h := exp_sub_one_pos hx
  rw [excessCountWeight]
  positivity

theorem hasSum_excessCountWeight {x : ℝ} (hx : 0 < x) : HasSum (excessCountWeight x) 1 := by
  have h1 := exp_sub_one_pos hx
  have h := (hasSum_pow_succ_div_factorial_succ x).div_const (Real.exp x - 1)
  rw [div_self h1.ne'] at h
  refine h.congr_fun fun n => ?_
  rw [excessCountWeight, div_div]

theorem isProbabilityMeasure_excessCountMeasure {x : ℝ} (hx : 0 < x) :
    IsProbabilityMeasure (excessCountMeasure x) :=
  (hasSum_excessCountWeight hx).isProbabilityMeasure_sum_dirac
    fun n => (excessCountWeight_pos hx n).le

theorem excessCountMeasure_singleton (x : ℝ) (n : ℕ) :
    excessCountMeasure x {n} = ENNReal.ofReal (excessCountWeight x n) := by
  rw [excessCountMeasure, Measure.sum_smul_dirac_singleton]

theorem excessCountMeasure_singleton_toReal {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (excessCountMeasure x {n}).toReal = excessCountWeight x n := by
  rw [excessCountMeasure_singleton, ENNReal.toReal_ofReal (excessCountWeight_pos hx n).le]

theorem excessCountMeasure_singleton_ne_zero {x : ℝ} (hx : 0 < x) (n : ℕ) :
    excessCountMeasure x {n} ≠ 0 := by
  rw [excessCountMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact excessCountWeight_pos hx n

/-- The excess-count first moment. -/
theorem hasSum_excessCountWeight_mul_nat {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => excessCountWeight x n * (n : ℝ))
      (x * Real.exp x / (Real.exp x - 1) - 1) := by
  have h1 := exp_sub_one_pos hx
  have hsucc : HasSum (fun n : ℕ => ((n : ℝ) + 1) * excessCountWeight x n)
      (x * Real.exp x / (Real.exp x - 1)) := by
    refine ((hasSum_succ_mul_pow_succ_div_factorial_succ x).div_const
      (Real.exp x - 1)).congr_fun fun n => ?_
    rw [excessCountWeight]
    field_simp
  refine (hsucc.sub (hasSum_excessCountWeight hx)).congr_fun fun n => ?_
  ring

theorem log_excessCountMeasure_singleton_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Real.log ((excessCountMeasure a {n}).toReal / (excessCountMeasure b {n}).toReal)
      = (Real.log (a / b) + Real.log ((Real.exp b - 1) / (Real.exp a - 1)))
        + Real.log (a / b) * (n : ℝ) := by
  have hea := exp_sub_one_pos ha
  have heb := exp_sub_one_pos hb
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  rw [excessCountMeasure_singleton_toReal ha, excessCountMeasure_singleton_toReal hb,
    excessCountWeight, excessCountWeight]
  rw [show a ^ (n + 1) / (((n + 1).factorial : ℝ) * (Real.exp a - 1)) /
      (b ^ (n + 1) / (((n + 1).factorial : ℝ) * (Real.exp b - 1)))
      = (a / b) ^ (n + 1) * ((Real.exp b - 1) / (Real.exp a - 1)) from by
    rw [div_pow]
    field_simp]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

theorem summable_excessCount_abs_logRatio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Summable fun n : ℕ => (excessCountMeasure a {n}).toReal *
      |Real.log ((excessCountMeasure a {n}).toReal / (excessCountMeasure b {n}).toReal)| := by
  have hrw : (fun n : ℕ => (excessCountMeasure a {n}).toReal *
      |Real.log ((excessCountMeasure a {n}).toReal / (excessCountMeasure b {n}).toReal)|)
      = fun n : ℕ => excessCountWeight a n *
        |(Real.log (a / b) + Real.log ((Real.exp b - 1) / (Real.exp a - 1)))
          + Real.log (a / b) * (n : ℝ)| := by
    funext n
    rw [log_excessCountMeasure_singleton_ratio ha hb n, excessCountMeasure_singleton_toReal ha]
  rw [hrw]
  exact summable_weight_mul_abs_affine (fun n => (excessCountWeight_pos ha n).le)
    (hasSum_excessCountWeight ha).summable (hasSum_excessCountWeight_mul_nat ha).summable _ _

/-- **Excess-count relative entropy.** -/
theorem toReal_klDiv_excessCountMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (klDiv (excessCountMeasure a) (excessCountMeasure b)).toReal
      = a * Real.exp a / (Real.exp a - 1) * Real.log (a / b)
        + Real.log ((Real.exp b - 1) / (Real.exp a - 1)) := by
  haveI := isProbabilityMeasure_excessCountMeasure ha
  haveI := isProbabilityMeasure_excessCountMeasure hb
  rw [toReal_klDiv_of_countable (fun n => excessCountMeasure_singleton_ne_zero hb n)
    (summable_excessCount_abs_logRatio ha hb)]
  have hw : HasSum (fun n : ℕ => (excessCountMeasure a {n}).toReal) 1 := by
    refine (hasSum_excessCountWeight ha).congr_fun fun n => ?_
    rw [excessCountMeasure_singleton_toReal ha]
  have hwn : HasSum (fun n : ℕ => (excessCountMeasure a {n}).toReal * (n : ℝ))
      (a * Real.exp a / (Real.exp a - 1) - 1) := by
    refine (hasSum_excessCountWeight_mul_nat ha).congr_fun fun n => ?_
    rw [excessCountMeasure_singleton_toReal ha]
  have hval := (hasSum_weight_mul_affine hw hwn
    (Real.log (a / b) + Real.log ((Real.exp b - 1) / (Real.exp a - 1)))
    (Real.log (a / b))).tsum_eq
  rw [show (fun n : ℕ => (excessCountMeasure a {n}).toReal *
      Real.log ((excessCountMeasure a {n}).toReal / (excessCountMeasure b {n}).toReal))
      = fun n : ℕ => (excessCountMeasure a {n}).toReal *
        ((Real.log (a / b) + Real.log ((Real.exp b - 1) / (Real.exp a - 1)))
          + Real.log (a / b) * (n : ℝ)) from by
    funext n
    rw [log_excessCountMeasure_singleton_ratio ha hb n], hval]
  ring

theorem klDiv_excessCountMeasure_ne_top {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    klDiv (excessCountMeasure a) (excessCountMeasure b) ≠ ⊤ := by
  haveI := isProbabilityMeasure_excessCountMeasure ha
  haveI := isProbabilityMeasure_excessCountMeasure hb
  exact klDiv_ne_top_of_summable_log_singleton_ratio
    (fun n => excessCountMeasure_singleton_ne_zero hb n) (summable_excessCount_abs_logRatio ha hb)

/-! ## The occupancy--history chain rule -/

/-- Boolean occupancy parameter of a Poisson formation of rate `x`. -/
def poissonOccupancyUnit (x : ℝ≥0) : unitInterval :=
  ⟨1 - Real.exp (-(x : ℝ)), by
    constructor
    · have : Real.exp (-(x : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
      linarith
    · have := Real.exp_pos (-(x : ℝ))
      linarith⟩

@[simp] theorem coe_poissonOccupancyUnit (x : ℝ≥0) :
    (poissonOccupancyUnit x : ℝ) = 1 - Real.exp (-(x : ℝ)) := rfl

theorem coe_poissonOccupancyUnit_pos {x : ℝ≥0} (hx : 0 < x) :
    0 < (poissonOccupancyUnit x : ℝ) := by
  have hx' : (0 : ℝ) < (x : ℝ) := hx
  have : Real.exp (-(x : ℝ)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  simpa using this

theorem coe_poissonOccupancyUnit_lt_one (x : ℝ≥0) : (poissonOccupancyUnit x : ℝ) < 1 := by
  have := Real.exp_pos (-(x : ℝ))
  simpa using this

/-- Boolean occupancy report of a Poisson formation. -/
def occupancyReport (x : ℝ≥0) : Measure Bool := Ber(true, false, poissonOccupancyUnit x)

instance isProbabilityMeasure_occupancyReport (x : ℝ≥0) :
    IsProbabilityMeasure (occupancyReport x) := by
  rw [occupancyReport]
  infer_instance

/-- **Exact occupancy--history chain rule.**  The relative entropy of two Poisson count laws is the
relative entropy of their Boolean occupancy reports plus the occupancy-weighted relative entropy of
their excess-count histories. -/
theorem toReal_klDiv_poissonMeasure_eq_occupancy_add_history {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    (klDiv Po(a) Po(b)).toReal
      = (klDiv (occupancyReport a) (occupancyReport b)).toReal
        + (poissonOccupancyUnit a : ℝ) *
          (klDiv (excessCountMeasure a) (excessCountMeasure b)).toReal := by
  have ha' : (0 : ℝ) < (a : ℝ) := ha
  have hb' : (0 : ℝ) < (b : ℝ) := hb
  have hea := exp_sub_one_pos ha'
  have heb := exp_sub_one_pos hb'
  have hexpa := Real.exp_pos ((a : ℝ))
  have hexpb := Real.exp_pos ((b : ℝ))
  have hqa := coe_poissonOccupancyUnit_pos ha
  have hqb := coe_poissonOccupancyUnit_pos hb
  have hnegA : Real.exp (-(a : ℝ)) = (Real.exp (a : ℝ))⁻¹ := by
    rw [Real.exp_neg]
  have hnegB : Real.exp (-(b : ℝ)) = (Real.exp (b : ℝ))⁻¹ := by
    rw [Real.exp_neg]
  rw [occupancyReport, occupancyReport,
    toReal_klDiv_bernoulli_baseline_interior _ _ hqb (coe_poissonOccupancyUnit_lt_one b),
    toReal_klDiv_poissonMeasure ha hb, toReal_klDiv_excessCountMeasure ha' hb']
  -- the complementary occupancy log
  have hcomp : Real.log ((1 - (poissonOccupancyUnit a : ℝ)) / (1 - (poissonOccupancyUnit b : ℝ)))
      = (b : ℝ) - (a : ℝ) := by
    simp only [coe_poissonOccupancyUnit, sub_sub_cancel]
    rw [← Real.exp_sub, Real.log_exp]
    ring
  -- the occupancy log
  have hocc : Real.log ((poissonOccupancyUnit a : ℝ) / (poissonOccupancyUnit b : ℝ))
      = Real.log ((Real.exp (a : ℝ) - 1) / (Real.exp (b : ℝ) - 1)) + ((b : ℝ) - (a : ℝ)) := by
    have hsplit : (poissonOccupancyUnit a : ℝ) / (poissonOccupancyUnit b : ℝ)
        = ((Real.exp (a : ℝ) - 1) / (Real.exp (b : ℝ) - 1)) * Real.exp ((b : ℝ) - (a : ℝ)) := by
      simp only [coe_poissonOccupancyUnit, hnegA, hnegB]
      rw [Real.exp_sub]
      field_simp
    rw [hsplit, Real.log_mul (by positivity) (by positivity), Real.log_exp]
  -- the two cancelling history logs
  have hcancel : Real.log ((Real.exp (b : ℝ) - 1) / (Real.exp (a : ℝ) - 1))
      = -Real.log ((Real.exp (a : ℝ) - 1) / (Real.exp (b : ℝ) - 1)) := by
    rw [← Real.log_inv, inv_div]
  -- the occupancy-weighted virial
  have hvirial : (poissonOccupancyUnit a : ℝ) *
      ((a : ℝ) * Real.exp (a : ℝ) / (Real.exp (a : ℝ) - 1)) = (a : ℝ) := by
    simp only [coe_poissonOccupancyUnit, hnegA]
    field_simp
  rw [hcomp, hocc, hcancel]
  have hq1 : (poissonOccupancyUnit a : ℝ) + Real.exp (-(a : ℝ)) = 1 := by
    simp only [coe_poissonOccupancyUnit]
    ring
  have hexpand : (poissonOccupancyUnit a : ℝ) *
      ((a : ℝ) * Real.exp (a : ℝ) / (Real.exp (a : ℝ) - 1) *
          Real.log ((a : ℝ) / (b : ℝ)) +
        -Real.log ((Real.exp (a : ℝ) - 1) / (Real.exp (b : ℝ) - 1)))
      = (a : ℝ) * Real.log ((a : ℝ) / (b : ℝ))
        - (poissonOccupancyUnit a : ℝ) *
          Real.log ((Real.exp (a : ℝ) - 1) / (Real.exp (b : ℝ) - 1)) := by
    rw [mul_add, ← mul_assoc, hvirial]
    ring
  rw [hexpand]
  simp only [coe_poissonOccupancyUnit]
  ring

/-! ## Extensive formation conservation -/

/-- Jeffreys divergence of two Poisson count laws. -/
def poissonJeffreys (a b : ℝ≥0) : ℝ :=
  (klDiv Po(a) Po(b)).toReal + (klDiv Po(b) Po(a)).toReal

/-- Jeffreys divergence of the two Boolean occupancy reports. -/
def booleanOccupancyJeffreys (a b : ℝ≥0) : ℝ :=
  (klDiv (occupancyReport a) (occupancyReport b)).toReal +
    (klDiv (occupancyReport b) (occupancyReport a)).toReal

/-- Vertical history action: occupancy-weighted symmetrized excess-count relative entropy. -/
def hiddenHistoryWork (a b : ℝ≥0) : ℝ :=
  (poissonOccupancyUnit a : ℝ) * (klDiv (excessCountMeasure a) (excessCountMeasure b)).toReal +
    (poissonOccupancyUnit b : ℝ) * (klDiv (excessCountMeasure b) (excessCountMeasure a)).toReal

theorem poissonJeffreys_eq {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    poissonJeffreys a b = ((a : ℝ) - (b : ℝ)) * Real.log ((a : ℝ) / (b : ℝ)) := by
  have ha' : (0 : ℝ) < (a : ℝ) := ha
  have hb' : (0 : ℝ) < (b : ℝ) := hb
  rw [poissonJeffreys, toReal_klDiv_poissonMeasure ha hb, toReal_klDiv_poissonMeasure hb ha,
    Real.log_div hb'.ne' ha'.ne', Real.log_div ha'.ne' hb'.ne']
  ring

/-- **Extensive formation conservation.**  Poisson Jeffreys information is exactly the Boolean
occupancy work plus the vertical history action. -/
theorem poissonJeffreys_eq_boolean_add_hidden {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    poissonJeffreys a b = booleanOccupancyJeffreys a b + hiddenHistoryWork a b := by
  rw [poissonJeffreys, booleanOccupancyJeffreys, hiddenHistoryWork,
    toReal_klDiv_poissonMeasure_eq_occupancy_add_history ha hb,
    toReal_klDiv_poissonMeasure_eq_occupancy_add_history hb ha]
  ring

/-- The exact Boolean occupancy work of two Poisson formations. -/
theorem booleanOccupancyJeffreys_eq {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    booleanOccupancyJeffreys a b
      = (Real.exp (-(b : ℝ)) - Real.exp (-(a : ℝ))) *
        Real.log ((Real.exp (a : ℝ) - 1) / (Real.exp (b : ℝ) - 1)) := by
  have ha' : (0 : ℝ) < (a : ℝ) := ha
  have hb' : (0 : ℝ) < (b : ℝ) := hb
  have hea := exp_sub_one_pos ha'
  have heb := exp_sub_one_pos hb'
  have hqa := coe_poissonOccupancyUnit_pos ha
  have hqb := coe_poissonOccupancyUnit_pos hb
  have hnegA : Real.exp (-(a : ℝ)) = (Real.exp (a : ℝ))⁻¹ := Real.exp_neg _
  have hnegB : Real.exp (-(b : ℝ)) = (Real.exp (b : ℝ))⁻¹ := Real.exp_neg _
  have hocc : ∀ u v : ℝ≥0, 0 < (u : ℝ) → 0 < (v : ℝ) →
      Real.log ((poissonOccupancyUnit u : ℝ) / (poissonOccupancyUnit v : ℝ))
        = Real.log ((Real.exp (u : ℝ) - 1) / (Real.exp (v : ℝ) - 1)) + ((v : ℝ) - (u : ℝ)) := by
    intro u v hu hv
    have heu := exp_sub_one_pos hu
    have hev := exp_sub_one_pos hv
    have hsplit : (poissonOccupancyUnit u : ℝ) / (poissonOccupancyUnit v : ℝ)
        = ((Real.exp (u : ℝ) - 1) / (Real.exp (v : ℝ) - 1)) * Real.exp ((v : ℝ) - (u : ℝ)) := by
      simp only [coe_poissonOccupancyUnit, Real.exp_neg]
      rw [Real.exp_sub]
      field_simp
    rw [hsplit, Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hcomp : ∀ u v : ℝ≥0,
      Real.log ((1 - (poissonOccupancyUnit u : ℝ)) / (1 - (poissonOccupancyUnit v : ℝ)))
        = (v : ℝ) - (u : ℝ) := by
    intro u v
    simp only [coe_poissonOccupancyUnit, sub_sub_cancel]
    rw [← Real.exp_sub, Real.log_exp]
    ring
  rw [booleanOccupancyJeffreys, occupancyReport, occupancyReport,
    toReal_klDiv_bernoulli_baseline_interior _ _ hqb (coe_poissonOccupancyUnit_lt_one b),
    toReal_klDiv_bernoulli_baseline_interior _ _ hqa (coe_poissonOccupancyUnit_lt_one a),
    hocc a b ha' hb', hocc b a hb' ha', hcomp a b, hcomp b a]
  have hcancel : Real.log ((Real.exp (b : ℝ) - 1) / (Real.exp (a : ℝ) - 1))
      = -Real.log ((Real.exp (a : ℝ) - 1) / (Real.exp (b : ℝ) - 1)) := by
    rw [← Real.log_inv, inv_div]
  rw [hcancel]
  simp only [coe_poissonOccupancyUnit]
  ring

/-- The exact vertical history action of two Poisson formations. -/
theorem hiddenHistoryWork_eq {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    hiddenHistoryWork a b
      = ((a : ℝ) - (b : ℝ)) * Real.log ((a : ℝ) / (b : ℝ))
        - (Real.exp (-(b : ℝ)) - Real.exp (-(a : ℝ))) *
          Real.log ((Real.exp (a : ℝ) - 1) / (Real.exp (b : ℝ) - 1)) := by
  have h := poissonJeffreys_eq_boolean_add_hidden ha hb
  rw [poissonJeffreys_eq ha hb, booleanOccupancyJeffreys_eq ha hb] at h
  linarith

theorem booleanOccupancyJeffreys_nonneg (a b : ℝ≥0) : 0 ≤ booleanOccupancyJeffreys a b := by
  rw [booleanOccupancyJeffreys]
  positivity

theorem hiddenHistoryWork_nonneg (a b : ℝ≥0) : 0 ≤ hiddenHistoryWork a b := by
  rw [hiddenHistoryWork]
  have h1 : (0 : ℝ) ≤ (poissonOccupancyUnit a : ℝ) := (poissonOccupancyUnit a).2.1
  have h2 : (0 : ℝ) ≤ (poissonOccupancyUnit b : ℝ) := (poissonOccupancyUnit b).2.1
  positivity

/-- The excess-count history law determines the rate. -/
theorem excessCountMeasure_injOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : excessCountMeasure a = excessCountMeasure b) : a = b := by
  have h0 := congrArg (fun μ : Measure ℕ => (μ {0}).toReal) h
  have h1 := congrArg (fun μ : Measure ℕ => (μ {1}).toReal) h
  simp only [excessCountMeasure_singleton_toReal ha, excessCountMeasure_singleton_toReal hb,
    excessCountWeight] at h0 h1
  have hea := exp_sub_one_pos ha
  have heb := exp_sub_one_pos hb
  have hane : a ≠ 0 := ha.ne'
  have hbne : b ≠ 0 := hb.ne'
  norm_num [Nat.factorial] at h0 h1
  field_simp at h0 h1
  have hkey : (Real.exp a - 1) * b * (a - b) = 0 := by linear_combination h1 - a * h0
  rcases mul_eq_zero.1 hkey with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd h'' hea.ne'
    · exact absurd h'' hbne
  · linarith

/-- **Vertical history action vanishes exactly on the diagonal.** -/
theorem hiddenHistoryWork_eq_zero_iff {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    hiddenHistoryWork a b = 0 ↔ a = b := by
  have ha' : (0 : ℝ) < (a : ℝ) := ha
  have hb' : (0 : ℝ) < (b : ℝ) := hb
  haveI := isProbabilityMeasure_excessCountMeasure ha'
  haveI := isProbabilityMeasure_excessCountMeasure hb'
  constructor
  · intro h
    have hqa := coe_poissonOccupancyUnit_pos ha
    have hqb := coe_poissonOccupancyUnit_pos hb
    have hA : (0 : ℝ) ≤ (poissonOccupancyUnit a : ℝ) *
        (klDiv (excessCountMeasure a) (excessCountMeasure b)).toReal := by positivity
    have hB : (0 : ℝ) ≤ (poissonOccupancyUnit b : ℝ) *
        (klDiv (excessCountMeasure b) (excessCountMeasure a)).toReal := by positivity
    rw [hiddenHistoryWork] at h
    have hAzero : (klDiv (excessCountMeasure a) (excessCountMeasure b)).toReal = 0 := by
      have := le_antisymm (by linarith : (poissonOccupancyUnit a : ℝ) *
        (klDiv (excessCountMeasure a) (excessCountMeasure b)).toReal ≤ 0) hA
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' hqa.ne'
      · exact h'
    have hne : klDiv (excessCountMeasure a) (excessCountMeasure b) ≠ ⊤ :=
      klDiv_excessCountMeasure_ne_top ha' hb'
    have : klDiv (excessCountMeasure a) (excessCountMeasure b) = 0 := by
      rw [← ENNReal.ofReal_toReal hne, hAzero, ENNReal.ofReal_zero]
    have hmeas := klDiv_eq_zero_iff.1 this
    exact NNReal.coe_injective (excessCountMeasure_injOn ha' hb' hmeas)
  · rintro rfl
    simp [hiddenHistoryWork]

theorem booleanOccupancyJeffreys_symm (a b : ℝ≥0) :
    booleanOccupancyJeffreys a b = booleanOccupancyJeffreys b a := by
  rw [booleanOccupancyJeffreys, booleanOccupancyJeffreys]; ring

theorem hiddenHistoryWork_symm (a b : ℝ≥0) :
    hiddenHistoryWork a b = hiddenHistoryWork b a := by
  rw [hiddenHistoryWork, hiddenHistoryWork]; ring

@[simp] theorem booleanOccupancyJeffreys_self (a : ℝ≥0) : booleanOccupancyJeffreys a a = 0 := by
  simp [booleanOccupancyJeffreys, occupancyReport, klDiv_self]

@[simp] theorem hiddenHistoryWork_self (a : ℝ≥0) : hiddenHistoryWork a a = 0 := by
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ a from bot_le) with h | h
  · subst h
    simp [hiddenHistoryWork]
  · haveI := isProbabilityMeasure_excessCountMeasure (show (0:ℝ) < (a : ℝ) from h)
    simp [hiddenHistoryWork, klDiv_self]

end

end GaloisForLFunctions.HTGeometry
