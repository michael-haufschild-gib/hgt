import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.RHTower.VonMangoldtGammaJetBoundaryConvergence
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Sharp tempered-admission wall for the odd Euler comb

This file formalizes the literal logarithmic von Mangoldt atoms.  The positive half of the
odd comb is the atomic measure

`sum_{n >= 2} Lambda(n) n^{-b} delta_{log n}`.

Temperateness of an atomic Radon measure is expressed by mathlib's
`Measure.HasTemperateGrowth`: integrability of one inverse polynomial weight.  We prove its exact
threshold `b >= 1`, construct the admitted odd tempered distribution, and retain the locally finite
distribution for every real `b`.
-/

open Filter MeasureTheory Module Set TopologicalSpace Topology
open scoped Distributions ENNReal NNReal Real SchwartzMap

namespace HTGeometry

noncomputable section

/-- Literal coefficient `Lambda(n) n^{-b}`, written using the existing resolved coefficient
`Lambda(n)/n`.  The equality with the paper's formula is proved below for `n >= 2`. -/
def oddEulerWeight (b : ℝ) (n : ℕ) : ℝ :=
  RHTower.finiteVonMangoldtRealWeight n * (n : ℝ) ^ (1 - b)

theorem oddEulerWeight_nonneg (b : ℝ) (n : ℕ) : 0 ≤ oddEulerWeight b n := by
  exact mul_nonneg (RHTower.finiteVonMangoldtRealWeight_nonneg n)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem oddEulerWeight_eq_vonMangoldt_mul_rpow_neg
    (b : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    oddEulerWeight b n = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-b) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  rw [oddEulerWeight, RHTower.finiteVonMangoldtRealWeight]
  rw [div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ)]
  calc
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (1 - b) =
        ArithmeticFunction.vonMangoldt n *
          ((n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (1 - b)) := by
          ring
    _ = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ) + (1 - b)) := by
          rw [Real.rpow_add hn0]
    _ = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-b) := by ring_nf

/-- Positive logarithmic half of the odd Euler comb. -/
def oddEulerPositiveMeasure (b : ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (oddEulerWeight b n) • Measure.dirac (Real.log n)

/-- Negative logarithmic half, kept as a positive measure before taking the difference in `S'`. -/
def oddEulerNegativeMeasure (b : ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (oddEulerWeight b n) • Measure.dirac (-Real.log n)

/-- Sequence obtained by testing the positive atoms against the `k`-th inverse polynomial
weight on the logarithmic axis. -/
def oddEulerTemperedTerm (b : ℝ) (k n : ℕ) : ℝ :=
  oddEulerWeight b n * (1 + |Real.log n|) ^ (-(k : ℝ))

@[simp] theorem oddEulerTemperedTerm_zero (b : ℝ) (n : ℕ) :
    oddEulerTemperedTerm b 0 n = oddEulerWeight b n := by
  rw [oddEulerTemperedTerm]
  norm_num

theorem oddEulerTemperedTerm_zero_fun (b : ℝ) :
    oddEulerTemperedTerm b 0 = oddEulerWeight b := by
  funext n
  exact oddEulerTemperedTerm_zero b n

@[simp] theorem oddEulerWeight_one (n : ℕ) :
    oddEulerWeight 1 n = RHTower.finiteVonMangoldtRealWeight n := by
  rw [oddEulerWeight]
  norm_num

theorem oddEulerWeight_one_fun :
    oddEulerWeight 1 = RHTower.finiteVonMangoldtRealWeight := by
  funext n
  exact oddEulerWeight_one n

theorem oddEulerTemperedTerm_nonneg (b : ℝ) (k n : ℕ) :
    0 ≤ oddEulerTemperedTerm b k n := by
  exact mul_nonneg (oddEulerWeight_nonneg b n)
    (Real.rpow_nonneg (by positivity : 0 ≤ 1 + |Real.log n|) _)

/-- The harmonic von Mangoldt series diverges.  A prime residue-class subseries already diverges. -/
theorem not_summable_finiteVonMangoldtRealWeight :
    ¬ Summable RHTower.finiteVonMangoldtRealWeight := by
  intro hsum
  have hrestricted : Summable (fun n : ℕ =>
      (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 2) n else 0) /
        (n : ℝ)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hsum
    · intro n
      split_ifs
      · exact div_nonneg (ArithmeticFunction.vonMangoldt.residueClass_nonneg _ _)
          (Nat.cast_nonneg n)
      · norm_num
    · intro n
      split_ifs
      · exact div_le_div_of_nonneg_right
          (ArithmeticFunction.vonMangoldt.residueClass_le _ n) (Nat.cast_nonneg n)
      · simpa using RHTower.finiteVonMangoldtRealWeight_nonneg n
  exact ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div
    (q := 2) (a := (1 : ZMod 2)) isUnit_one hrestricted

/-- Every fixed power of `1 + |log x|` is eventually bounded by every positive power of `x`. -/
theorem eventually_one_add_abs_log_pow_le_rpow (k : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (1 + |Real.log x|) ^ k ≤ x ^ s := by
  have hs2 : 0 < s / 2 := by linarith
  have hlogRaw :=
    (isLittleO_log_rpow_rpow_atTop (k : ℝ) hs2).eventuallyLE
  have hconst : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ^ k ≤ x ^ (s / 2) :=
    (tendsto_rpow_atTop hs2).eventually (eventually_ge_atTop ((2 : ℝ) ^ k))
  filter_upwards [hlogRaw, hconst, eventually_ge_atTop (Real.exp 1)] with x hlog hconstx hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlogone : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hxpos hx
  have hlognonneg : 0 ≤ Real.log x := le_trans zero_le_one hlogone
  have hlogpow : Real.log x ^ k ≤ x ^ (s / 2) := by
    simpa [Real.norm_of_nonneg hlognonneg, Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _),
      Real.rpow_natCast] using hlog
  rw [abs_of_nonneg hlognonneg]
  calc
    (1 + Real.log x) ^ k ≤ (2 * Real.log x) ^ k := by
      gcongr
      linarith
    _ = (2 : ℝ) ^ k * Real.log x ^ k := by rw [mul_pow]
    _ ≤ x ^ (s / 2) * x ^ (s / 2) :=
      mul_le_mul hconstx hlogpow (pow_nonneg hlognonneg k)
        (Real.rpow_nonneg hxpos.le _)
    _ = x ^ s := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring

/-- Below the wall, no polynomial damping makes the logarithmic atom weights summable. -/
theorem not_summable_oddEulerTemperedTerm_of_lt_one
    {b : ℝ} (hb : b < 1) (k : ℕ) :
    ¬ Summable (oddEulerTemperedTerm b k) := by
  intro hsum
  have hs : 0 < 1 - b := sub_pos.mpr hb
  have hpolyReal := eventually_one_add_abs_log_pow_le_rpow k hs
  have hpolyNat : ∀ᶠ n : ℕ in atTop,
      (1 + |Real.log (n : ℝ)|) ^ k ≤ (n : ℝ) ^ (1 - b) :=
    tendsto_natCast_atTop_atTop.eventually hpolyReal
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖RHTower.finiteVonMangoldtRealWeight n‖ ≤ oddEulerTemperedTerm b k n := by
    filter_upwards [hpolyNat] with n hn
    have hbase : 0 < 1 + |Real.log (n : ℝ)| := by positivity
    have hfactor :
        1 ≤ (n : ℝ) ^ (1 - b) * (1 + |Real.log (n : ℝ)|) ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg hbase.le, Real.rpow_natCast]
      exact (le_div_iff₀ (pow_pos hbase k)).2 (by simpa using hn)
    have hweight := RHTower.finiteVonMangoldtRealWeight_nonneg n
    rw [Real.norm_of_nonneg hweight]
    calc
      RHTower.finiteVonMangoldtRealWeight n =
          RHTower.finiteVonMangoldtRealWeight n * 1 := by ring
      _ ≤ RHTower.finiteVonMangoldtRealWeight n *
          ((n : ℝ) ^ (1 - b) *
            (1 + |Real.log (n : ℝ)|) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left hfactor hweight
      _ = oddEulerTemperedTerm b k n := by
        rw [oddEulerTemperedTerm, oddEulerWeight]
        ring
  exact not_summable_finiteVonMangoldtRealWeight
    (hsum.of_norm_bounded_eventually_nat hbound)

/-- At and above the wall, cubic logarithmic damping is summable. -/
theorem summable_oddEulerTemperedTerm_three_of_one_le
    {b : ℝ} (hb : 1 ≤ b) :
    Summable (oddEulerTemperedTerm b 3) := by
  refine Summable.of_nonneg_of_le (oddEulerTemperedTerm_nonneg b 3) ?_
    (RHTower.summable_vonMangoldtInverseLogPowerWeight 0)
  intro n
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;>
      simp [oddEulerTemperedTerm, oddEulerWeight,
        RHTower.vonMangoldtInverseLogPowerWeight,
        RHTower.finiteVonMangoldtRealWeight]
  · have hncast : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hn)
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hncast
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hpow : (n : ℝ) ^ (1 - b) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hncast (by linarith)
    have hdamp :
        (1 + |Real.log (n : ℝ)|) ^ (-(3 : ℝ)) ≤
          Real.log (n : ℝ) ^ (-(3 : ℝ)) := by
      rw [abs_of_pos hlogpos]
      exact Real.rpow_le_rpow_of_nonpos hlogpos (by linarith) (by norm_num)
    rw [oddEulerTemperedTerm, oddEulerWeight,
      RHTower.vonMangoldtInverseLogPowerWeight]
    calc
      RHTower.finiteVonMangoldtRealWeight n * (n : ℝ) ^ (1 - b) *
          (1 + |Real.log (n : ℝ)|) ^ (-(3 : ℝ)) ≤
          RHTower.finiteVonMangoldtRealWeight n * 1 *
            Real.log (n : ℝ) ^ (-(3 : ℝ)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hpow
            (RHTower.finiteVonMangoldtRealWeight_nonneg n))
          hdamp (Real.rpow_nonneg (by positivity) _)
          (by simpa using RHTower.finiteVonMangoldtRealWeight_nonneg n)
      _ = RHTower.finiteVonMangoldtRealWeight n / Real.log (n : ℝ) ^ (0 + 3) := by
        rw [Real.rpow_neg hlogpos.le]
        simp [div_eq_mul_inv]

/-- Exact atomic integration criterion for the positive logarithmic comb. -/
theorem integrable_oddEulerPositiveMeasure_iff (b : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(k : ℝ))) (oddEulerPositiveMeasure b) ↔
      Summable (oddEulerTemperedTerm b k) := by
  rw [oddEulerPositiveMeasure,
    integrable_sum_dirac_iff (fun n : ℕ => ENNReal.ofReal_ne_top)]
  apply summable_congr
  intro n
  rw [ENNReal.toReal_ofReal (oddEulerWeight_nonneg b n)]
  simp only [Real.norm_eq_abs, oddEulerTemperedTerm]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

/-- Exact admission threshold for the positive half-measure. -/
theorem oddEulerPositiveMeasure_hasTemperateGrowth_iff (b : ℝ) :
    (oddEulerPositiveMeasure b).HasTemperateGrowth ↔ 1 ≤ b := by
  constructor
  · intro hgrowth
    by_contra hwall
    have hb : b < 1 := lt_of_not_ge hwall
    rcases hgrowth.exists_integrable with ⟨k, hk⟩
    exact not_summable_oddEulerTemperedTerm_of_lt_one hb k
      ((integrable_oddEulerPositiveMeasure_iff b k).1 hk)
  · intro hb
    exact ⟨⟨3, (integrable_oddEulerPositiveMeasure_iff b 3).2
      (summable_oddEulerTemperedTerm_three_of_one_le hb)⟩⟩

/-- Reflection does not change the polynomial-growth criterion. -/
theorem integrable_oddEulerNegativeMeasure_iff (b : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(k : ℝ))) (oddEulerNegativeMeasure b) ↔
      Summable (oddEulerTemperedTerm b k) := by
  rw [oddEulerNegativeMeasure,
    integrable_sum_dirac_iff (fun n : ℕ => ENNReal.ofReal_ne_top)]
  apply summable_congr
  intro n
  rw [ENNReal.toReal_ofReal (oddEulerWeight_nonneg b n)]
  simp only [Real.norm_eq_abs, oddEulerTemperedTerm, abs_neg]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

theorem oddEulerNegativeMeasure_hasTemperateGrowth_iff (b : ℝ) :
    (oddEulerNegativeMeasure b).HasTemperateGrowth ↔ 1 ≤ b := by
  constructor
  · intro hgrowth
    by_contra hwall
    have hb : b < 1 := lt_of_not_ge hwall
    rcases hgrowth.exists_integrable with ⟨k, hk⟩
    exact not_summable_oddEulerTemperedTerm_of_lt_one hb k
      ((integrable_oddEulerNegativeMeasure_iff b k).1 hk)
  · intro hb
    exact ⟨⟨3, (integrable_oddEulerNegativeMeasure_iff b 3).2
      (summable_oddEulerTemperedTerm_three_of_one_le hb)⟩⟩

/-- Positive half as an actual tempered distribution whenever `b` is admitted. -/
def oddEulerPositiveTemperedDistribution (b : ℝ) (hb : 1 ≤ b) :
    TemperedDistribution ℝ ℂ := by
  letI : (oddEulerPositiveMeasure b).HasTemperateGrowth :=
    (oddEulerPositiveMeasure_hasTemperateGrowth_iff b).2 hb
  exact (oddEulerPositiveMeasure b).toTemperedDistribution

/-- Reflected half as an actual tempered distribution whenever `b` is admitted. -/
def oddEulerNegativeTemperedDistribution (b : ℝ) (hb : 1 ≤ b) :
    TemperedDistribution ℝ ℂ := by
  letI : (oddEulerNegativeMeasure b).HasTemperateGrowth :=
    (oddEulerNegativeMeasure_hasTemperateGrowth_iff b).2 hb
  exact (oddEulerNegativeMeasure b).toTemperedDistribution

/-- Literal admitted odd Euler comb in `S'(R)`. -/
def oddEulerTemperedDistribution (b : ℝ) (hb : 1 ≤ b) :
    TemperedDistribution ℝ ℂ :=
  oddEulerPositiveTemperedDistribution b hb - oddEulerNegativeTemperedDistribution b hb

theorem oddEulerPositiveTemperedDistribution_apply
    (b : ℝ) (hb : 1 ≤ b) (f : SchwartzMap ℝ ℂ) :
    oddEulerPositiveTemperedDistribution b hb f =
      ∫ x, f x ∂oddEulerPositiveMeasure b := by
  letI : (oddEulerPositiveMeasure b).HasTemperateGrowth :=
    (oddEulerPositiveMeasure_hasTemperateGrowth_iff b).2 hb
  change (oddEulerPositiveMeasure b).toTemperedDistribution f = _
  exact Measure.toTemperedDistribution_apply _ _

theorem oddEulerNegativeTemperedDistribution_apply
    (b : ℝ) (hb : 1 ≤ b) (f : SchwartzMap ℝ ℂ) :
    oddEulerNegativeTemperedDistribution b hb f =
      ∫ x, f x ∂oddEulerNegativeMeasure b := by
  letI : (oddEulerNegativeMeasure b).HasTemperateGrowth :=
    (oddEulerNegativeMeasure_hasTemperateGrowth_iff b).2 hb
  change (oddEulerNegativeMeasure b).toTemperedDistribution f = _
  exact Measure.toTemperedDistribution_apply _ _

theorem oddEulerTemperedDistribution_apply
    (b : ℝ) (hb : 1 ≤ b) (f : SchwartzMap ℝ ℂ) :
    oddEulerTemperedDistribution b hb f =
      (∫ x, f x ∂oddEulerPositiveMeasure b) -
        ∫ x, f x ∂oddEulerNegativeMeasure b := by
  change oddEulerPositiveTemperedDistribution b hb f -
    oddEulerNegativeTemperedDistribution b hb f = _
  rw [
    oddEulerPositiveTemperedDistribution_apply,
    oddEulerNegativeTemperedDistribution_apply]

theorem oddEulerPositiveSchwartz_summable
    (b : ℝ) (hb : 1 ≤ b) (f : SchwartzMap ℝ ℂ) :
    Summable fun n : ℕ => (oddEulerWeight b n : ℂ) * f (Real.log n) := by
  letI : (oddEulerPositiveMeasure b).HasTemperateGrowth :=
    (oddEulerPositiveMeasure_hasTemperateGrowth_iff b).2 hb
  have hf : Integrable f (oddEulerPositiveMeasure b) := f.integrable
  rw [oddEulerPositiveMeasure] at hf
  have hnorm := (integrable_sum_dirac_iff
    (f := fun x : ℝ => f x)
    (c := fun n : ℕ => ENNReal.ofReal (oddEulerWeight b n))
    (x := fun n : ℕ => Real.log n)
    (fun _ => ENNReal.ofReal_ne_top)).1 hf
  apply Summable.of_norm
  convert hnorm using 1
  ext n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (oddEulerWeight_nonneg b n),
    ENNReal.toReal_ofReal (oddEulerWeight_nonneg b n)]

theorem oddEulerNegativeSchwartz_summable
    (b : ℝ) (hb : 1 ≤ b) (f : SchwartzMap ℝ ℂ) :
    Summable fun n : ℕ => (oddEulerWeight b n : ℂ) * f (-Real.log n) := by
  letI : (oddEulerNegativeMeasure b).HasTemperateGrowth :=
    (oddEulerNegativeMeasure_hasTemperateGrowth_iff b).2 hb
  have hf : Integrable f (oddEulerNegativeMeasure b) := f.integrable
  rw [oddEulerNegativeMeasure] at hf
  have hnorm := (integrable_sum_dirac_iff
    (f := fun x : ℝ => f x)
    (c := fun n : ℕ => ENNReal.ofReal (oddEulerWeight b n))
    (x := fun n : ℕ => -Real.log n)
    (fun _ => ENNReal.ofReal_ne_top)).1 hf
  apply Summable.of_norm
  convert hnorm using 1
  ext n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (oddEulerWeight_nonneg b n),
    ENNReal.toReal_ofReal (oddEulerWeight_nonneg b n)]

theorem integral_oddEulerPositiveMeasure_eq_tsum
    (b : ℝ) (hb : 1 ≤ b) (f : SchwartzMap ℝ ℂ) :
    ∫ x, f x ∂oddEulerPositiveMeasure b =
      ∑' n : ℕ, (oddEulerWeight b n : ℂ) * f (Real.log n) := by
  letI : (oddEulerPositiveMeasure b).HasTemperateGrowth :=
    (oddEulerPositiveMeasure_hasTemperateGrowth_iff b).2 hb
  have hf : Integrable f (oddEulerPositiveMeasure b) := f.integrable
  rw [oddEulerPositiveMeasure] at hf ⊢
  have hnorm := (integrable_sum_dirac_iff
    (f := fun x : ℝ => f x)
    (c := fun n : ℕ => ENNReal.ofReal (oddEulerWeight b n))
    (x := fun n : ℕ => Real.log n)
    (fun _ => ENNReal.ofReal_ne_top)).1 hf
  rw [integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) hnorm]
  apply tsum_congr
  intro n
  rw [ENNReal.toReal_ofReal (oddEulerWeight_nonneg b n)]
  simp

theorem integral_oddEulerNegativeMeasure_eq_tsum
    (b : ℝ) (hb : 1 ≤ b) (f : SchwartzMap ℝ ℂ) :
    ∫ x, f x ∂oddEulerNegativeMeasure b =
      ∑' n : ℕ, (oddEulerWeight b n : ℂ) * f (-Real.log n) := by
  letI : (oddEulerNegativeMeasure b).HasTemperateGrowth :=
    (oddEulerNegativeMeasure_hasTemperateGrowth_iff b).2 hb
  have hf : Integrable f (oddEulerNegativeMeasure b) := f.integrable
  rw [oddEulerNegativeMeasure] at hf ⊢
  have hnorm := (integrable_sum_dirac_iff
    (f := fun x : ℝ => f x)
    (c := fun n : ℕ => ENNReal.ofReal (oddEulerWeight b n))
    (x := fun n : ℕ => -Real.log n)
    (fun _ => ENNReal.ofReal_ne_top)).1 hf
  rw [integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) hnorm]
  apply tsum_congr
  intro n
  rw [ENNReal.toReal_ofReal (oddEulerWeight_nonneg b n)]
  simp

/-- Exact pairing with the paper's odd Dirac series. -/
theorem oddEulerTemperedDistribution_eq_odd_tsum
    (b : ℝ) (hb : 1 ≤ b) (f : SchwartzMap ℝ ℂ) :
    oddEulerTemperedDistribution b hb f =
      ∑' n : ℕ, (oddEulerWeight b n : ℂ) *
        (f (Real.log n) - f (-Real.log n)) := by
  rw [oddEulerTemperedDistribution_apply,
    integral_oddEulerPositiveMeasure_eq_tsum b hb,
    integral_oddEulerNegativeMeasure_eq_tsum b hb]
  rw [← (oddEulerPositiveSchwartz_summable b hb f).tsum_sub
    (oddEulerNegativeSchwartz_summable b hb f)]
  apply tsum_congr
  intro n
  ring

/-- Finite total mass is exactly undamped coefficient summability. -/
theorem oddEulerPositiveMeasure_isFiniteMeasure_iff (b : ℝ) :
    IsFiniteMeasure (oddEulerPositiveMeasure b) ↔ Summable (oddEulerWeight b) := by
  constructor
  · intro hfinite
    letI : IsFiniteMeasure (oddEulerPositiveMeasure b) := hfinite
    have hint : Integrable (fun _ : ℝ => (1 : ℝ)) (oddEulerPositiveMeasure b) :=
      integrable_const (1 : ℝ)
    have hdamped : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-((0 : ℕ) : ℝ)))
        (oddEulerPositiveMeasure b) := by simp
    have hsum := (integrable_oddEulerPositiveMeasure_iff b 0).1 hdamped
    rw [oddEulerTemperedTerm_zero_fun] at hsum
    exact hsum
  · intro hsum
    have hdamped : Summable (oddEulerTemperedTerm b 0) := by
      rw [oddEulerTemperedTerm_zero_fun]
      exact hsum
    have hint := (integrable_oddEulerPositiveMeasure_iff b 0).2 hdamped
    have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (oddEulerPositiveMeasure b) := by
      simpa using hint
    exact (integrable_const_iff_isFiniteMeasure one_ne_zero).1 hone

theorem oddEulerNegativeMeasure_isFiniteMeasure_iff (b : ℝ) :
    IsFiniteMeasure (oddEulerNegativeMeasure b) ↔ Summable (oddEulerWeight b) := by
  constructor
  · intro hfinite
    letI : IsFiniteMeasure (oddEulerNegativeMeasure b) := hfinite
    have hint : Integrable (fun _ : ℝ => (1 : ℝ)) (oddEulerNegativeMeasure b) :=
      integrable_const (1 : ℝ)
    have hdamped : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-((0 : ℕ) : ℝ)))
        (oddEulerNegativeMeasure b) := by simp
    have hsum := (integrable_oddEulerNegativeMeasure_iff b 0).1 hdamped
    rw [oddEulerTemperedTerm_zero_fun] at hsum
    exact hsum
  · intro hsum
    have hdamped : Summable (oddEulerTemperedTerm b 0) := by
      rw [oddEulerTemperedTerm_zero_fun]
      exact hsum
    have hint := (integrable_oddEulerNegativeMeasure_iff b 0).2 hdamped
    have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (oddEulerNegativeMeasure b) := by
      simpa using hint
    exact (integrable_const_iff_isFiniteMeasure one_ne_zero).1 hone

theorem summable_oddEulerWeight_of_one_lt {b : ℝ} (hb : 1 < b) :
    Summable (oddEulerWeight b) := by
  refine (GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow hb).congr ?_
  intro n
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;>
      simp [oddEulerWeight, RHTower.finiteVonMangoldtRealWeight]
  · exact (oddEulerWeight_eq_vonMangoldt_mul_rpow_neg b hn).symm

theorem oddEulerPositiveMeasure_finite_of_one_lt {b : ℝ} (hb : 1 < b) :
    IsFiniteMeasure (oddEulerPositiveMeasure b) :=
  (oddEulerPositiveMeasure_isFiniteMeasure_iff b).2
    (summable_oddEulerWeight_of_one_lt hb)

theorem oddEulerNegativeMeasure_finite_of_one_lt {b : ℝ} (hb : 1 < b) :
    IsFiniteMeasure (oddEulerNegativeMeasure b) :=
  (oddEulerNegativeMeasure_isFiniteMeasure_iff b).2
    (summable_oddEulerWeight_of_one_lt hb)

/-- Endpoint is tempered but has infinite positive and negative total variation. -/
theorem oddEuler_endpoint_tempered_infinite_variation :
    (oddEulerPositiveMeasure 1).HasTemperateGrowth ∧
      ¬ IsFiniteMeasure (oddEulerPositiveMeasure 1) ∧
      ¬ IsFiniteMeasure (oddEulerNegativeMeasure 1) := by
  refine ⟨(oddEulerPositiveMeasure_hasTemperateGrowth_iff 1).2 le_rfl, ?_, ?_⟩
  · rw [oddEulerPositiveMeasure_isFiniteMeasure_iff]
    rw [oddEulerWeight_one_fun]
    exact not_summable_finiteVonMangoldtRealWeight
  · rw [oddEulerNegativeMeasure_isFiniteMeasure_iff]
    rw [oddEulerWeight_one_fun]
    exact not_summable_finiteVonMangoldtRealWeight

/-- Route-L coefficient exponent after the exact half-density weld. -/
def routeLCoefficientExponent (a : ℝ) : ℝ := a + 1 / 2

theorem routeL_oddEuler_admitted_iff (a : ℝ) :
    (oddEulerPositiveMeasure (routeLCoefficientExponent a)).HasTemperateGrowth ↔
      1 / 2 ≤ a := by
  rw [oddEulerPositiveMeasure_hasTemperateGrowth_iff]
  simp only [routeLCoefficientExponent]
  constructor <;> intro h <;> linarith

theorem routeL_oddEuler_finite_variation_of_half_lt
    {a : ℝ} (ha : 1 / 2 < a) :
    IsFiniteMeasure (oddEulerPositiveMeasure (routeLCoefficientExponent a)) ∧
      IsFiniteMeasure (oddEulerNegativeMeasure (routeLCoefficientExponent a)) := by
  have h : 1 < routeLCoefficientExponent a := by
    simp only [routeLCoefficientExponent]
    linarith
  exact ⟨oddEulerPositiveMeasure_finite_of_one_lt h,
    oddEulerNegativeMeasure_finite_of_one_lt h⟩

theorem routeL_oddEuler_endpoint_tempered_infinite_variation :
    (oddEulerPositiveMeasure (routeLCoefficientExponent (1 / 2))).HasTemperateGrowth ∧
      ¬ IsFiniteMeasure (oddEulerPositiveMeasure (routeLCoefficientExponent (1 / 2))) := by
  have hexponent : routeLCoefficientExponent (1 / 2) = 1 := by
    norm_num [routeLCoefficientExponent]
  rw [hexponent]
  have h := oddEuler_endpoint_tempered_infinite_variation
  exact ⟨h.1, h.2.1⟩

theorem routeL_oddEuler_not_admitted_of_lt_half {a : ℝ} (ha : a < 1 / 2) :
    ¬ (oddEulerPositiveMeasure (routeLCoefficientExponent a)).HasTemperateGrowth := by
  rw [routeL_oddEuler_admitted_iff]
  exact not_le_of_gt ha

/-- Positive magnitude of the torque current coefficient. -/
def oddEulerTorqueWeight (n : ℕ) : ℝ :=
  oddEulerWeight (1 / 2) n * Real.log n

theorem oddEulerTorqueWeight_nonneg (n : ℕ) : 0 ≤ oddEulerTorqueWeight n := by
  rcases n with _ | n
  · simp [oddEulerTorqueWeight, oddEulerWeight,
      RHTower.finiteVonMangoldtRealWeight]
  · exact mul_nonneg (oddEulerWeight_nonneg (1 / 2) (n + 1))
      (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)))

theorem oddEulerTorqueWeight_eq
    {n : ℕ} (hn : 2 ≤ n) :
    oddEulerTorqueWeight n = ArithmeticFunction.vonMangoldt n * Real.log n *
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [oddEulerTorqueWeight,
    oddEulerWeight_eq_vonMangoldt_mul_rpow_neg (1 / 2) hn]
  ring

def oddEulerTorqueTemperedTerm (k n : ℕ) : ℝ :=
  oddEulerTorqueWeight n * (1 + |Real.log n|) ^ (-(k : ℝ))

theorem oddEulerTorqueTemperedTerm_nonneg (k n : ℕ) :
    0 ≤ oddEulerTorqueTemperedTerm k n := by
  exact mul_nonneg (oddEulerTorqueWeight_nonneg n)
    (Real.rpow_nonneg (by positivity) _)

theorem not_summable_oddEulerTorqueTemperedTerm (k : ℕ) :
    ¬ Summable (oddEulerTorqueTemperedTerm k) := by
  intro htorque
  apply not_summable_oddEulerTemperedTerm_of_lt_one
    (b := (1 / 2 : ℝ)) (by norm_num) k
  apply htorque.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hlog : 1 ≤ Real.log (n : ℝ) := by
    have h3e : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    have hne : Real.exp 1 ≤ (n : ℝ) := h3e.le.trans (by exact_mod_cast hn)
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
      (lt_of_lt_of_le (Real.exp_pos 1) hne) hne
  have heuler : 0 ≤ oddEulerTemperedTerm (1 / 2) k n :=
    oddEulerTemperedTerm_nonneg _ _ _
  rw [Real.norm_of_nonneg heuler]
  calc
    oddEulerTemperedTerm (1 / 2) k n =
        oddEulerTemperedTerm (1 / 2) k n * 1 := by ring
    _ ≤ oddEulerTemperedTerm (1 / 2) k n * Real.log n :=
      mul_le_mul_of_nonneg_left hlog heuler
    _ = oddEulerTorqueTemperedTerm k n := by
      rw [oddEulerTemperedTerm, oddEulerTorqueTemperedTerm, oddEulerTorqueWeight]
      ring

/-- Positive half of the torque current. -/
def oddEulerTorquePositiveMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (oddEulerTorqueWeight n) • Measure.dirac (Real.log n)

def oddEulerTorqueNegativeMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (oddEulerTorqueWeight n) • Measure.dirac (-Real.log n)

theorem integrable_oddEulerTorquePositiveMeasure_iff (k : ℕ) :
    Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(k : ℝ)))
        oddEulerTorquePositiveMeasure ↔
      Summable (oddEulerTorqueTemperedTerm k) := by
  rw [oddEulerTorquePositiveMeasure,
    integrable_sum_dirac_iff (fun n : ℕ => ENNReal.ofReal_ne_top)]
  apply summable_congr
  intro n
  rw [ENNReal.toReal_ofReal (oddEulerTorqueWeight_nonneg n)]
  simp only [Real.norm_eq_abs, oddEulerTorqueTemperedTerm]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

/-- Torque current lies beyond the tempered-admission wall. -/
theorem oddEulerTorquePositiveMeasure_not_hasTemperateGrowth :
    ¬ oddEulerTorquePositiveMeasure.HasTemperateGrowth := by
  intro hgrowth
  rcases hgrowth.exists_integrable with ⟨k, hk⟩
  exact not_summable_oddEulerTorqueTemperedTerm k
    ((integrable_oddEulerTorquePositiveMeasure_iff k).1 hk)

theorem integrable_oddEulerTorqueNegativeMeasure_iff (k : ℕ) :
    Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(k : ℝ)))
        oddEulerTorqueNegativeMeasure ↔
      Summable (oddEulerTorqueTemperedTerm k) := by
  rw [oddEulerTorqueNegativeMeasure,
    integrable_sum_dirac_iff (fun n : ℕ => ENNReal.ofReal_ne_top)]
  apply summable_congr
  intro n
  rw [ENNReal.toReal_ofReal (oddEulerTorqueWeight_nonneg n)]
  simp only [Real.norm_eq_abs, oddEulerTorqueTemperedTerm, abs_neg]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

theorem oddEulerTorqueNegativeMeasure_not_hasTemperateGrowth :
    ¬ oddEulerTorqueNegativeMeasure.HasTemperateGrowth := by
  intro hgrowth
  rcases hgrowth.exists_integrable with ⟨k, hk⟩
  exact not_summable_oddEulerTorqueTemperedTerm k
    ((integrable_oddEulerTorqueNegativeMeasure_iff k).1 hk)

def OddEulerTorqueTemperedAdmission : Prop :=
  oddEulerTorquePositiveMeasure.HasTemperateGrowth ∧
    oddEulerTorqueNegativeMeasure.HasTemperateGrowth

/-- Full signed torque current is not admitted to `S'`. -/
theorem oddEulerTorque_not_tempered : ¬ OddEulerTorqueTemperedAdmission := by
  intro h
  exact oddEulerTorquePositiveMeasure_not_hasTemperateGrowth h.1

/-- Every left ray has finite positive-half mass, without any restriction on `b`. -/
theorem oddEulerPositiveMeasure_Iio_lt_top (b y : ℝ) :
    oddEulerPositiveMeasure b (Iio y) < ∞ := by
  rw [oddEulerPositiveMeasure, Measure.sum_apply _ measurableSet_Iio]
  let N : ℕ := ⌈Real.exp y⌉₊ + 1
  rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
    have hnN : N ≤ n := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
    have hceil : Real.exp y ≤ (⌈Real.exp y⌉₊ : ℝ) := Nat.le_ceil (Real.exp y)
    have hexp : Real.exp y < (n : ℝ) := by
      calc
        Real.exp y ≤ (⌈Real.exp y⌉₊ : ℝ) := hceil
        _ < (N : ℕ) := by
          simp only [N, Nat.cast_add, Nat.cast_one]
          linarith
        _ ≤ (n : ℕ) := by exact_mod_cast hnN
    have hlog : y < Real.log (n : ℝ) := by
      rw [← Real.log_exp y]
      exact Real.strictMonoOn_log (Real.exp_pos y)
        (lt_trans (Real.exp_pos y) hexp) hexp
    simp [Measure.smul_apply, measurableSet_Iio, not_lt_of_ge hlog.le])]
  rw [ENNReal.sum_lt_top]
  intro n hn
  apply ENNReal.mul_lt_top
  · exact ENNReal.ofReal_lt_top
  · by_cases h : Real.log (n : ℝ) ∈ Iio y <;> simp [Set.indicator, h]

/-- Every right ray has finite reflected-half mass, without any restriction on `b`. -/
theorem oddEulerNegativeMeasure_Ioi_lt_top (b y : ℝ) :
    oddEulerNegativeMeasure b (Ioi y) < ∞ := by
  rw [oddEulerNegativeMeasure, Measure.sum_apply _ measurableSet_Ioi]
  let N : ℕ := ⌈Real.exp (-y)⌉₊ + 1
  rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
    have hnN : N ≤ n := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
    have hceil : Real.exp (-y) ≤ (⌈Real.exp (-y)⌉₊ : ℝ) := Nat.le_ceil (Real.exp (-y))
    have hexp : Real.exp (-y) < (n : ℝ) := by
      calc
        Real.exp (-y) ≤ (⌈Real.exp (-y)⌉₊ : ℝ) := hceil
        _ < (N : ℕ) := by
          simp only [N, Nat.cast_add, Nat.cast_one]
          linarith
        _ ≤ (n : ℕ) := by exact_mod_cast hnN
    have hlog : -y < Real.log (n : ℝ) := by
      rw [← Real.log_exp (-y)]
      exact Real.strictMonoOn_log (Real.exp_pos (-y))
        (lt_trans (Real.exp_pos (-y)) hexp) hexp
    have hnot : ¬ y < -Real.log (n : ℝ) := by linarith
    simp [Measure.smul_apply, measurableSet_Ioi, hnot])]
  rw [ENNReal.sum_lt_top]
  intro n hn
  apply ENNReal.mul_lt_top
  · exact ENNReal.ofReal_lt_top
  · by_cases h : -Real.log (n : ℝ) ∈ Ioi y <;> simp [Set.indicator, h]

theorem oddEulerPositiveMeasure_isLocallyFinite (b : ℝ) :
    IsLocallyFiniteMeasure (oddEulerPositiveMeasure b) := by
  refine ⟨fun x => ⟨Iio (x + 1), Iio_mem_nhds (by linarith), ?_⟩⟩
  exact oddEulerPositiveMeasure_Iio_lt_top b (x + 1)

theorem oddEulerNegativeMeasure_isLocallyFinite (b : ℝ) :
    IsLocallyFiniteMeasure (oddEulerNegativeMeasure b) := by
  refine ⟨fun x => ⟨Ioi (x - 1), Ioi_mem_nhds (by linarith), ?_⟩⟩
  exact oddEulerNegativeMeasure_Ioi_lt_top b (x - 1)

/-- Positive half as a genuine distribution on all of `R`, for every real `b`. -/
def oddEulerPositiveDistribution (b : ℝ) : 𝓓'((⊤ : Opens ℝ), ℝ) := by
  letI : IsLocallyFiniteMeasure (oddEulerPositiveMeasure b) :=
    oddEulerPositiveMeasure_isLocallyFinite b
  exact TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    (oddEulerPositiveMeasure b) (fun _ : ℝ => (1 : ℝ))

/-- Reflected half as a genuine distribution on all of `R`, for every real `b`. -/
def oddEulerNegativeDistribution (b : ℝ) : 𝓓'((⊤ : Opens ℝ), ℝ) := by
  letI : IsLocallyFiniteMeasure (oddEulerNegativeMeasure b) :=
    oddEulerNegativeMeasure_isLocallyFinite b
  exact TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    (oddEulerNegativeMeasure b) (fun _ : ℝ => (1 : ℝ))

/-- Literal odd locally finite Euler comb `D_b` in `D'(R)`, for every real `b`. -/
def oddEulerDistribution (b : ℝ) : 𝓓'((⊤ : Opens ℝ), ℝ) :=
  oddEulerPositiveDistribution b - oddEulerNegativeDistribution b

theorem oddEulerPositiveDistribution_apply
    (b : ℝ) (f : 𝓓((⊤ : Opens ℝ), ℝ)) :
    oddEulerPositiveDistribution b f = ∫ x, f x ∂oddEulerPositiveMeasure b := by
  letI : IsLocallyFiniteMeasure (oddEulerPositiveMeasure b) :=
    oddEulerPositiveMeasure_isLocallyFinite b
  change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    (oddEulerPositiveMeasure b) (fun _ : ℝ => (1 : ℝ)) f = _
  rw [TestFunction.integralAgainstBilinCLM_eq_integral
    (locallyIntegrableOn_const (1 : ℝ))]
  simp

theorem oddEulerNegativeDistribution_apply
    (b : ℝ) (f : 𝓓((⊤ : Opens ℝ), ℝ)) :
    oddEulerNegativeDistribution b f = ∫ x, f x ∂oddEulerNegativeMeasure b := by
  letI : IsLocallyFiniteMeasure (oddEulerNegativeMeasure b) :=
    oddEulerNegativeMeasure_isLocallyFinite b
  change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    (oddEulerNegativeMeasure b) (fun _ : ℝ => (1 : ℝ)) f = _
  rw [TestFunction.integralAgainstBilinCLM_eq_integral
    (locallyIntegrableOn_const (1 : ℝ))]
  simp

theorem oddEulerDistribution_apply
    (b : ℝ) (f : 𝓓((⊤ : Opens ℝ), ℝ)) :
    oddEulerDistribution b f =
      (∫ x, f x ∂oddEulerPositiveMeasure b) -
        ∫ x, f x ∂oddEulerNegativeMeasure b := by
  change oddEulerPositiveDistribution b f - oddEulerNegativeDistribution b f = _
  rw [oddEulerPositiveDistribution_apply, oddEulerNegativeDistribution_apply]

theorem oddEulerPositiveTest_summable
    (b : ℝ) (f : 𝓓((⊤ : Opens ℝ), ℝ)) :
    Summable fun n : ℕ => oddEulerWeight b n * f (Real.log n) := by
  letI : IsLocallyFiniteMeasure (oddEulerPositiveMeasure b) :=
    oddEulerPositiveMeasure_isLocallyFinite b
  have hlocal : LocallyIntegrableOn (fun _ : ℝ => (1 : ℝ)) (⊤ : Opens ℝ)
      (oddEulerPositiveMeasure b) := locallyIntegrableOn_const (1 : ℝ)
  have hf : Integrable f (oddEulerPositiveMeasure b) :=
    f.integrable hlocal
  rw [oddEulerPositiveMeasure] at hf
  have hnorm := (integrable_sum_dirac_iff
    (f := fun x : ℝ => f x)
    (c := fun n : ℕ => ENNReal.ofReal (oddEulerWeight b n))
    (x := fun n : ℕ => Real.log n)
    (fun _ => ENNReal.ofReal_ne_top)).1 hf
  apply Summable.of_norm
  convert hnorm using 1
  ext n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (oddEulerWeight_nonneg b n),
    ENNReal.toReal_ofReal (oddEulerWeight_nonneg b n)]
  rw [Real.norm_eq_abs]

theorem oddEulerNegativeTest_summable
    (b : ℝ) (f : 𝓓((⊤ : Opens ℝ), ℝ)) :
    Summable fun n : ℕ => oddEulerWeight b n * f (-Real.log n) := by
  letI : IsLocallyFiniteMeasure (oddEulerNegativeMeasure b) :=
    oddEulerNegativeMeasure_isLocallyFinite b
  have hlocal : LocallyIntegrableOn (fun _ : ℝ => (1 : ℝ)) (⊤ : Opens ℝ)
      (oddEulerNegativeMeasure b) := locallyIntegrableOn_const (1 : ℝ)
  have hf : Integrable f (oddEulerNegativeMeasure b) :=
    f.integrable hlocal
  rw [oddEulerNegativeMeasure] at hf
  have hnorm := (integrable_sum_dirac_iff
    (f := fun x : ℝ => f x)
    (c := fun n : ℕ => ENNReal.ofReal (oddEulerWeight b n))
    (x := fun n : ℕ => -Real.log n)
    (fun _ => ENNReal.ofReal_ne_top)).1 hf
  apply Summable.of_norm
  convert hnorm using 1
  ext n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (oddEulerWeight_nonneg b n),
    ENNReal.toReal_ofReal (oddEulerWeight_nonneg b n)]
  rw [Real.norm_eq_abs]

/-- Exact locally finite distribution pairing, with no condition on `b`. -/
theorem oddEulerDistribution_eq_odd_tsum
    (b : ℝ) (f : 𝓓((⊤ : Opens ℝ), ℝ)) :
    oddEulerDistribution b f =
      ∑' n : ℕ, oddEulerWeight b n *
        (f (Real.log n) - f (-Real.log n)) := by
  rw [oddEulerDistribution_apply]
  letI : IsLocallyFiniteMeasure (oddEulerPositiveMeasure b) :=
    oddEulerPositiveMeasure_isLocallyFinite b
  letI : IsLocallyFiniteMeasure (oddEulerNegativeMeasure b) :=
    oddEulerNegativeMeasure_isLocallyFinite b
  have hposLocal : LocallyIntegrableOn (fun _ : ℝ => (1 : ℝ)) (⊤ : Opens ℝ)
      (oddEulerPositiveMeasure b) := locallyIntegrableOn_const (1 : ℝ)
  have hnegLocal : LocallyIntegrableOn (fun _ : ℝ => (1 : ℝ)) (⊤ : Opens ℝ)
      (oddEulerNegativeMeasure b) := locallyIntegrableOn_const (1 : ℝ)
  have hposInt : Integrable f (oddEulerPositiveMeasure b) := f.integrable hposLocal
  have hnegInt : Integrable f (oddEulerNegativeMeasure b) := f.integrable hnegLocal
  have hposNorm : Summable fun n : ℕ =>
      (ENNReal.ofReal (oddEulerWeight b n)).toReal * ‖f (Real.log n)‖ := by
    rw [oddEulerPositiveMeasure] at hposInt
    exact (integrable_sum_dirac_iff (fun _ => ENNReal.ofReal_ne_top)).1 hposInt
  have hnegNorm : Summable fun n : ℕ =>
      (ENNReal.ofReal (oddEulerWeight b n)).toReal * ‖f (-Real.log n)‖ := by
    rw [oddEulerNegativeMeasure] at hnegInt
    exact (integrable_sum_dirac_iff (fun _ => ENNReal.ofReal_ne_top)).1 hnegInt
  rw [oddEulerPositiveMeasure,
    integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) hposNorm,
    oddEulerNegativeMeasure,
    integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top) hnegNorm]
  simp_rw [ENNReal.toReal_ofReal (oddEulerWeight_nonneg b _), smul_eq_mul]
  rw [← (oddEulerPositiveTest_summable b f).tsum_sub
    (oddEulerNegativeTest_summable b f)]
  apply tsum_congr
  intro n
  ring

/-- Standard signed-Radon-measure admission condition: both Jordan halves have polynomially
weighted finite mass.  For this odd comb the halves are reflections with disjoint nonzero support,
so this is exactly temperateness of its total variation. -/
def OddEulerCombTemperedAdmission (b : ℝ) : Prop :=
  (oddEulerPositiveMeasure b).HasTemperateGrowth ∧
    (oddEulerNegativeMeasure b).HasTemperateGrowth

/-- Exact sharp admission wall for the literal odd Euler comb. -/
theorem oddEulerCombTemperedAdmission_iff (b : ℝ) :
    OddEulerCombTemperedAdmission b ↔ 1 ≤ b := by
  rw [OddEulerCombTemperedAdmission,
    oddEulerPositiveMeasure_hasTemperateGrowth_iff,
    oddEulerNegativeMeasure_hasTemperateGrowth_iff,
    and_self]

/-- Full Card-2 capstone: local `D'` object exists for every `b`; its signed-measure total
variation is tempered exactly at `b >= 1`; every admitted parameter has the literal `S'`
realization and exact odd atomic pairing. -/
theorem oddEulerComb_exact_admission_wall (b : ℝ) :
    (∃ D : 𝓓'((⊤ : Opens ℝ), ℝ),
      ∀ f : 𝓓((⊤ : Opens ℝ), ℝ),
        D f = ∑' n : ℕ, oddEulerWeight b n *
          (f (Real.log n) - f (-Real.log n))) ∧
    (OddEulerCombTemperedAdmission b ↔ 1 ≤ b) ∧
    (∀ _hb : 1 ≤ b, ∃ T : TemperedDistribution ℝ ℂ,
      ∀ f : SchwartzMap ℝ ℂ,
        T f = ∑' n : ℕ, (oddEulerWeight b n : ℂ) *
          (f (Real.log n) - f (-Real.log n))) := by
  refine ⟨⟨oddEulerDistribution b, oddEulerDistribution_eq_odd_tsum b⟩,
    oddEulerCombTemperedAdmission_iff b, ?_⟩
  intro hb
  exact ⟨oddEulerTemperedDistribution b hb,
    oddEulerTemperedDistribution_eq_odd_tsum b hb⟩

end

end HTGeometry
