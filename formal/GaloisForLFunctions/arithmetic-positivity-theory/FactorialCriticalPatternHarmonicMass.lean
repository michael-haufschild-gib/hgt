import GaloisForLFunctions.RHTower.FourierPositiveJumpNetwork
import GaloisForLFunctions.RHTower.ZetaUnitIntervalIntegrals
import GaloisForLFunctions.HTGeometry.InverseSquareTailSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Uniform physical harmonic masses of finite translated patterns

For a finite real coefficient pattern, `factorialCriticalPatternDensity` is the
squared modulus of its integer-frequency trigonometric polynomial. The critical
factorial collar supplies the slow factor `1 - cos (2π m v / 12)`.

The resulting physical mass, integrated against `v⁻²` on `v > 1`, lies between
`(∑ j ∈ S, b j²) / 48` and `4 * ∑ j ∈ S, b j²` for every positive integer harmonic.
These constants are independent of the number and positions of the coefficients.
The mass therefore vanishes exactly for the zero coefficient pattern.

The proof reuses the corpus's scalar integer cosine orthogonality, unit-interval
half-line decomposition, and rational inverse-square series estimate. The exact
unit-cell and twelve-unit collar identities retain the finite Fourier square.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory

/-- The finite real Fourier square carried by a translated coefficient pattern. -/
def factorialCriticalPatternDensity (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  (∑ j ∈ S, b j * Real.cos (2 * Real.pi * j * t)) ^ 2 +
    (∑ j ∈ S, b j * Real.sin (2 * Real.pi * j * t)) ^ 2

/-- The pattern density is nonnegative at every point. -/
theorem factorialCriticalPatternDensity_nonneg (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    0 ≤ factorialCriticalPatternDensity S b t :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Exact pairwise cosine expansion, including every unequal coefficient pair. -/
theorem factorialCriticalPatternDensity_eq (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    factorialCriticalPatternDensity S b t =
      ∑ i ∈ S, ∑ j ∈ S, b i * b j * Real.cos (2 * Real.pi * ((i : ℝ) - j) * t) := by
  classical
  unfold factorialCriticalPatternDensity
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show 2 * Real.pi * ((i : ℝ) - j) * t =
    2 * Real.pi * i * t - 2 * Real.pi * j * t by ring, Real.cos_sub]
  ring

/-- The finite pattern density is continuous. -/
theorem continuous_factorialCriticalPatternDensity (S : Finset ℕ) (b : ℕ → ℝ) :
    Continuous (factorialCriticalPatternDensity S b) := by
  unfold factorialCriticalPatternDensity
  fun_prop

private theorem pattern_cos_periodic (k : ℤ) :
    Function.Periodic (fun t : ℝ => Real.cos (2 * Real.pi * k * t)) 1 := by
  intro t
  change Real.cos (2 * Real.pi * k * (t + 1)) = Real.cos (2 * Real.pi * k * t)
  rw [show 2 * Real.pi * (k : ℝ) * (t + 1) =
    2 * Real.pi * k * t + k * (2 * Real.pi) by ring]
  exact Real.cos_add_int_mul_two_pi _ _

private theorem pattern_cos_cell (k : ℤ) (a : ℝ) :
    (∫ t in a..a + 1, Real.cos (2 * Real.pi * k * t)) =
      if k = 0 then 1 else 0 := by
  rw [(pattern_cos_periodic k).intervalIntegral_add_eq a 0]
  simpa only [zero_add] using RHTower.integral_cos_two_pi_int_mul k

/-- Every real unit interval has exactly the coefficient square mass at each positive integer dilation. -/
theorem factorialCriticalPatternDensity_cell (S : Finset ℕ) (b : ℕ → ℝ)
    {m : ℕ} (hm : 0 < m) (a : ℝ) :
    (∫ t in a..a + 1, factorialCriticalPatternDensity S b (m * t)) =
      ∑ j ∈ S, b j ^ 2 := by
  classical
  simp_rw [factorialCriticalPatternDensity_eq]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul]
      have hfreq (j : ℕ) (t : ℝ) :
          Real.cos (2 * Real.pi * ((i : ℝ) - j) * (m * t)) =
          Real.cos (2 * Real.pi * ((m : ℤ) * ((i : ℤ) - j) : ℤ) * t) := by
        congr 1
        push_cast
        ring
      simp_rw [hfreq, pattern_cos_cell]
      have hz (j : ℕ) : (m : ℤ) * ((i : ℤ) - j) = 0 ↔ j = i := by
        rw [mul_eq_zero, or_iff_right (by exact_mod_cast (ne_of_gt hm)), sub_eq_zero]
        constructor <;> intro h <;> exact_mod_cast h.symm
      simp_rw [hz]
      simp [hi, pow_two]
    · intro j hj
      exact (by fun_prop : Continuous (fun t : ℝ =>
        b i * b j * Real.cos (2 * Real.pi * ((i : ℝ) - j) * (m * t)))).intervalIntegrable _ _
  · intro i hi
    exact (by fun_prop : Continuous (fun t : ℝ =>
      ∑ j ∈ S, b i * b j * Real.cos (2 * Real.pi * ((i : ℝ) - j) * (m * t)))).intervalIntegrable _ _

/-- The coefficient absolute-sum square bounds the density pointwise. -/
theorem factorialCriticalPatternDensity_le (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    |factorialCriticalPatternDensity S b t| ≤ (∑ j ∈ S, |b j|) ^ 2 := by
  classical
  rw [factorialCriticalPatternDensity_eq]
  calc
    |∑ i ∈ S, ∑ j ∈ S, b i * b j * Real.cos (2 * Real.pi * ((i : ℝ) - j) * t)|
        ≤ ∑ i ∈ S, |∑ j ∈ S, b i * b j *
          Real.cos (2 * Real.pi * ((i : ℝ) - j) * t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, |b i| * |b j| := by
      apply Finset.sum_le_sum
      intro i hi
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro j hj
      simp only [abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Real.abs_cos_le_one _)
    _ = (∑ j ∈ S, |b j|) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

private theorem pattern_cos_twelve_cell (k : ℤ) :
    (∫ t in (12 : ℝ)..24, Real.cos (2 * Real.pi * k * t / 12)) =
      12 * (if k = 0 then 1 else 0) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (1 : ℝ)) (b := 2)
    (fun t : ℝ => Real.cos (2 * Real.pi * k * t / 12)) (12 : ℝ)
  norm_num only [smul_eq_mul, mul_one, show (12 : ℝ) * 2 = 24 by norm_num] at h
  rw [← h]
  congr 1
  have heq (t : ℝ) : 2 * Real.pi * (k : ℝ) * (12 * t) / 12 =
      2 * Real.pi * k * t := by ring
  simp_rw [heq]
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using pattern_cos_cell k 1

private theorem pattern_cos_twelve (m : ℕ) (k : ℤ) :
    (∫ t in (12 : ℝ)..24, Real.cos (2 * Real.pi * m * k * t)) =
      12 * (if (m : ℤ) * k = 0 then 1 else 0) := by
  have heq (t : ℝ) :
      Real.cos (2 * Real.pi * m * k * t) =
      Real.cos (2 * Real.pi * (12 * ((m : ℤ) * k) : ℤ) * t / 12) := by
    congr 1
    push_cast
    ring
  simp_rw [heq, pattern_cos_twelve_cell]
  simp

private theorem pattern_mixed_twelve {m : ℕ} (hm : 0 < m) (k : ℤ) :
    (∫ t in (12 : ℝ)..24, Real.cos (2 * Real.pi * m * t / 12) *
      Real.cos (2 * Real.pi * m * k * t)) = 0 := by
  have hp : (m : ℤ) * (12 * k + 1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (ne_of_gt hm)) (by omega)
  have hn : (m : ℤ) * (12 * k - 1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (ne_of_gt hm)) (by omega)
  have heq (t : ℝ) : Real.cos (2 * Real.pi * m * t / 12) *
      Real.cos (2 * Real.pi * m * k * t) =
      (Real.cos (2 * Real.pi * ((m : ℤ) * (12 * k + 1) : ℤ) * t / 12) +
       Real.cos (2 * Real.pi * ((m : ℤ) * (12 * k - 1) : ℤ) * t / 12)) / 2 := by
    have hplus : 2 * Real.pi * (((m : ℤ) * (12 * k + 1) : ℤ) : ℝ) * t / 12 =
        2 * Real.pi * m * k * t + 2 * Real.pi * m * t / 12 := by push_cast; ring
    have hminus : 2 * Real.pi * (((m : ℤ) * (12 * k - 1) : ℤ) : ℝ) * t / 12 =
        2 * Real.pi * m * k * t - 2 * Real.pi * m * t / 12 := by push_cast; ring
    rw [hplus, hminus, Real.cos_add, Real.cos_sub]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add]
  · simp only [pattern_cos_twelve_cell, if_neg hp, if_neg hn, mul_zero, add_zero, zero_div]
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Real.cos (2 * Real.pi * ((m : ℤ) * (12 * k + 1) : ℤ) * t / 12))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Real.cos (2 * Real.pi * ((m : ℤ) * (12 * k - 1) : ℤ) * t / 12))).intervalIntegrable _ _

/-- The slow factorial collar retains exactly twelve times the coefficient square mass on `[12,24]`. -/
theorem factorialCriticalPatternDensity_twelve_collar (S : Finset ℕ) (b : ℕ → ℝ)
    {m : ℕ} (hm : 0 < m) :
    (∫ t in (12 : ℝ)..24, (1 - Real.cos (2 * Real.pi * m * t / 12)) *
      factorialCriticalPatternDensity S b (m * t)) = 12 * ∑ j ∈ S, b j ^ 2 := by
  classical
  have hsingle (i j : ℕ) :
      (∫ t in (12 : ℝ)..24, (1 - Real.cos (2 * Real.pi * m * t / 12)) *
        Real.cos (2 * Real.pi * ((i : ℝ) - j) * (m * t))) =
        12 * (if j = i then 1 else 0) := by
    have heq (t : ℝ) : 2 * Real.pi * ((i : ℝ) - j) * (m * t) =
        2 * Real.pi * m * ((i : ℤ) - j : ℤ) * t := by push_cast; ring
    simp_rw [heq, sub_mul, one_mul]
    rw [intervalIntegral.integral_sub]
    · rw [pattern_cos_twelve, pattern_mixed_twelve hm, sub_zero]
      congr 2
      apply propext
      rw [mul_eq_zero, or_iff_right (by exact_mod_cast (ne_of_gt hm)), sub_eq_zero]
      constructor <;> intro h <;> exact_mod_cast h.symm
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        Real.cos (2 * Real.pi * m * ((i : ℤ) - j : ℤ) * t))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        Real.cos (2 * Real.pi * m * t / 12) *
          Real.cos (2 * Real.pi * m * ((i : ℤ) - j : ℤ) * t))).intervalIntegrable _ _
  simp_rw [factorialCriticalPatternDensity_eq, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · have heq (j : ℕ) (t : ℝ) :
          (1 - Real.cos (2 * Real.pi * m * t / 12)) *
            (b i * b j * Real.cos (2 * Real.pi * ((i : ℝ) - j) * (m * t))) =
          (b i * b j) * ((1 - Real.cos (2 * Real.pi * m * t / 12)) *
            Real.cos (2 * Real.pi * ((i : ℝ) - j) * (m * t))) := by ring
      simp_rw [heq, intervalIntegral.integral_const_mul, hsingle]
      simp [hi, pow_two]
      ring
    · intro j hj
      exact (by fun_prop : Continuous (fun t : ℝ =>
        (1 - Real.cos (2 * Real.pi * m * t / 12)) *
          (b i * b j * Real.cos (2 * Real.pi * ((i : ℝ) - j) * (m * t))))).intervalIntegrable _ _
  · intro i hi
    exact (by fun_prop : Continuous (fun t : ℝ =>
      ∑ j ∈ S, (1 - Real.cos (2 * Real.pi * m * t / 12)) *
        (b i * b j * Real.cos (2 * Real.pi * ((i : ℝ) - j) * (m * t))))).intervalIntegrable _ _

private theorem pattern_weighted_integrable {f : ℝ → ℝ} {B : ℝ}
    (hf : Continuous f) (hB : ∀ v, |f v| ≤ B) :
    IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ) * f v) (Ioi 1) := by
  have hw : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  refine (hw.mul_const B).mono' (hw.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 ≤ v := le_trans zero_le_one (le_of_lt hv)
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv0 _)] using
    mul_le_mul_of_nonneg_left (hB v) (Real.rpow_nonneg hv0 (-2))

private theorem pattern_weighted_density_integrable (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ) *
      factorialCriticalPatternDensity S b (m * v)) (Ioi 1) :=
  pattern_weighted_integrable
    ((continuous_factorialCriticalPatternDensity S b).comp (by fun_prop))
    (fun v => factorialCriticalPatternDensity_le S b (m * v))

/-- The physical harmonic mass of a finite translated pattern at the critical factorial collar. -/
def factorialCriticalPatternHarmonicMass (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
    ((1 - Real.cos (2 * Real.pi * m * v / 12)) * factorialCriticalPatternDensity S b (m * v))

/-- Every finite pattern has an integrable physical harmonic density. -/
theorem integrable_factorialCriticalPatternHarmonicMass
    (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ) *
      ((1 - Real.cos (2 * Real.pi * m * v / 12)) *
        factorialCriticalPatternDensity S b (m * v))) (Ioi 1) := by
  apply pattern_weighted_integrable (B := 2 * (∑ j ∈ S, |b j|) ^ 2)
  · exact (by fun_prop : Continuous (fun v : ℝ => 1 - Real.cos (2 * Real.pi * m * v / 12))).mul
      ((continuous_factorialCriticalPatternDensity S b).comp (by fun_prop))
  · intro v
    rw [abs_mul]
    have hslow : |1 - Real.cos (2 * Real.pi * m * v / 12)| ≤ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      linarith [Real.neg_one_le_cos (2 * Real.pi * m * v / 12)]
    exact mul_le_mul hslow (factorialCriticalPatternDensity_le S b (m * v))
      (abs_nonneg _) (by norm_num)

private theorem pattern_slow_nonneg (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) (v : ℝ) :
    0 ≤ (1 - Real.cos (2 * Real.pi * m * v / 12)) *
      factorialCriticalPatternDensity S b (m * v) :=
  mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _))
    (factorialCriticalPatternDensity_nonneg S b _)

/-- Every physical harmonic mass is nonnegative. -/
theorem factorialCriticalPatternHarmonicMass_nonneg
    (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) :
    0 ≤ factorialCriticalPatternHarmonicMass S b m := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro v hv
  exact mul_nonneg (Real.rpow_nonneg (by linarith [mem_Ioi.mp hv]) _)
    (pattern_slow_nonneg S b m v)

private theorem pattern_weighted_density_le (S : Finset ℕ) (b : ℕ → ℝ)
    {m : ℕ} (hm : 0 < m) :
    (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * factorialCriticalPatternDensity S b (m * v)) ≤
      2 * ∑ j ∈ S, b j ^ 2 := by
  let f : ℝ → ℝ := fun v => v ^ (-2 : ℝ) * factorialCriticalPatternDensity S b (m * v)
  have hf : IntegrableOn f (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (pattern_weighted_density_integrable S b m)
  have hsumC := RHTower.hasSum_integral_Ico_unit (c := 1)
    (f := fun v => (f v : ℂ)) hf.ofReal
  have hsum := Complex.hasSum_re hsumC
  simp only [integral_complex_ofReal, Complex.ofReal_re, integral_Ici_eq_integral_Ioi] at hsum
  have hmajor := (HTGeometry.summable_inv_sq_shift (σ := 1) zero_lt_one).mul_right
    (∑ j ∈ S, b j ^ 2)
  have hcell (k : ℕ) : (∫ v in Ico (1 + (k : ℝ)) (1 + k + 1), f v) ≤
      (1 / (1 + (k : ℝ)) ^ 2) * ∑ j ∈ S, b j ^ 2 := by
    have hfc : IntegrableOn f (Ico (1 + (k : ℝ)) (1 + k + 1)) :=
      hf.mono_set (by
        intro v hv
        change (1 : ℝ) ≤ v
        linarith [hv.1, Nat.cast_nonneg (α := ℝ) k])
    have hQc : IntegrableOn (fun v : ℝ =>
        (1 / (1 + (k : ℝ)) ^ 2) * factorialCriticalPatternDensity S b (m * v))
        (Ico (1 + k) (1 + k + 1)) :=
      (((continuous_factorialCriticalPatternDensity S b).comp (by fun_prop)).const_mul _).integrableOn_Icc.mono_set
        Ico_subset_Icc_self
    calc
      (∫ v in Ico (1 + (k : ℝ)) (1 + k + 1), f v) ≤
          ∫ v in Ico (1 + (k : ℝ)) (1 + k + 1),
            (1 / (1 + (k : ℝ)) ^ 2) * factorialCriticalPatternDensity S b (m * v) := by
        apply setIntegral_mono_on hfc hQc measurableSet_Ico
        intro v hv
        have hk : 0 < 1 + (k : ℝ) := by positivity
        have hv0 : 0 < v := lt_of_lt_of_le hk hv.1
        have hweight : v ^ (-2 : ℝ) ≤ 1 / (1 + (k : ℝ)) ^ 2 := by
          rw [Real.rpow_neg hv0.le, Real.rpow_two, ← one_div]
          apply one_div_le_one_div_of_le (sq_pos_of_pos hk)
          nlinarith [hv.1, sq_nonneg (v - (1 + (k : ℝ)))]
        exact mul_le_mul_of_nonneg_right hweight (factorialCriticalPatternDensity_nonneg S b _)
      _ = (1 / (1 + (k : ℝ)) ^ 2) * ∑ j ∈ S, b j ^ 2 := by
        rw [integral_const_mul, integral_Ico_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith), factorialCriticalPatternDensity_cell S b hm]
  calc
    (∫ v in Ioi (1 : ℝ), f v) = ∑' k : ℕ, ∫ v in Ico (1 + (k : ℝ)) (1 + k + 1), f v := hsum.tsum_eq.symm
    _ ≤ ∑' k : ℕ, (1 / (1 + (k : ℝ)) ^ 2) * ∑ j ∈ S, b j ^ 2 :=
      hsum.summable.tsum_le_tsum hcell hmajor
    _ = (∑' k : ℕ, 1 / (1 + (k : ℝ)) ^ 2) * ∑ j ∈ S, b j ^ 2 := tsum_mul_right
    _ ≤ 2 * ∑ j ∈ S, b j ^ 2 :=
      mul_le_mul_of_nonneg_right HTGeometry.tsum_inv_sq_shift_one_le_two
        (Finset.sum_nonneg (fun j hj => sq_nonneg _))

/-- Uniform upper bound independent of support size, support positions, and positive harmonic index. -/
theorem factorialCriticalPatternHarmonicMass_le (S : Finset ℕ) (b : ℕ → ℝ)
    {m : ℕ} (hm : 0 < m) :
    factorialCriticalPatternHarmonicMass S b m ≤ 4 * ∑ j ∈ S, b j ^ 2 := by
  have hcmp : factorialCriticalPatternHarmonicMass S b m ≤
      2 * (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * factorialCriticalPatternDensity S b (m * v)) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (integrable_factorialCriticalPatternHarmonicMass S b m)
      ((pattern_weighted_density_integrable S b m).const_mul 2) measurableSet_Ioi
    intro v hv
    have hv0 : 0 ≤ v := by linarith [mem_Ioi.mp hv]
    have hq := factorialCriticalPatternDensity_nonneg S b (m * v)
    have hs : 1 - Real.cos (2 * Real.pi * m * v / 12) ≤ 2 := by
      linarith [Real.neg_one_le_cos (2 * Real.pi * m * v / 12)]
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs hq)
      (Real.rpow_nonneg hv0 (-2))
    nlinarith
  linarith [pattern_weighted_density_le S b hm]

/-- Uniform positive lower bound from the exact twelve-unit collar identity. -/
theorem factorialCriticalPatternHarmonicMass_ge (S : Finset ℕ) (b : ℕ → ℝ)
    {m : ℕ} (hm : 0 < m) :
    (∑ j ∈ S, b j ^ 2) / 48 ≤ factorialCriticalPatternHarmonicMass S b m := by
  let F : ℝ → ℝ := fun v => (1 - Real.cos (2 * Real.pi * m * v / 12)) *
    factorialCriticalPatternDensity S b (m * v)
  have hF : Continuous F :=
    (by fun_prop : Continuous (fun v : ℝ => 1 - Real.cos (2 * Real.pi * m * v / 12))).mul
      ((continuous_factorialCriticalPatternDensity S b).comp (by fun_prop))
  have hf := integrable_factorialCriticalPatternHarmonicMass S b m
  have hsub : Ioc (12 : ℝ) 24 ⊆ Ioi 1 := by
    intro v hv
    change (1 : ℝ) < v
    linarith [hv.1]
  have hint : IntervalIntegrable (fun v : ℝ => v ^ (-2 : ℝ) * F v) volume 12 24 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.mono_set hsub)
  have hlow : (∫ v in (12 : ℝ)..24, (1 / 576 : ℝ) * F v) ≤
      ∫ v in (12 : ℝ)..24, v ^ (-2 : ℝ) * F v := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hF.const_mul _).intervalIntegrable 12 24) hint
    intro v hv
    have hv0 : 0 < v := by linarith [hv.1]
    have hweight : (1 / 576 : ℝ) ≤ v ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hv0.le, Real.rpow_two, ← one_div]
      apply one_div_le_one_div_of_le (sq_pos_of_pos hv0)
      nlinarith [hv.1, hv.2]
    exact mul_le_mul_of_nonneg_right hweight (pattern_slow_nonneg S b m v)
  have hupper : (∫ v in (12 : ℝ)..24, v ^ (-2 : ℝ) * F v) ≤
      factorialCriticalPatternHarmonicMass S b m := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    apply setIntegral_mono_set hf _ hsub.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mul_nonneg (Real.rpow_nonneg (by linarith [mem_Ioi.mp hv]) _)
      (pattern_slow_nonneg S b m v)
  rw [intervalIntegral.integral_const_mul] at hlow
  change (1 / 576 : ℝ) * (∫ v in (12 : ℝ)..24,
    (1 - Real.cos (2 * Real.pi * m * v / 12)) * factorialCriticalPatternDensity S b (m * v)) ≤ _ at hlow
  rw [factorialCriticalPatternDensity_twelve_collar S b hm] at hlow
  linarith

/-- At every positive harmonic, zero physical mass is equivalent to zero coefficients on the support. -/
theorem factorialCriticalPatternHarmonicMass_eq_zero_iff
    (S : Finset ℕ) (b : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    factorialCriticalPatternHarmonicMass S b m = 0 ↔ ∀ j ∈ S, b j = 0 := by
  constructor
  · intro hzero j hj
    have hlow := factorialCriticalPatternHarmonicMass_ge S b hm
    rw [hzero] at hlow
    have hterm : b j ^ 2 ≤ ∑ i ∈ S, b i ^ 2 :=
      Finset.single_le_sum (fun i hi => sq_nonneg _) hj
    nlinarith [sq_nonneg (b j)]
  · intro hb
    have hQ (v : ℝ) : factorialCriticalPatternDensity S b v = 0 := by
      unfold factorialCriticalPatternDensity
      have hc : (∑ j ∈ S, b j * Real.cos (2 * Real.pi * j * v)) = 0 :=
        Finset.sum_eq_zero (fun j hj => by rw [hb j hj, zero_mul])
      have hs : (∑ j ∈ S, b j * Real.sin (2 * Real.pi * j * v)) = 0 :=
        Finset.sum_eq_zero (fun j hj => by rw [hb j hj, zero_mul])
      rw [hc, hs]
      norm_num
    simp [factorialCriticalPatternHarmonicMass, hQ]

/-- Every nonzero finite coefficient pattern has strictly positive physical mass at every positive harmonic. -/
theorem factorialCriticalPatternHarmonicMass_pos_iff
    (S : Finset ℕ) (b : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    0 < factorialCriticalPatternHarmonicMass S b m ↔ ∃ j ∈ S, b j ≠ 0 := by
  constructor
  · intro hpos
    by_contra! hall
    have hz := (factorialCriticalPatternHarmonicMass_eq_zero_iff S b hm).mpr hall
    linarith
  · rintro ⟨j, hj, hbj⟩
    by_contra hnot
    have hz : factorialCriticalPatternHarmonicMass S b m = 0 :=
      le_antisymm (le_of_not_gt hnot) (factorialCriticalPatternHarmonicMass_nonneg S b m)
    exact hbj ((factorialCriticalPatternHarmonicMass_eq_zero_iff S b hm).mp hz j hj)

end GaloisForLFunctions.ArithmeticPositivityTheory
