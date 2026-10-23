import GaloisForLFunctions.«arithmetic-positivity-theory».DyadicDilationCorrelationInequality
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialAffineFrequencyIntervals
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-! Critical square energy of the affine-clock error.
Disjoint frequency intervals control each harmonic in coefficient square norm,
independently of the number of source scales. -/

open MeasureTheory Set Filter
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The complete critical physical weight on the half-line. -/
def criticalWindowWeight (v : ℝ) : ℝ := v ^ (-2 : ℝ)

theorem integrableOn_criticalWindowWeight :
    IntegrableOn criticalWindowWeight (Ioi (1 : ℝ)) :=
  integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one

/-- Integer dilation multiplies the harmonic index without changing the source scales. -/
theorem realHarmonicLayer_dilate_nat (S : Finset ℕ) (b : ℕ → ℝ) (k r : ℕ) (v : ℝ) :
    realHarmonicLayer S b k ((r : ℝ) * v) = realHarmonicLayer S b (k * r) v := by
  unfold realHarmonicLayer
  apply Finset.sum_congr rfl
  intro n hn
  congr 2 <;> congr 1 <;> push_cast <;> ring

theorem realHarmonicLayer_zero (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    realHarmonicLayer S b 0 v = 0 := by
  simp only [realHarmonicLayer, Nat.cast_zero, mul_zero, zero_mul, sub_self,
    Finset.sum_const_zero]

/-- The real and complex harmonic normalizations agree for real coefficients. -/
theorem realHarmonicLayer_eq_re (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) (v : ℝ) :
    realHarmonicLayer S b k v =
      (factorialHarmonicLayer S (fun n => (b n : ℂ)) k v).re := by
  simp only [realHarmonicLayer, factorialHarmonicLayer, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re]

/-- Critical physical measure, with the endpoint at one retained. -/
def criticalWindowMeasure : Measure ℝ :=
  (volume.restrict (Ioi (1 : ℝ))).withDensity fun v => ENNReal.ofReal ((v ^ 2)⁻¹)

private theorem window_weight_integrable :
    IntegrableOn (fun v : ℝ => (v ^ 2)⁻¹) (Ioi (1 : ℝ)) := by
  refine integrableOn_criticalWindowWeight.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  unfold criticalWindowWeight
  rw [Real.rpow_neg (zero_lt_one.trans hv).le, Real.rpow_two]

instance : IsFiniteMeasure criticalWindowMeasure :=
  isFiniteMeasure_withDensity_ofReal window_weight_integrable.2

theorem integral_criticalWindowMeasure (f : ℝ → ℝ) :
    (∫ v, f v ∂criticalWindowMeasure) = ∫ v in Ioi (1 : ℝ), f v / v ^ 2 := by
  unfold criticalWindowMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun v => ENNReal.ofReal_lt_top) f]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg v)), smul_eq_mul]
  ring

theorem integral_criticalWindowMeasure_eq_weight (f : ℝ → ℝ) :
    (∫ v, f v ∂criticalWindowMeasure) =
      ∫ v in Ioi (1 : ℝ), criticalWindowWeight v * f v := by
  rw [integral_criticalWindowMeasure]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  unfold criticalWindowWeight
  rw [Real.rpow_neg (zero_lt_one.trans hv).le, Real.rpow_two]
  ring

/-- Harmonic layer of the affine clock `n+1+1/12`. -/
def realAffineHarmonicLayer (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  ∑ n ∈ S, b n *
    (Real.cos (2 * Real.pi * k * ((((n+1 : ℕ) : ℝ) + 1/12) * v)) -
      Real.cos (2 * Real.pi * k * (((n+1 : ℕ) : ℝ) * v)))

theorem continuous_realAffineHarmonicLayer (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    Continuous (realAffineHarmonicLayer S b k) := by
  unfold realAffineHarmonicLayer
  fun_prop

theorem abs_realAffineHarmonicLayer_le (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) (v : ℝ) :
    |realAffineHarmonicLayer S b k v| ≤ 2 * ∑ n ∈ S, |b n| := by
  unfold realAffineHarmonicLayer
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [abs_mul]
  have hcos : |Real.cos (2 * Real.pi * k * ((((n+1 : ℕ) : ℝ)+1/12)*v)) -
      Real.cos (2 * Real.pi * k * (((n+1 : ℕ) : ℝ)*v))| ≤ 2 := by
    exact (abs_sub _ _).trans ((add_le_add (Real.abs_cos_le_one _)
      (Real.abs_cos_le_one _)).trans_eq (by norm_num))
  calc _ ≤ |b n| * 2 := mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = _ := by ring

theorem factorialAffineHarmonicError_real (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) (v : ℝ) :
    factorialAffineHarmonicError S (fun n => (b n : ℂ)) k v =
      ((realHarmonicLayer S b k v - realAffineHarmonicLayer S b k v : ℝ) : ℂ) := by
  unfold factorialAffineHarmonicError realHarmonicLayer realAffineHarmonicLayer
  rw [← Finset.sum_sub_distrib]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

private theorem window_integrable_sq {f : ℝ → ℝ} {B : ℝ} (hf : Continuous f)
    (hB : ∀ v, |f v| ≤ B) : Integrable (fun v => f v ^ 2) criticalWindowMeasure := by
  refine Integrable.of_bound (hf.pow 2).aestronglyMeasurable (B ^ 2)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hB v) 2

theorem integrable_criticalWindow_harmonic_sq (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    Integrable (fun v => realHarmonicLayer S b k v ^ 2) criticalWindowMeasure :=
  window_integrable_sq (by unfold realHarmonicLayer; fun_prop)
    (abs_realHarmonicLayer_le S b k)

theorem integrable_criticalWindow_affine_sq (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    Integrable (fun v => realAffineHarmonicLayer S b k v ^ 2) criticalWindowMeasure :=
  window_integrable_sq (continuous_realAffineHarmonicLayer S b k)
    (abs_realAffineHarmonicLayer_le S b k)

theorem integrable_criticalWindow_affine_error_sq (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    Integrable (fun v => (realHarmonicLayer S b k v - realAffineHarmonicLayer S b k v) ^ 2)
      criticalWindowMeasure := by
  refine window_integrable_sq (by
    unfold realHarmonicLayer realAffineHarmonicLayer; fun_prop) (B := 4 * ∑ n ∈ S, |b n|) ?_
  intro v
  exact (abs_sub _ _).trans ((add_le_add (abs_realHarmonicLayer_le S b k v)
    (abs_realAffineHarmonicLayer_le S b k v)).trans_eq (by ring))

/-- High-scale affine error in one harmonic, without a support-cardinality factor. -/
theorem integral_criticalWindow_affine_error_sq_le {S : Finset ℕ} (b : ℕ → ℝ)
    (k : ℕ) {N : ℝ} (hN : 0 < N) (hS : ∀ n ∈ S, N ≤ ((n+1 : ℕ) : ℝ)) :
    (∫ v, (realHarmonicLayer S b k v - realAffineHarmonicLayer S b k v) ^ 2
      ∂criticalWindowMeasure) ≤
      (Real.pi ^ 2 * k / (140 * N)) * ∑ n ∈ S, b n ^ 2 := by
  have h := critical_factorialAffineHarmonicError_le S (fun n => (b n : ℂ)) k
  simp_rw [factorialAffineHarmonicError_real, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at h
  rw [integral_criticalWindowMeasure]
  refine h.trans ?_
  have hsum : (∑ n ∈ S, factorialAffineDefect (n+1) * b n ^ 2) ≤
      (1 / (140 * N)) * ∑ n ∈ S, b n ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    refine (factorialAffineDefect_bounds n).2.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have hnN := hS n hn
    push_cast at hnN
    linarith
  calc Real.pi ^ 2 * k * (∑ n ∈ S, factorialAffineDefect (n+1) * b n ^ 2)
      ≤ Real.pi ^ 2 * k * ((1 / (140 * N)) * ∑ n ∈ S, b n ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticPositivityTheory
