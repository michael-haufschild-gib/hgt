import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheEscapeIsATailPhenomenon

/-!
# The actual long-modulus Möbius quadrature function

The floor-cutoff function is the pointwise sum of bounded-interval indicators.
Positive damping makes the integrals of their absolute values summable, so the
actual function is integrable and its integral is the full harmonic tail.
-/

noncomputable section
open MeasureTheory Set ArithmeticFunction
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
set_option autoImplicit false

/-- The actual power-damped Möbius weight. -/
def pmLongModulusWeight (ε : ℝ) (d : ℕ) : ℝ :=
  (moebius d : ℝ) * (d : ℝ) ^ (-ε)

/-- The long-modulus floor function, extended by zero on the nonpositive half-line. -/
def pmLongModulusFunction (ε : ℝ) (n D : ℕ) (u : ℝ) : ℝ :=
  if 0 < u then ∑ d ∈ Finset.Ioc D ⌊(n : ℝ) / u⌋₊, pmLongModulusWeight ε d else 0

/-- One modulus contributes its signed weight on the exact interval `(0,n/d]`. -/
def pmLongModulusIndicatorTerm (ε : ℝ) (n D d : ℕ) : ℝ → ℝ :=
  if D < d then (Ioc (0 : ℝ) ((n : ℝ) / d)).indicator (fun _ => pmLongModulusWeight ε d)
    else 0

private theorem longModulus_mem_iff {u : ℝ} (hu : 0 < u) (n : ℕ) {d : ℕ} (hd : 0 < d) :
    u ∈ Ioc (0 : ℝ) ((n : ℝ) / d) ↔ d ≤ ⌊(n : ℝ) / u⌋₊ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Nat.le_floor_iff (div_nonneg (Nat.cast_nonneg n) hu.le)]
  constructor
  · intro hx
    rw [le_div_iff₀ hu]
    simpa only [mul_comm] using (le_div_iff₀ hdR).mp hx.2
  · intro hx
    refine ⟨hu, ?_⟩
    rw [le_div_iff₀ hdR]
    simpa only [mul_comm] using (le_div_iff₀ hu).mp hx

/-- The floor cutoff agrees pointwise, including at every discontinuity, with its indicator series. -/
theorem pmLongModulusFunction_eq_tsum (ε : ℝ) (n D : ℕ) (u : ℝ) :
    pmLongModulusFunction ε n D u = ∑' d, pmLongModulusIndicatorTerm ε n D d u := by
  classical
  by_cases hu : 0 < u
  · rw [pmLongModulusFunction, if_pos hu]
    have hterm (d : ℕ) (hd : d ∈ Finset.Ioc D ⌊(n : ℝ) / u⌋₊) :
        pmLongModulusIndicatorTerm ε n D d u = pmLongModulusWeight ε d := by
      obtain ⟨hD, hd⟩ := Finset.mem_Ioc.mp hd
      rw [pmLongModulusIndicatorTerm, if_pos hD, indicator_of_mem
        ((longModulus_mem_iff hu n (by omega : 0 < d)).mpr hd)]
    calc
      _ = ∑ d ∈ Finset.Ioc D ⌊(n : ℝ) / u⌋₊, pmLongModulusIndicatorTerm ε n D d u :=
        Finset.sum_congr rfl (fun d hd => (hterm d hd).symm)
      _ = _ := (tsum_eq_sum fun d hd => by
        by_cases hD : D < d
        · rw [pmLongModulusIndicatorTerm, if_pos hD]
          apply indicator_of_notMem
          intro hx
          exact hd (Finset.mem_Ioc.mpr ⟨hD,
            (longModulus_mem_iff hu n (by omega : 0 < d)).mp hx⟩)
        · simp only [pmLongModulusIndicatorTerm, if_neg hD, Pi.zero_apply]).symm
  · rw [pmLongModulusFunction, if_neg hu]
    have hz (d : ℕ) : pmLongModulusIndicatorTerm ε n D d u = 0 := by
      by_cases hD : D < d
      · rw [pmLongModulusIndicatorTerm, if_pos hD]
        exact indicator_of_notMem (fun hx => hu hx.1) _
      · simp only [pmLongModulusIndicatorTerm, if_neg hD, Pi.zero_apply]
    simp only [hz, tsum_zero]

private theorem integrable_longModulusTerm (ε : ℝ) (n D d : ℕ) :
    Integrable (pmLongModulusIndicatorTerm ε n D d) := by
  by_cases hD : D < d
  · rw [pmLongModulusIndicatorTerm, if_pos hD, integrable_indicator_iff measurableSet_Ioc]
    exact continuous_const.integrableOn_Ioc
  · simp only [pmLongModulusIndicatorTerm, if_neg hD]
    exact integrable_zero ℝ ℝ volume

private theorem integral_longModulusTerm (ε : ℝ) (n D d : ℕ) :
    (∫ u, pmLongModulusIndicatorTerm ε n D d u) =
      if D < d then (n : ℝ) * (pmLongModulusWeight ε d / d) else 0 := by
  by_cases hD : D < d
  · rw [pmLongModulusIndicatorTerm, if_pos hD, if_pos hD, integral_indicator_const _ measurableSet_Ioc,
      Real.volume_real_Ioc, sub_zero, max_eq_left (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg d)),
      smul_eq_mul]
    ring
  · simp only [pmLongModulusIndicatorTerm, if_neg hD, Pi.zero_apply, integral_zero]

private theorem integral_norm_longModulusTerm (ε : ℝ) (n D d : ℕ) :
    (∫ u, ‖pmLongModulusIndicatorTerm ε n D d u‖) =
      if D < d then (n : ℝ) * (|pmLongModulusWeight ε d| / d) else 0 := by
  by_cases hD : D < d
  · simp only [pmLongModulusIndicatorTerm, if_pos hD, norm_indicator_eq_indicator_norm, Real.norm_eq_abs]
    rw [integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc, sub_zero,
      max_eq_left (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg d)), smul_eq_mul]
    ring
  · simp only [pmLongModulusIndicatorTerm, if_neg hD, Pi.zero_apply, norm_zero, integral_zero]

/-- The reciprocal weight has the exact absolutely summable Dirichlet exponent. -/
theorem pmLongModulusWeight_div_eq (ε : ℝ) (d : ℕ) :
    pmLongModulusWeight ε d / d = (moebius d : ℝ) * (d : ℝ) ^ (-(1 + ε)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [pmLongModulusWeight]
  · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [pmLongModulusWeight, show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub_one hdR]
    ring

private theorem abs_pmLongModulusWeight_div_le (ε : ℝ) (d : ℕ) :
    |pmLongModulusWeight ε d| / d ≤ (d : ℝ) ^ (-(1 + ε)) := by
  have hμ : |(moebius d : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_moebius_le_one
  calc
    _ = |pmLongModulusWeight ε d / d| := by
      have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      rw [abs_div, abs_of_nonneg hdR]
    _ = |(moebius d : ℝ)| * (d : ℝ) ^ (-(1 + ε)) := by
      rw [pmLongModulusWeight_div_eq, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) hμ

private theorem summable_integral_norm_longModulusTerm {ε : ℝ} (hε : 0 < ε) (n D : ℕ) :
    Summable (fun d => ∫ u, ‖pmLongModulusIndicatorTerm ε n D d u‖) := by
  refine Summable.of_nonneg_of_le (fun d => integral_nonneg (fun u => norm_nonneg _))
    (fun d => ?_) ((Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)).mul_left (n : ℝ))
  rw [integral_norm_longModulusTerm]
  split_ifs with hD
  · exact mul_le_mul_of_nonneg_left (abs_pmLongModulusWeight_div_le ε d) (Nat.cast_nonneg n)
  · exact mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- Positive damping makes the actual long-modulus floor function Lebesgue integrable. -/
theorem integrable_pmLongModulusFunction {ε : ℝ} (hε : 0 < ε) (n D : ℕ) :
    Integrable (pmLongModulusFunction ε n D) := by
  rw [funext (pmLongModulusFunction_eq_tsum ε n D)]
  exact HTGeometry.integrable_tsum_of_summable_integral_norm
    (integrable_longModulusTerm ε n D) (summable_integral_norm_longModulusTerm hε n D)

/-- Its integral retains the entire signed harmonic tail beyond the modulus cutoff. -/
theorem integral_pmLongModulusFunction {ε : ℝ} (hε : 0 < ε) (n D : ℕ) :
    (∫ u, pmLongModulusFunction ε n D u) =
      (n : ℝ) * ∑' d : ℕ, if D < d then pmLongModulusWeight ε d / d else 0 := by
  rw [funext (pmLongModulusFunction_eq_tsum ε n D),
    ← integral_tsum_of_summable_integral_norm (integrable_longModulusTerm ε n D)
      (summable_integral_norm_longModulusTerm hε n D), ← tsum_mul_left]
  apply tsum_congr
  intro d
  rw [integral_longModulusTerm]
  split_ifs <;> simp only [mul_zero]

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
