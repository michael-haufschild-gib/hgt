import GaloisForLFunctions.RHTower.WeilWorkDeficitZeroKernel
import GaloisForLFunctions.RHTower.WeilWorkDeficitProjection

/-!
# Finite-height Fourier transport of the actual Xi divisor

Summing the per-copy endpoint error gives a sublinear raw transport error, uniformly in
frequency. Line-conjugate projection then identifies the actual ordinate Fourier integral
at each fixed frequency, with every zero multiplicity retained.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral

private def copyFourierIntegral (k T : ℝ) (q : XiZeroCopy) : ℂ :=
  ∫ t in Ioc 0 T, Complex.exp (((k * t : ℝ) : ℂ) * I) * (copyPoisson 2 t q : ℂ)

private def copyWindowMultiplier (k T : ℝ) (q : XiZeroCopy) : ℂ :=
  (Ioc 0 T).indicator
    (fun r => ((Real.pi * Real.exp (-((2 - (q.1 : ℂ).re) * |k|)) : ℝ) : ℂ) *
      Complex.exp (((k * r : ℝ) : ℂ) * I)) (q.1 : ℂ).im

private theorem copyWindowMultiplier_eq_zero_of_not_mem (k T : ℝ) (q : XiZeroCopy)
    (hq : q ∉ (finite_deficitWindow T).toFinset) : copyWindowMultiplier k T q = 0 := by
  apply indicator_of_notMem
  simpa only [Set.Finite.mem_toFinset, deficitWindow, Set.mem_setOf_eq, Set.mem_Ioc] using hq

private theorem summable_copyWindowMultiplier (k T : ℝ) :
    Summable (copyWindowMultiplier k T) :=
  summable_of_ne_finset_zero (copyWindowMultiplier_eq_zero_of_not_mem k T)

private theorem tsum_copyWindowMultiplier (k T : ℝ) :
    ∑' q : XiZeroCopy, copyWindowMultiplier k T q =
      (Real.pi : ℂ) * ∑ q ∈ (finite_deficitWindow T).toFinset,
        (Real.exp (-(2 - (q.1 : ℂ).re) * |k|) : ℂ) *
          Complex.exp (((k * (q.1 : ℂ).im : ℝ) : ℂ) * I) := by
  rw [tsum_eq_sum (copyWindowMultiplier_eq_zero_of_not_mem k T), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hmem : (q.1 : ℂ).im ∈ Ioc 0 T := by
    simpa only [Set.Finite.mem_toFinset, deficitWindow, Set.mem_setOf_eq, Set.mem_Ioc] using hq
  rw [copyWindowMultiplier, indicator_of_mem hmem]
  simp only [Complex.ofReal_mul, neg_mul, mul_assoc]

private theorem summable_copyLeakage {T : ℝ} (hT : 1 ≤ T) :
    Summable (fun q : XiZeroCopy => deficitPoissonLeakage T (q.1 : ℂ).im) := by
  have h := (integrable_deficitOrdinatePoissonLeakage hT).summable_integral
  have hn (q : XiZeroCopy) : ‖deficitPoissonLeakage T (q.1 : ℂ).im‖ =
      deficitPoissonLeakage T (q.1 : ℂ).im :=
    Real.norm_of_nonneg (deficitPoissonLeakage_nonneg T _)
  simpa only [deficitOrdinateMeasure, integral_dirac, hn] using h

private theorem integral_copyLeakage {T : ℝ} (hT : 1 ≤ T) :
    (∫ r, deficitPoissonLeakage T r ∂deficitOrdinateMeasure) =
      ∑' q : XiZeroCopy, deficitPoissonLeakage T (q.1 : ℂ).im := by
  have h := integral_sum_measure (integrable_deficitOrdinatePoissonLeakage hT)
  simpa only [deficitOrdinateMeasure, integral_dirac] using h

/-- Error before projecting the true horizontal copy multipliers. -/
def deficitZeroRawFourierError (k T : ℝ) : ℂ :=
  (∫ t in Ioc 0 T, Complex.exp (((k * t : ℝ) : ℂ) * I) *
    ((logDeriv xi ((2 : ℂ) + t * I)).re : ℂ)) -
  (Real.pi : ℂ) * ∑ q ∈ (finite_deficitWindow T).toFinset,
    (Real.exp (-(2 - (q.1 : ℂ).re) * |k|) : ℂ) *
      Complex.exp (((k * (q.1 : ℂ).im : ℝ) : ℂ) * I)

/-- The full actual-copy transport error is bounded uniformly in frequency. -/
theorem norm_deficitZeroRawFourierError_le {T : ℝ} (hT : 1 ≤ T) (k : ℝ) :
    ‖deficitZeroRawFourierError k T‖ ≤
      (3 / 2) * ∫ r, deficitPoissonLeakage T r ∂deficitOrdinateMeasure := by
  have hA := hasSum_deficitCopyFourierIntegral (show 0 ≤ T by linarith) k
  have hB := summable_copyWindowMultiplier k T
  have hL := (summable_copyLeakage hT).mul_left (3 / 2)
  have hb (q : XiZeroCopy) : ‖copyFourierIntegral k T q - copyWindowMultiplier k T q‖ ≤
      (3 / 2) * deficitPoissonLeakage T (q.1 : ℂ).im :=
    norm_deficitCopyFourierIntegral_sub_le (by linarith) k q
  have hnorm : Summable (fun q : XiZeroCopy =>
      ‖copyFourierIntegral k T q - copyWindowMultiplier k T q‖) :=
    hL.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have heq : deficitZeroRawFourierError k T =
      ∑' q : XiZeroCopy, (copyFourierIntegral k T q - copyWindowMultiplier k T q) := by
    unfold copyFourierIntegral
    rw [hA.summable.tsum_sub hB, tsum_copyWindowMultiplier, hA.tsum_eq]
    rfl
  rw [heq]
  calc
    _ ≤ ∑' q : XiZeroCopy, ‖copyFourierIntegral k T q - copyWindowMultiplier k T q‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : XiZeroCopy, (3 / 2) * deficitPoissonLeakage T (q.1 : ℂ).im :=
      hnorm.tsum_le_tsum hb hL
    _ = _ := by rw [(summable_copyLeakage hT).tsum_mul_left, ← integral_copyLeakage hT]

/-- Raw endpoint transport remains sublinear even when frequency varies with height. -/
theorem tendsto_norm_deficitZeroRawFourierError_div (k : ℝ → ℝ) :
    Tendsto (fun T : ℝ => ‖deficitZeroRawFourierError (k T) T‖ / T) atTop (𝓝 0) := by
  have h := tendsto_integral_deficitOrdinatePoissonLeakage_div.const_mul (3 / 2 : ℝ)
  rw [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact div_nonneg (norm_nonneg _) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (norm_deficitZeroRawFourierError_le hT (k T)) (show 0 ≤ T by linarith)

theorem tendsto_deficitZeroRawFourierError_div (k : ℝ → ℝ) :
    Tendsto (fun T : ℝ => deficitZeroRawFourierError (k T) T / (T : ℂ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_norm_deficitZeroRawFourierError_div k).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < T)]

/-- Restricting the actual ordinate measure gives exactly the finite copy character sum. -/
theorem integral_deficitOrdinateWindow_character (k T : ℝ) :
    (∫ r in Ioc 0 T, Complex.exp (((k * r : ℝ) : ℂ) * I) ∂deficitOrdinateMeasure) =
      ∑ q ∈ (finite_deficitWindow T).toFinset,
        Complex.exp (((k * (q.1 : ℂ).im : ℝ) : ℂ) * I) := by
  haveI := isFiniteMeasure_deficitOrdinateWindow T
  let f : ℝ → ℂ := fun r => Complex.exp (((k * r : ℝ) : ℂ) * I)
  have hi : IntegrableOn f (Ioc 0 T) deficitOrdinateMeasure := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun r => ?_)
    simp [f, Complex.norm_exp]
  have hi' := hi.integrable_indicator measurableSet_Ioc
  change (∫ r in Ioc 0 T, f r ∂deficitOrdinateMeasure) = _
  rw [← integral_indicator measurableSet_Ioc]
  have hsum := integral_sum_measure hi'
  simp only [integral_dirac] at hsum
  rw [deficitOrdinateMeasure, hsum,
    tsum_eq_sum (s := (finite_deficitWindow T).toFinset) (fun q hq => ?_)]
  · apply Finset.sum_congr rfl
    intro q hq
    apply indicator_of_mem
    simpa only [Set.Finite.mem_toFinset, deficitWindow, Set.mem_setOf_eq, Set.mem_Ioc] using hq
  · apply indicator_of_notMem
    simpa only [Set.Finite.mem_toFinset, deficitWindow, Set.mem_setOf_eq, Set.mem_Ioc] using hq

/-- Forward Fourier error comparing the actual Xi logarithmic derivative with its ordinate measure. -/
def deficitZeroFourierError (k T : ℝ) : ℂ :=
  (∫ t in Ioc 0 T, Complex.exp (((k * t : ℝ) : ℂ) * I) *
    ((logDeriv xi ((2 : ℂ) + t * I)).re : ℂ)) -
  ((Real.pi * Real.exp (-((3 / 2) * |k|)) : ℝ) : ℂ) *
    ∫ r in Ioc 0 T, Complex.exp (((k * r : ℝ) : ℂ) * I) ∂deficitOrdinateMeasure

private theorem deficitZeroFourierError_eq (k T : ℝ) :
    deficitZeroFourierError k T = deficitZeroRawFourierError k T +
      (Real.pi : ℂ) * deficitZeroProjectionError k T := by
  rw [deficitZeroFourierError, integral_deficitOrdinateWindow_character,
    deficitZeroRawFourierError, deficitZeroProjectionError]
  simp only [Complex.ofReal_mul, neg_mul]
  ring

/-- The actual zero Fourier transport has sublinear error at every fixed frequency. -/
theorem tendsto_deficitZeroFourierError_div (k : ℝ) :
    Tendsto (fun T : ℝ => deficitZeroFourierError k T / (T : ℂ)) atTop (𝓝 0) := by
  have h := (tendsto_deficitZeroRawFourierError_div (fun _ => k)).add
    ((tendsto_deficitZeroProjectionError_div k).const_mul (Real.pi : ℂ))
  simpa only [deficitZeroFourierError_eq, add_div, mul_div_assoc, mul_zero, add_zero] using h

end RHTower.WeilSpectral
end
