import GaloisForLFunctions.RHTower.WeilPaperCauchyLattice
import GaloisForLFunctions.RHTower.WeilWorkDeficitSharedMass

/-!
# Simultaneous Cauchy sampling of the actual Weil measures

The shift-uniform Cauchy lattice bound controls the total sampled mass on the
whole integer lattice. Applying it after removing the actual common submeasure
gives an `ℓ¹` discrepancy bound paid by the native deficit and total mass error.
The boundary measure need not be atomic.
-/

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section

namespace RHTower.WeilSpectral

/-- Sampling a measure with the Cauchy probe at an integer site. -/
def paperCauchySample (μ : Measure ℝ) (k : ℕ) (n : ℤ) : ℝ :=
  ∫ y, paperCauchyKernel k ((n : ℝ) - y) ∂μ

theorem paperCauchySample_nonneg (μ : Measure ℝ) (k : ℕ) (n : ℤ) :
    0 ≤ paperCauchySample μ k n :=
  integral_nonneg (fun _ => paperCauchyKernel_nonneg _ _)

private theorem kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (k : ℕ) (n : ℤ) :
    Integrable (fun y => paperCauchyKernel k ((n : ℝ) - y)) μ := by
  have hc : Continuous (fun y : ℝ => paperCauchyKernel k ((n : ℝ) - y)) :=
    (continuous_paperCauchyKernel k).comp (continuous_const.sub continuous_id)
  exact (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (paperCauchyKernel_nonneg _ _)]
      exact paperCauchyKernel_le_one _ _)

private theorem sample_sum_le (μ : Measure ℝ) [IsFiniteMeasure μ] (k : ℕ) (s : Finset ℤ) :
    (∑ n ∈ s, paperCauchySample μ k n) ≤
      (2 + Real.pi / ((k : ℝ) + 1)) * μ.real univ := by
  unfold paperCauchySample
  rw [← integral_finsetSum s (fun n _ => kernel_integrable μ k n)]
  calc
    _ ≤ ∫ _ : ℝ, (2 + Real.pi / ((k : ℝ) + 1)) ∂μ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => paperCauchyKernel_nonneg _ _)
        (integrable_const _)
        (Eventually.of_forall fun y => sum_paperCauchyKernel_lattice_le k y s)
    _ = _ := by rw [integral_const, smul_eq_mul, mul_comm]

private theorem sample_summable_and_le (μ : Measure ℝ) [IsFiniteMeasure μ] (k : ℕ) :
    Summable (paperCauchySample μ k) ∧
      (∑' n : ℤ, paperCauchySample μ k n) ≤
        (2 + Real.pi / ((k : ℝ) + 1)) * μ.real univ :=
  ⟨summable_of_sum_le (paperCauchySample_nonneg μ k) (sample_sum_le μ k),
    Real.tsum_le_of_sum_le (paperCauchySample_nonneg μ k) (sample_sum_le μ k)⟩

/-- All sampled multiplicity mass is controlled by the actual number of zero copies. -/
theorem deficitOrdinate_cauchy_summable_and_le (k : ℕ) (T : ℝ) :
    Summable (paperCauchySample (deficitOrdinateMeasure.restrict (Ioc 0 T)) k) ∧
      (∑' n : ℤ, paperCauchySample (deficitOrdinateMeasure.restrict (Ioc 0 T)) k n) ≤
        (2 + Real.pi / ((k : ℝ) + 1)) * (finite_deficitWindow T).toFinset.card := by
  haveI := isFiniteMeasure_deficitOrdinateWindow T
  have h := sample_summable_and_le (deficitOrdinateMeasure.restrict (Ioc 0 T)) k
  rw [measureReal_restrict_apply_univ, measureReal_def,
    deficitOrdinateMeasure_Ioc, ENNReal.toReal_natCast] at h
  exact h

/-- Shared atoms contribute exactly the count-minus-deficit mass budget. -/
theorem deficitShared_cauchy_summable_and_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) :
    Summable (paperCauchySample ((deficitSharedMeasure hW).restrict (Ioc 0 T)) k) ∧
      (∑' n : ℤ, paperCauchySample ((deficitSharedMeasure hW).restrict (Ioc 0 T)) k n) ≤
        (2 + Real.pi / ((k : ℝ) + 1)) *
          ((finite_deficitWindow T).toFinset.card - deficitCount hW T) := by
  haveI := isFiniteMeasure_deficitSharedWindow hW T
  simpa only [measureReal_restrict_apply_univ, deficitSharedMeasure_real_Ioc] using
    sample_summable_and_le ((deficitSharedMeasure hW).restrict (Ioc 0 T)) k

/-- The canonical boundary measure admits simultaneous sampling without atomicity. -/
theorem deficitBoundary_cauchy_summable_and_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) :
    Summable (paperCauchySample ((boundaryMeasure hW).restrict (Ioc 0 T)) k) ∧
      (∑' n : ℤ, paperCauchySample ((boundaryMeasure hW).restrict (Ioc 0 T)) k n) ≤
        (2 + Real.pi / ((k : ℝ) + 1)) * (boundaryMeasure hW).real (Ioc 0 T) := by
  haveI := isFiniteMeasure_deficitBoundaryWindow hW T
  simpa only [measureReal_restrict_apply_univ] using
    sample_summable_and_le ((boundaryMeasure hW).restrict (Ioc 0 T)) k

private theorem sample_sub_common {μ ν χ : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure χ]
    (hχμ : χ ≤ μ) (hχν : χ ≤ ν) (k : ℕ) (n : ℤ) :
    paperCauchySample μ k n - paperCauchySample ν k n =
      paperCauchySample (μ - χ) k n - paperCauchySample (ν - χ) k n := by
  have hμ := integral_add_measure (kernel_integrable (μ - χ) k n) (kernel_integrable χ k n)
  have hν := integral_add_measure (kernel_integrable (ν - χ) k n) (kernel_integrable χ k n)
  rw [Measure.sub_add_cancel_of_le hχμ] at hμ
  rw [Measure.sub_add_cancel_of_le hχν] at hν
  unfold paperCauchySample
  rw [hμ, hν]
  ring

private theorem sample_sum_abs_sub_le_common {μ ν χ : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure χ]
    (hχμ : χ ≤ μ) (hχν : χ ≤ ν) (k : ℕ) (s : Finset ℤ) :
    (∑ n ∈ s, |paperCauchySample μ k n - paperCauchySample ν k n|) ≤
      (2 + Real.pi / ((k : ℝ) + 1)) * (μ.real univ + ν.real univ - 2 * χ.real univ) := by
  calc
    _ ≤ ∑ n ∈ s, (paperCauchySample (μ - χ) k n + paperCauchySample (ν - χ) k n) := by
      apply Finset.sum_le_sum
      intro n _
      rw [sample_sub_common hχμ hχν]
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (paperCauchySample_nonneg _ _ _),
        abs_of_nonneg (paperCauchySample_nonneg _ _ _)])
    _ ≤ (2 + Real.pi / ((k : ℝ) + 1)) *
        ((μ - χ).real univ + (ν - χ).real univ) := by
      rw [Finset.sum_add_distrib, mul_add]
      exact add_le_add (sample_sum_le (μ - χ) k s) (sample_sum_le (ν - χ) k s)
    _ = _ := by
      congr 1
      simp only [measureReal_def, Measure.sub_apply MeasurableSet.univ hχμ,
        Measure.sub_apply MeasurableSet.univ hχν,
        ENNReal.toReal_sub_of_le (hχμ univ) (measure_ne_top μ univ),
        ENNReal.toReal_sub_of_le (hχν univ) (measure_ne_top ν univ)]
      ring

/-- Every finite set of sample discrepancies is paid once by the actual common mass. -/
theorem sum_abs_deficitWindow_cauchy_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) (s : Finset ℤ) :
    (∑ n ∈ s, |paperCauchySample ((boundaryMeasure hW).restrict (Ioc 0 T)) k n -
      paperCauchySample (deficitOrdinateMeasure.restrict (Ioc 0 T)) k n|) ≤
      (2 + Real.pi / ((k : ℝ) + 1)) *
        ((boundaryMeasure hW).real (Ioc 0 T) - (finite_deficitWindow T).toFinset.card +
          2 * deficitCount hW T) := by
  haveI := isFiniteMeasure_deficitBoundaryWindow hW T
  haveI := isFiniteMeasure_deficitOrdinateWindow T
  haveI := isFiniteMeasure_deficitSharedWindow hW T
  have h := sample_sum_abs_sub_le_common
    (Measure.restrict_mono_measure (deficitSharedMeasure_le_boundary hW) (Ioc 0 T))
    (Measure.restrict_mono_measure (deficitSharedMeasure_le_ordinate hW) (Ioc 0 T)) k s
  have hν : (deficitOrdinateMeasure.restrict (Ioc 0 T)).real univ =
      ((finite_deficitWindow T).toFinset.card : ℝ) := by
    rw [measureReal_restrict_apply_univ, measureReal_def, deficitOrdinateMeasure_Ioc,
      ENNReal.toReal_natCast]
  have hχ : ((deficitSharedMeasure hW).restrict (Ioc 0 T)).real univ =
      ((finite_deficitWindow T).toFinset.card : ℝ) - deficitCount hW T := by
    rw [measureReal_restrict_apply_univ, deficitSharedMeasure_real_Ioc]
  rw [hν, hχ, measureReal_restrict_apply_univ] at h
  convert h using 1
  ring

/-- The entire Cauchy-sampled discrepancy is in `ℓ¹`. -/
theorem summable_abs_deficitWindow_cauchy_sub {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) :
    Summable (fun n : ℤ =>
      |paperCauchySample ((boundaryMeasure hW).restrict (Ioc 0 T)) k n -
        paperCauchySample (deficitOrdinateMeasure.restrict (Ioc 0 T)) k n|) :=
  summable_of_sum_le (fun _ => abs_nonneg _) (sum_abs_deficitWindow_cauchy_sub_le hW k T)

/-- Simultaneous recovery bound for all integer sites, with no sample-count loss. -/
theorem tsum_abs_deficitWindow_cauchy_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) :
    (∑' n : ℤ, |paperCauchySample ((boundaryMeasure hW).restrict (Ioc 0 T)) k n -
      paperCauchySample (deficitOrdinateMeasure.restrict (Ioc 0 T)) k n|) ≤
      (2 + Real.pi / ((k : ℝ) + 1)) *
        ((boundaryMeasure hW).real (Ioc 0 T) - (finite_deficitWindow T).toFinset.card +
          2 * deficitCount hW T) :=
  Real.tsum_le_of_sum_le (fun _ => abs_nonneg _) (sum_abs_deficitWindow_cauchy_sub_le hW k T)

end RHTower.WeilSpectral
