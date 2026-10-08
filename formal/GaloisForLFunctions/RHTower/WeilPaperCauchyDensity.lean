import GaloisForLFunctions.RHTower.WeilPaperCauchyLattice
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Stable Cauchy lattice sampling of integrable densities

The paper's Cauchy lattice mechanism extends to signed integrable densities.
Sampling is bounded from L1 to l1. For positive densities the total sampled
mass also has a positive lower bound, uniformly in the density's location.
-/

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section
namespace RHTower.WeilSpectral

/-- Integer-height Cauchy samples of a density with respect to Lebesgue measure. -/
def paperCauchyDensitySample (f : ℝ → ℝ) (k : ℕ) (n : ℤ) : ℝ :=
  ∫ y, paperCauchyKernel k ((n : ℝ) - y) * f y

private theorem kernel_mul_integrable {f : ℝ → ℝ} (hf : Integrable f)
    (k : ℕ) (n : ℤ) : Integrable (fun y => paperCauchyKernel k ((n : ℝ) - y) * f y) := by
  apply hf.bdd_mul (c := 1) ((continuous_paperCauchyKernel k).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    change ‖paperCauchyKernel k ((n : ℝ) - y)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (paperCauchyKernel_nonneg _ _)]
    exact paperCauchyKernel_le_one _ _

theorem paperCauchyDensitySample_nonneg {f : ℝ → ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) (n : ℤ) : 0 ≤ paperCauchyDensitySample f k n :=
  integral_nonneg fun y => mul_nonneg (paperCauchyKernel_nonneg _ _) (hf0 y)

private theorem sample_sum_le {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) (s : Finset ℤ) :
    (∑ n ∈ s, paperCauchyDensitySample f k n) ≤
      (2 + Real.pi / ((k : ℝ) + 1)) * ∫ y, f y := by
  unfold paperCauchyDensitySample
  rw [← integral_finsetSum s (fun n _ => kernel_mul_integrable hf k n), ← integral_const_mul]
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun y => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (paperCauchyKernel_nonneg _ _) (hf0 y)) (hf.const_mul _)
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_paperCauchyKernel_lattice_le k y s) (hf0 y)

theorem paperCauchyDensitySample_summable_nonneg {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) : Summable (paperCauchyDensitySample f k) :=
  summable_of_sum_le (paperCauchyDensitySample_nonneg hf0 k) (sample_sum_le hf hf0 k)

theorem tsum_paperCauchyDensitySample_le {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) :
    (∑' n : ℤ, paperCauchyDensitySample f k n) ≤
      (2 + Real.pi / ((k : ℝ) + 1)) * ∫ y, f y :=
  Real.tsum_le_of_sum_le (paperCauchyDensitySample_nonneg hf0 k) (sample_sum_le hf hf0 k)

theorem abs_paperCauchyDensitySample_le {f : ℝ → ℝ} (k : ℕ) (n : ℤ) :
    |paperCauchyDensitySample f k n| ≤ paperCauchyDensitySample (fun y => |f y|) k n := by
  unfold paperCauchyDensitySample
  simpa only [abs_mul, abs_of_nonneg (paperCauchyKernel_nonneg _ _)] using
    (abs_integral_le_integral_abs (f := fun y => paperCauchyKernel k ((n : ℝ) - y) * f y))

theorem summable_abs_paperCauchyDensitySample {f : ℝ → ℝ} (hf : Integrable f) (k : ℕ) :
    Summable (fun n : ℤ => |paperCauchyDensitySample f k n|) :=
  (paperCauchyDensitySample_summable_nonneg hf.abs (fun _ => abs_nonneg _) k).of_nonneg_of_le
    (fun _ => abs_nonneg _) (fun n => abs_paperCauchyDensitySample_le k n)

theorem tsum_abs_paperCauchyDensitySample_le {f : ℝ → ℝ} (hf : Integrable f) (k : ℕ) :
    (∑' n : ℤ, |paperCauchyDensitySample f k n|) ≤
      (2 + Real.pi / ((k : ℝ) + 1)) * ∫ y, |f y| := by
  exact (Summable.tsum_le_tsum (fun n => abs_paperCauchyDensitySample_le k n)
    (summable_abs_paperCauchyDensitySample hf k)
    (paperCauchyDensitySample_summable_nonneg hf.abs (fun _ => abs_nonneg _) k)).trans
    (tsum_paperCauchyDensitySample_le hf.abs (fun _ => abs_nonneg _) k)

theorem paperCauchyDensitySample_sub {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (k : ℕ) (n : ℤ) :
    paperCauchyDensitySample (fun y => f y - g y) k n =
      paperCauchyDensitySample f k n - paperCauchyDensitySample g k n := by
  simp only [paperCauchyDensitySample, mul_sub]
  exact integral_sub (kernel_mul_integrable hf k n) (kernel_mul_integrable hg k n)

/-- Global lattice recovery error is controlled by the density's L1 error. -/
theorem tsum_abs_paperCauchyDensitySample_sub_le {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (k : ℕ) :
    (∑' n : ℤ, |paperCauchyDensitySample f k n - paperCauchyDensitySample g k n|) ≤
      (2 + Real.pi / ((k : ℝ) + 1)) * ∫ y, |f y - g y| := by
  simpa only [Pi.sub_def, paperCauchyDensitySample_sub hf hg] using
    tsum_abs_paperCauchyDensitySample_le (hf.sub hg) k

private theorem lattice_mul_integrable {f : ℝ → ℝ} (hf : Integrable f) (k : ℕ) :
    Integrable (fun y => (∑' n : ℤ, paperCauchyKernel k ((n : ℝ) - y)) * f y) := by
  apply hf.bdd_mul (c := 2 + Real.pi / ((k : ℝ) + 1))
    ((Measurable.tsum fun n : ℤ => ((continuous_paperCauchyKernel k).comp
      (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable)
  exact Eventually.of_forall fun y => by
    change ‖∑' n : ℤ, paperCauchyKernel k ((n : ℝ) - y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => paperCauchyKernel_nonneg _ _)]
    exact tsum_paperCauchyKernel_lattice_le k y

/-- Exact sum/integral interchange for the entire integer lattice. -/
theorem tsum_paperCauchyDensitySample_eq {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) :
    (∑' n : ℤ, paperCauchyDensitySample f k n) =
      ∫ y, (∑' n : ℤ, paperCauchyKernel k ((n : ℝ) - y)) * f y := by
  have hs0 := paperCauchyDensitySample_summable_nonneg hf hf0 k
  change Summable (fun n : ℤ => ∫ y, paperCauchyKernel k ((n : ℝ) - y) * f y) at hs0
  have hs : Summable (fun n : ℤ => ∫ y, ‖paperCauchyKernel k ((n : ℝ) - y) * f y‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (paperCauchyKernel_nonneg _ _) (hf0 _))] using hs0
  unfold paperCauchyDensitySample
  rw [integral_tsum_of_summable_integral_norm (kernel_mul_integrable hf k) hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => tsum_mul_right

/-- A positive density cannot disappear between integer sampling sites. -/
theorem paperCauchyDensitySample_mass_lower {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ y, 0 ≤ f y) (k : ℕ) :
    paperCauchyKernel k (1 / 2) * (∫ y, f y) ≤
      ∑' n : ℤ, paperCauchyDensitySample f k n := by
  rw [tsum_paperCauchyDensitySample_eq hf hf0, ← integral_const_mul]
  exact integral_mono (hf.const_mul _) (lattice_mul_integrable hf k) fun y =>
    mul_le_mul_of_nonneg_right (paperCauchyKernel_half_le_lattice k y) (hf0 y)

end RHTower.WeilSpectral
