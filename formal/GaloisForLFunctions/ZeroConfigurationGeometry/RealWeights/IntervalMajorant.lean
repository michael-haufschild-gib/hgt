import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convolution


/-!
# Smoothed interval majorants

Enlarge an interval by `R`, convolve with a nonnegative kernel, and divide
by its central mass. The result majorizes the original interval. Its total
mass is exactly the enlarged length times the ratio of full to central mass.
-/

open MeasureTheory Set Filter
open scoped Topology Convolution

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- An interval enlarged by `R`, smoothed by a nonnegative kernel and normalized
by the kernel mass in `[-R,R]`. -/
def intervalKernelMajorant (K : ℝ → ℝ) (x y R t : ℝ) : ℝ :=
  (∫ u in (x - R)..(y + R), K (t - u)) / ∫ u in (-R)..R, K u

/-- Smoothing an enlarged interval preserves nonnegativity. -/
theorem intervalKernelMajorant_nonneg {K : ℝ → ℝ} {x y R : ℝ}
    (hK : ∀ t, 0 ≤ K t) (hxy : x ≤ y) (hR : 0 ≤ R)
    (hC : 0 < ∫ u in (-R)..R, K u) (t : ℝ) :
    0 ≤ intervalKernelMajorant K x y R t := by
  exact div_nonneg (intervalIntegral.integral_nonneg
    (by linarith only [hxy, hR]) (fun u _ => hK (t - u))) hC.le

/-- Every point of the original interval sees all the central kernel mass. -/
theorem one_le_intervalKernelMajorant {K : ℝ → ℝ} {x y R t : ℝ}
    (hKc : Continuous K) (hK : ∀ t, 0 ≤ K t) (hR : 0 ≤ R)
    (hC : 0 < ∫ u in (-R)..R, K u) (ht : t ∈ Icc x y) :
    1 ≤ intervalKernelMajorant K x y R t := by
  have hcont : Continuous fun u : ℝ => K (t - u) :=
    hKc.comp (continuous_const.sub continuous_id)
  have hle := intervalIntegral.integral_mono_interval
    (show x - R ≤ t - R by linarith only [ht.1])
    (show t - R ≤ t + R by linarith only [hR])
    (show t + R ≤ y + R by linarith only [ht.2])
    (Eventually.of_forall fun u => hK (t - u))
    (hcont.intervalIntegrable (μ := volume) (x - R) (y + R))
  have hcentral : (∫ u in (t - R)..(t + R), K (t - u)) =
      ∫ u in (-R)..R, K u := by
    rw [intervalIntegral.integral_comp_sub_left]
    congr 1 <;> ring
  rw [hcentral] at hle
  exact (one_le_div hC).mpr hle

/-- The smoothed majorant has exactly the enlarged interval length times the
ratio of full kernel mass to central kernel mass. -/
theorem integral_intervalKernelMajorant {K : ℝ → ℝ} {x y R : ℝ}
    (hKi : Integrable K) (hxy : x ≤ y) (hR : 0 ≤ R) :
    (∫ t, intervalKernelMajorant K x y R t) =
      (y - x + 2 * R) * (∫ t, K t) / (∫ t in (-R)..R, K t) := by
  let F : ℝ → ℝ := (Icc (x - R) (y + R)).indicator (fun _ => 1)
  have hF : Integrable F := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hab : x - R ≤ y + R := by linarith only [hxy, hR]
  have hconv (t : ℝ) : (F ⋆[ContinuousLinearMap.mul ℝ ℝ] K) t =
      ∫ u in (x - R)..(y + R), K (t - u) := by
    rw [convolution_def]
    have he : (fun u => ContinuousLinearMap.mul ℝ ℝ (F u) (K (t - u))) =
        (Icc (x - R) (y + R)).indicator (fun u => K (t - u)) := by
      funext u
      simp only [ContinuousLinearMap.mul_apply', F, Set.indicator_apply]
      split_ifs <;> simp only [one_mul, zero_mul]
    rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
  have hFm : (∫ u, F u) = y - x + 2 * R := by
    rw [show F = (Icc (x - R) (y + R)).indicator (fun _ => 1) from rfl,
      integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
    ring
  have he : (fun t => intervalKernelMajorant K x y R t) =
      fun t => (F ⋆[ContinuousLinearMap.mul ℝ ℝ] K) t / (∫ u in (-R)..R, K u) := by
    funext t
    rw [intervalKernelMajorant, hconv]
  rw [he, integral_div, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hF hKi, hFm]
  rw [ContinuousLinearMap.mul_apply']

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.one_le_intervalKernelMajorant

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.integral_intervalKernelMajorant
