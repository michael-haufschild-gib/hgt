import GaloisForLFunctions.RHTower.ChronologicalDampedRepair
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The actual positive-half-line L² norm for chronological heat repair

The Bose response and every finite raw or damped heat residual lie in L²(0,∞).
The real L² norm is identified with the square root of the actual squared integral.
Dilations by a factor at least one contract this norm. These facts justify norm
comparisons for the finite arithmetic residuals, without a formal-series shortcut.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RHTower
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

abbrev chronologicalPositiveVolume := volume.restrict (Ioi (0:ℝ))

def chronologicalL2Norm (f : ℝ → ℝ) : ℝ := lpNorm f 2 chronologicalPositiveVolume

theorem chronologicalL2Norm_nonneg (f : ℝ → ℝ) : 0 ≤ chronologicalL2Norm f := lpNorm_nonneg

theorem chronologicalBose_continuousOn : ContinuousOn fusionBoseDefect (Ioi 0) := by
  have h1 : ContinuousOn (fun t : ℝ => 1/t) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht)
  have h2 : ContinuousOn (fun t : ℝ => 1/(Real.exp t-1)) (Ioi 0) :=
    continuousOn_const.div (Real.continuous_exp.continuousOn.sub continuousOn_const)
      (fun t ht => ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)))
  apply (h1.sub h2).congr
  intro t ht
  change 0 < t at ht
  simp only [fusionBoseDefect, if_pos ht, Pi.sub_apply]

theorem chronologicalBose_sq_bound (t : ℝ) :
    fusionBoseDefect t ^ 2 ≤ 2 * (1+t^2)⁻¹ := by
  have hb := fusionBoseDefect_bounds t
  have hs : fusionBoseDefect t ^ 2 ≤ 1 := by nlinarith
  have hp : fusionBoseDefect t ^ 2 * t^2 ≤ 1 := by
    by_cases ht : t=0
    · simp [ht]
    · have ha : 0 < |t| := abs_pos.mpr ht
      have hh : fusionBoseDefect t * |t| ≤ 1 := (le_div_iff₀ ha).mp hb.2.2
      have hn : 0 ≤ fusionBoseDefect t * |t| := mul_nonneg hb.1 ha.le
      have hh2 : (fusionBoseDefect t * |t|)^2 ≤ 1 := by nlinarith
      simpa [mul_pow, sq_abs] using hh2
  apply (le_mul_inv_iff₀ (by positivity : 0 < 1+t^2)).mpr
  nlinarith

theorem chronologicalBose_memLp : MemLp fusionBoseDefect 2 chronologicalPositiveVolume := by
  have hm : AEStronglyMeasurable fusionBoseDefect chronologicalPositiveVolume :=
    chronologicalBose_continuousOn.aestronglyMeasurable (μ := volume) measurableSet_Ioi
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrable_inv_one_add_sq.const_mul (2:ℝ)).integrableOn.mono' (hm.pow 2)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact chronologicalBose_sq_bound t

theorem chronological_memLp_dilate {f : ℝ → ℝ}
    (hf : MemLp f 2 chronologicalPositiveVolume) (hc : ContinuousOn f (Ioi 0))
    {d : ℝ} (hd : 0 < d) : MemLp (fun t => f (d*t)) 2 chronologicalPositiveVolume := by
  have hcont : ContinuousOn (fun t => f (d*t)) (Ioi 0) :=
    hc.comp (continuous_const.mul continuous_id).continuousOn (fun t ht => mul_pos hd ht)
  apply (memLp_two_iff_integrable_sq (hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioi)).mpr
  have hi : IntegrableOn (fun t : ℝ => f t ^ (2:ℕ)) (Ioi (d*0)) := by
    rw [mul_zero]
    exact hf.integrable_sq
  exact (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => f t ^ (2:ℕ)) 0 hd).mpr hi

theorem chronologicalL2Norm_eq_sqrt {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f chronologicalPositiveVolume) :
    chronologicalL2Norm f = Real.sqrt (∫ t in Ioi (0:ℝ), f t ^ 2) := by
  rw [chronologicalL2Norm, lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp) hf]
  simp [Real.sqrt_eq_rpow, Real.norm_eq_abs]

theorem chronologicalL2Norm_dilate_le {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ioi 0)) {d : ℝ} (hd : 1 ≤ d) :
    chronologicalL2Norm (fun t => f (d*t)) ≤ chronologicalL2Norm f := by
  have hd0 : 0 < d := by linarith
  have hcont : ContinuousOn (fun t => f (d*t)) (Ioi 0) :=
    hc.comp (continuous_const.mul continuous_id).continuousOn (fun t ht => mul_pos hd0 ht)
  rw [chronologicalL2Norm_eq_sqrt (hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioi),
    chronologicalL2Norm_eq_sqrt (hc.aestronglyMeasurable (μ := volume) measurableSet_Ioi)]
  have he := integral_comp_mul_left_Ioi (fun t => f t^2) 0 hd0
  simp only [mul_zero, smul_eq_mul] at he
  rw [he]
  apply Real.sqrt_le_sqrt
  have hi : 0 ≤ ∫ t in Ioi (0:ℝ), f t^2 := integral_nonneg (fun t => sq_nonneg _)
  exact mul_le_of_le_one_left hi (inv_le_one_of_one_le₀ hd)

theorem chronologicalExponential_memLp :
    MemLp (fun t : ℝ => Real.exp (-t)) 2 chronologicalPositiveVolume := by
  apply (memLp_two_iff_integrable_sq (f := fun t : ℝ => Real.exp (-t))
    (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable).mpr
  have hi := integrableOn_exp_mul_Ioi (a := (-2:ℝ)) (by linarith) 0
  have he : (fun t : ℝ => Real.exp (-t)^2) = (fun t => Real.exp (-2*t)) := by
    funext t
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact hi

theorem chronologicalExponential_L2Norm_le_one :
    chronologicalL2Norm (fun t : ℝ => Real.exp (-t)) ≤ 1 := by
  rw [chronologicalL2Norm_eq_sqrt (f := fun t : ℝ => Real.exp (-t))
    (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable]
  have he : (fun t : ℝ => Real.exp (-t)^2) = (fun t => Real.exp (-2*t)) := by
    funext t
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he, integral_exp_mul_Ioi (by linarith : (-2:ℝ) < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  apply (Real.sqrt_le_left (by positivity : (0:ℝ) ≤ 1)).mpr
  linarith

theorem chronologicalRawHeatError_continuousOn (N : ℕ) :
    ContinuousOn (chronologicalRawHeatError N) (Ioi 0) := by
  apply (Real.continuous_exp.comp continuous_neg).continuousOn.add
  apply continuousOn_finsetSum
  intro k hk
  apply continuousOn_const.mul
  apply chronologicalBose_continuousOn.comp (continuous_const.mul continuous_id).continuousOn
  intro t ht
  change 0 < (k:ℝ)*t
  exact mul_pos (by exact_mod_cast (Finset.mem_Ioc.mp hk).1) (show 0 < t from ht)

theorem chronologicalRawHeatError_memLp (N : ℕ) :
    MemLp (chronologicalRawHeatError N) 2 chronologicalPositiveVolume := by
  apply chronologicalExponential_memLp.add
  apply memLp_finsetSum
  intro k hk
  exact (chronological_memLp_dilate chronologicalBose_memLp chronologicalBose_continuousOn
    (by exact_mod_cast (Finset.mem_Ioc.mp hk).1)).const_mul _

theorem chronologicalDampedHeatError_memLp (ε : ℝ) (N : ℕ) :
    MemLp (chronologicalDampedHeatError ε N) 2 chronologicalPositiveVolume := by
  apply chronologicalExponential_memLp.add
  apply memLp_finsetSum
  intro k hk
  exact (chronological_memLp_dilate chronologicalBose_memLp chronologicalBose_continuousOn
    (by exact_mod_cast (Finset.mem_Ioc.mp hk).1)).const_mul _

end RHTower
