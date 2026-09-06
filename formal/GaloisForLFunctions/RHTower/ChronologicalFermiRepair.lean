import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionHeat
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Geometric-series repair of the dyadic heat response

The dyadic difference of the chronological Bose defect is the Fermi response.
Repeated multiplication and addition recover the single exponential mode with
an exact error formula and an exponentially decaying full squared L² error.
The repair uses response products; it is not a linear arithmetic-dilation repair.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RHTower
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

def chronologicalFermi (t : ℝ) : ℝ := 1 / (Real.exp t + 1)

theorem chronologicalFermi_eq_dyadic (t : ℝ) (ht : 0 < t) :
    chronologicalFermi t = 2 * fusionBoseDefect (2*t) - fusionBoseDefect t := by
  rw [fusionBoseDefect_dyadic, if_pos ht]
  rfl

def chronologicalFermiRepair : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, t => chronologicalFermi t * (1 + chronologicalFermiRepair n t)

theorem chronologicalFermi_bounds (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ chronologicalFermi t ∧ chronologicalFermi t ≤ 1/2 := by
  have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  constructor
  · exact one_div_nonneg.mpr (by positivity)
  · unfold chronologicalFermi
    apply (div_le_iff₀ (by positivity : 0 < Real.exp t+1)).mpr
    linarith

theorem chronologicalFermi_fixed (t : ℝ) :
    chronologicalFermi t * (1 + Real.exp (-t)) = Real.exp (-t) := by
  rw [chronologicalFermi, Real.exp_neg]
  field_simp

theorem chronologicalFermiRepair_error (n : ℕ) (t : ℝ) :
    Real.exp (-t) - chronologicalFermiRepair n t =
      Real.exp (-t) * chronologicalFermi t ^ n := by
  induction n with
  | zero => simp [chronologicalFermiRepair]
  | succ n ih =>
    have hf := chronologicalFermi_fixed t
    rw [chronologicalFermiRepair, pow_succ]
    calc
      _ = chronologicalFermi t * (Real.exp (-t) - chronologicalFermiRepair n t) := by nlinarith [hf]
      _ = _ := by rw [ih]; ring

theorem chronologicalFermiRepair_sum (n : ℕ) (t : ℝ) :
    chronologicalFermiRepair n t =
      ∑ j ∈ Finset.range n, chronologicalFermi t ^ (j+1) := by
  induction n with
  | zero => simp [chronologicalFermiRepair]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have he := chronologicalFermiRepair_error n t
    have hf := chronologicalFermi_fixed t
    rw [chronologicalFermiRepair, pow_succ]
    nlinarith [congrArg (fun z : ℝ => z * (1-chronologicalFermi t)) he,
      congrArg (fun z : ℝ => z * chronologicalFermi t ^ n) hf]

theorem chronologicalFermiRepair_error_sq_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (Real.exp (-t) - chronologicalFermiRepair n t)^2 ≤
      (1/4:ℝ)^n * Real.exp (-2*t) := by
  rw [chronologicalFermiRepair_error, mul_pow]
  have hg := chronologicalFermi_bounds t ht
  have hgp : chronologicalFermi t ^ 2 ≤ (1/4:ℝ) := by nlinarith
  have hp := pow_le_pow_left₀ (sq_nonneg (chronologicalFermi t)) hgp n
  rw [← pow_mul, mul_comm n 2, pow_mul]
  have he : Real.exp (-t)^2 = Real.exp (-2*t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hp (Real.exp_pos (-2*t)).le]

theorem chronologicalFermi_continuous : Continuous chronologicalFermi := by
  exact continuous_const.div (Real.continuous_exp.add continuous_const) (fun t => by positivity)

theorem chronologicalFermiRepair_continuous (n : ℕ) : Continuous (chronologicalFermiRepair n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact chronologicalFermi_continuous.mul (continuous_const.add ih)

theorem chronologicalFermiRepair_error_integrable (n : ℕ) :
    IntegrableOn (fun t => (Real.exp (-t) - chronologicalFermiRepair n t)^2) (Ioi 0) := by
  have hb := (integrableOn_exp_mul_Ioi (a := (-2:ℝ)) (by linarith) 0).const_mul ((1/4:ℝ)^n)
  apply hb.mono' ((Real.continuous_exp.comp continuous_neg).sub
    (chronologicalFermiRepair_continuous n) |>.pow 2 |>.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact chronologicalFermiRepair_error_sq_le n t ht.le

def chronologicalFermiRepairEnergy (n : ℕ) : ℝ :=
  ∫ t in Ioi (0:ℝ), (Real.exp (-t) - chronologicalFermiRepair n t)^2

theorem chronologicalFermiRepairEnergy_bound (n : ℕ) :
    0 ≤ chronologicalFermiRepairEnergy n ∧
      chronologicalFermiRepairEnergy n ≤ (1/4:ℝ)^n / 2 := by
  constructor
  · exact integral_nonneg (fun t => sq_nonneg _)
  · have h := integral_mono_ae (chronologicalFermiRepair_error_integrable n)
      ((integrableOn_exp_mul_Ioi (a := (-2:ℝ)) (by linarith) 0).const_mul ((1/4:ℝ)^n))
      (show (fun t => (Real.exp (-t) - chronologicalFermiRepair n t)^2) ≤ᵐ[volume.restrict (Ioi 0)]
        (fun t => (1/4:ℝ)^n * Real.exp (-2*t)) by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact chronologicalFermiRepair_error_sq_le n t ht.le)
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : (-2:ℝ)<0) 0] at h
    simpa only [chronologicalFermiRepairEnergy, mul_zero, Real.exp_zero, neg_div_neg_eq,
      div_eq_mul_inv, inv_neg, neg_mul_neg, one_mul] using h

theorem chronologicalFermiRepairEnergy_tendsto :
    Tendsto chronologicalFermiRepairEnergy atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by positivity : (0:ℝ) ≤ 1/4) (by linarith : (1/4:ℝ) < 1)).div_const 2
  simp only [zero_div] at h
  exact squeeze_zero (fun n => (chronologicalFermiRepairEnergy_bound n).1)
    (fun n => (chronologicalFermiRepairEnergy_bound n).2) h

end RHTower
