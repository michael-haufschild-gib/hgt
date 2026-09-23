import GaloisForLFunctions.RHTower.SelbergNodalCurvature
import GaloisForLFunctions.RHTower.SelbergWeightedPathEnergy
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Exact logarithmic degeneration of nodal path resistance

For the local nodal profile h(x)=x, reciprocal-amplitude resistance is exactly
2*arsinh(1/e). Its logarithmic singularity has finite part 2*log 2, while its
capacity coefficient tends to zero. This classifies the failure of an unqualified
regulator-uniform resistance bound. The profile is not asserted to be a Maass,
periodic, modular, or cuspidal source. Actual-source coordinate variation is
retained separately in SelbergMaassChordEnergy.
-/

open Set Filter Topology MeasureTheory
namespace GaloisForLFunctions.RHTower.SelbergNodalResistance
open SelbergNodalCurvature SelbergWeightedPathEnergy
noncomputable section

/-- Literal resistance of the amplitude-regularized local nodal profile. -/
def nodalResistance (e : ℝ) : ℝ := resistance (radius e) (-1) 1

/-- Actual primitive of the reciprocal regularized nodal amplitude. -/
theorem reciprocal_radius_hasPrimitive {e : ℝ} (he : 0 < e) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arsinh (t / e)) (1 / radius e x) x := by
  have h := (Real.hasDerivAt_arsinh (x / e)).comp x ((hasDerivAt_id x).div_const e)
  have hs : 1 + (x / e) ^ (2 : ℕ) = (x ^ (2 : ℕ) + e ^ (2 : ℕ)) / e ^ (2 : ℕ) := by
    field_simp
    ring
  have hc : (Real.sqrt (1 + (x / e) ^ (2 : ℕ)))⁻¹ * (1 / e) = 1 / radius e x := by
    rw [hs, Real.sqrt_div (add_nonneg (sq_nonneg x) (sq_nonneg e)),
      Real.sqrt_sq_eq_abs, abs_of_pos he]
    unfold radius
    field_simp [he.ne']
  simpa only [Function.comp_def, id_eq, hc] using h

/-- The inverse nodal amplitude is genuinely interval integrable for every positive regulator. -/
theorem reciprocal_radius_intervalIntegrable {e : ℝ} (he : 0 < e) (a b : ℝ) :
    IntervalIntegrable (fun x => 1 / radius e x) volume a b := by
  apply Continuous.intervalIntegrable
  apply continuous_const.div (Real.continuous_sqrt.comp ((continuous_id.pow 2).add continuous_const))
  intro x
  exact (radius_pos he x).ne'

/-- Exact nodal resistance obtained by actual FTC. -/
theorem nodalResistance_eq_arsinh {e : ℝ} (he : 0 < e) :
    nodalResistance e = 2 * Real.arsinh (1 / e) := by
  unfold nodalResistance resistance
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => reciprocal_radius_hasPrimitive he x) (reciprocal_radius_intervalIntegrable he _ _)]
  rw [neg_div, Real.arsinh_neg]
  ring

/-- Exact logarithmic singularity and its finite positive correction. -/
theorem nodalResistance_eq_log {e : ℝ} (he : 0 < e) :
    nodalResistance e = 2 * Real.log (1 + Real.sqrt (1 + e ^ (2 : ℕ))) - 2 * Real.log e := by
  rw [nodalResistance_eq_arsinh he, Real.arsinh]
  have hs : 1 + (1 / e) ^ (2 : ℕ) = (1 + e ^ (2 : ℕ)) / e ^ (2 : ℕ) := by
    field_simp
    ring
  rw [hs, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos he,
    ← add_div, Real.log_div (by positivity) he.ne']
  ring

/-- The finite part of the nodal resistance has its exact limiting value. -/
theorem nodalResistance_renormalized_tendsto :
    Tendsto (fun e : ℝ => nodalResistance e + 2 * Real.log e) (𝓝[>] 0) (𝓝 (2 * Real.log 2)) := by
  have hc : ContinuousAt (fun e : ℝ => 2 * Real.log (1 + Real.sqrt (1 + e ^ (2 : ℕ)))) 0 := by
    apply continuousAt_const.mul
    apply ContinuousAt.log
    · exact continuousAt_const.add ((continuous_const.add (continuous_id.pow 2)).sqrt.continuousAt)
    · norm_num
  have hlim : Tendsto (fun e : ℝ => 2 * Real.log (1 + Real.sqrt (1 + e ^ (2 : ℕ)))) (𝓝[>] 0) (𝓝 (2 * Real.log 2)) := by
    convert hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))) using 1
    norm_num
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  rw [nodalResistance_eq_log he]
  ring

/-- The resistance factor in the nodal path comparison is unbounded as the regulator vanishes. -/
theorem nodalResistance_tendsto_atTop : Tendsto nodalResistance (𝓝[>] 0) atTop := by
  have hlim : Tendsto (fun e : ℝ => -2 * Real.log e) (𝓝[>] 0) atTop := by
    simpa only [mul_comm] using
      (Real.tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg (by norm_num : (-2 : ℝ) < 0))
  apply tendsto_atTop_mono' (𝓝[>] 0) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with e he
  rw [nodalResistance_eq_log he]
  have hlog := Real.log_nonneg (show 1 ≤ 1 + Real.sqrt (1 + e ^ (2 : ℕ)) by
    linarith [Real.sqrt_nonneg (1 + e ^ (2 : ℕ))])
  linarith

/-- The capacity coefficient in the nodal endpoint lower bound tends to zero. -/
theorem nodal_capacity_tendsto_zero :
    Tendsto (fun e : ℝ => 2 / nodalResistance e) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp nodalResistance_tendsto_atTop).const_mul (2 : ℝ)
  simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using h

end
end GaloisForLFunctions.RHTower.SelbergNodalResistance
