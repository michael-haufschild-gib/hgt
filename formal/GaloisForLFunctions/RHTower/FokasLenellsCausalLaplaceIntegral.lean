import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorCriterion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual Laplace integrals of completed causal vector orbits

Positive exponential damping makes every continuous vector orbit integrable
on the whole positive ray. The resulting actual Bochner integral is a bounded
linear map with the reciprocal damping bound. No operator-valued integral in
operator norm, and no bounded-generator assumption, is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance fokasLenellsCausalLaplaceIntegralInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- The actual completed vector orbit with strictly positive exponential damping. -/
def causalLaplaceOrbit (a : ℝ) (u : hardyL2ᗮ) (r : ℝ) : hardyL2ᗮ :=
  Real.exp (-Real.exp a*r) • causalForwardOrbit u r

/-- Every damped vector orbit is continuous in its actual lower Hardy norm. -/
theorem causalLaplaceOrbit_continuous (a : ℝ) (u : hardyL2ᗮ) : Continuous (causalLaplaceOrbit a u) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (causalForwardOrbit_continuous u)

/-- Damping leaves the actual initial datum unchanged. -/
theorem causalLaplaceOrbit_zero (a : ℝ) (u : hardyL2ᗮ) : causalLaplaceOrbit a u 0 = u := by
  simp only [causalLaplaceOrbit,mul_zero,Real.exp_zero,causalForwardOrbit_zero,one_smul]

/-- The actual damped orbit has its global scalar exponential majorant. -/
theorem causalLaplaceOrbit_norm_le (a r : ℝ) (u : hardyL2ᗮ) :
    ‖causalLaplaceOrbit a u r‖ ≤ Real.exp (-Real.exp a*r) * ‖u‖ := by
  rw [causalLaplaceOrbit,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (causalLowerCauchyEvolution_norm_le r.toNNReal u) (Real.exp_pos _).le

/-- The entire positive-time damped vector orbit is genuinely Bochner integrable. -/
theorem causalLaplaceOrbit_integrable (a : ℝ) (u : hardyL2ᗮ) :
    IntegrableOn (causalLaplaceOrbit a u) (Ioi (0:ℝ)) volume := by
  have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos (Real.exp_pos a)) 0).mul_const ‖u‖
  apply Integrable.mono' hi (causalLaplaceOrbit_continuous a u).aestronglyMeasurable.restrict
  exact Eventually.of_forall (fun r => causalLaplaceOrbit_norm_le a r u)

/-- Every actual damped orbit vanishes at positive infinity. -/
theorem causalLaplaceOrbit_tendsto (a : ℝ) (u : hardyL2ᗮ) :
    Tendsto (causalLaplaceOrbit a u) atTop (𝓝 0) := by
  have he : Tendsto (fun r : ℝ => Real.exp (-Real.exp a*r)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    convert tendsto_neg_atTop_atBot.comp
      (Tendsto.const_mul_atTop (Real.exp_pos a) tendsto_id) using 1
    funext r
    simp only [Function.comp_apply,id_eq,neg_mul]
  have he' : Tendsto (fun r : ℝ => Real.exp (-Real.exp a*r)*‖u‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using he.mul_const ‖u‖
  exact squeeze_zero_norm' (Eventually.of_forall (fun r => causalLaplaceOrbit_norm_le a r u)) he'

private theorem laplace_integral_bound (a : ℝ) (u : hardyL2ᗮ) :
    ‖∫ r in Ioi (0:ℝ), causalLaplaceOrbit a u r‖ ≤ (Real.exp a)⁻¹ * ‖u‖ := by
  have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos (Real.exp_pos a)) 0).mul_const ‖u‖
  have hb := norm_integral_le_of_norm_le hi (Eventually.of_forall (fun r => causalLaplaceOrbit_norm_le a r u))
  have he : (∫ r in Ioi (0:ℝ), Real.exp (-Real.exp a*r)) = (Real.exp a)⁻¹ := by
    simpa using integral_exp_mul_Ioi (neg_neg_of_pos (Real.exp_pos a)) 0
  rw [integral_mul_const,he] at hb
  exact hb

private def laplaceIntegralLinear (a : ℝ) : hardyL2ᗮ →ₗ[ℂ] hardyL2ᗮ where
  toFun u := ∫ r in Ioi (0:ℝ), causalLaplaceOrbit a u r
  map_add' u v := by
    have he : causalLaplaceOrbit a (u+v) = fun r => causalLaplaceOrbit a u r+causalLaplaceOrbit a v r := by
      funext r
      simp only [causalLaplaceOrbit,causalForwardOrbit,map_add,smul_add]
    rw [he]
    exact integral_add (causalLaplaceOrbit_integrable a u) (causalLaplaceOrbit_integrable a v)
  map_smul' c u := by
    have he : causalLaplaceOrbit a (c • u) = fun r => c • causalLaplaceOrbit a u r := by
      funext r
      change Real.exp (-Real.exp a*r) • causalLowerCauchyEvolution r.toNNReal (c • u) =
        c • (Real.exp (-Real.exp a*r) • causalLowerCauchyEvolution r.toNNReal u)
      rw [map_smul,smul_comm]
    rw [he]
    exact integral_smul c _

/-- The actual whole-ray vector Laplace integral as a bounded linear operator. -/
def causalLaplaceIntegral (a : ℝ) : hardyL2ᗮ →L[ℂ] hardyL2ᗮ :=
  (laplaceIntegralLinear a).mkContinuous (Real.exp a)⁻¹ (laplace_integral_bound a)

/-- The bounded operator retains the literal whole-ray Bochner integral. -/
theorem causalLaplaceIntegral_apply (a : ℝ) (u : hardyL2ᗮ) :
    causalLaplaceIntegral a u = ∫ r in Ioi (0:ℝ), causalLaplaceOrbit a u r := rfl

/-- The actual vector Laplace operator obeys the reciprocal positive-damping bound. -/
theorem causalLaplaceIntegral_norm_le (a : ℝ) (u : hardyL2ᗮ) :
    ‖causalLaplaceIntegral a u‖ ≤ (Real.exp a)⁻¹ * ‖u‖ := laplace_integral_bound a u

/-- The actual whole-ray Laplace integral commutes with every completed causal evolution. -/
theorem causalLaplaceIntegral_commutes (a : ℝ) (t : ℝ≥0) (u : hardyL2ᗮ) :
    causalLaplaceIntegral a (causalLowerCauchyEvolution t u) =
      causalLowerCauchyEvolution t (causalLaplaceIntegral a u) := by
  rw [causalLaplaceIntegral_apply,causalLaplaceIntegral_apply]
  have hc := ((causalLowerCauchyEvolution t).restrictScalars ℝ).integral_comp_comm (causalLaplaceOrbit_integrable a u)
  change (∫ r in Ioi (0:ℝ), causalLowerCauchyEvolution t (causalLaplaceOrbit a u r)) =
    causalLowerCauchyEvolution t (∫ r in Ioi (0:ℝ), causalLaplaceOrbit a u r) at hc
  rw [← hc]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro r
  change Real.exp (-Real.exp a*r) • causalLowerCauchyEvolution r.toNNReal (causalLowerCauchyEvolution t u) =
    causalLowerCauchyEvolution t (Real.exp (-Real.exp a*r) • causalLowerCauchyEvolution r.toNNReal u)
  rw [ContinuousLinearMap.map_smul_of_tower,← causalLowerCauchyEvolution_add,add_comm,causalLowerCauchyEvolution_add]

end
end RHTower.FokasLenells
