import GaloisForLFunctions.RHTower.FokasLenellsCausalCauchySemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strong vector-orbit integrals for causal Cauchy evolution

These are Bochner integrals of continuous vector orbits, not integrals of
the operator family in operator norm. Finite orbit integration is an actual
bounded linear operator; its primitive satisfies the fundamental theorem of
calculus, and normalized short averages recover every input in norm.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

private theorem continuous_clipped_orbit (u : hardyL2ᗮ) :
    Continuous (fun s : ℝ => causalLowerCauchyEvolution s.toNNReal u) :=
  (causalLowerCauchyEvolution_continuous u).comp continuous_real_toNNReal

/-- The actual vector primitive, extended to real endpoints by constant evolution before zero. -/
def causalOrbitPrimitive (r : ℝ) (u : hardyL2ᗮ) : hardyL2ᗮ :=
  ∫ s in (0:ℝ)..r, causalLowerCauchyEvolution s.toNNReal u

private def causalOrbitIntegralLinear (t : ℝ≥0) : hardyL2ᗮ →ₗ[ℂ] hardyL2ᗮ where
  toFun := causalOrbitPrimitive t
  map_add' u v := by
    unfold causalOrbitPrimitive
    simp only [map_add]
    exact intervalIntegral.integral_add ((continuous_clipped_orbit u).intervalIntegrable _ _)
      ((continuous_clipped_orbit v).intervalIntegrable _ _)
  map_smul' c u := by
    unfold causalOrbitPrimitive
    simp only [map_smul]
    exact intervalIntegral.integral_smul c _

private theorem primitive_bound (t : ℝ≥0) (u : hardyL2ᗮ) : ‖causalOrbitPrimitive t u‖ ≤ (t:ℝ)*‖u‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (t:ℝ)) (fun s _ => causalLowerCauchyEvolution_norm_le s.toNNReal u)
  have ht : |(t:ℝ)| = (t:ℝ) := abs_of_nonneg t.property
  simpa only [causalOrbitPrimitive,sub_zero,ht,mul_comm] using h

/-- Finite integration of actual causal vector orbits as a bounded complex-linear map. -/
def causalOrbitIntegral (t : ℝ≥0) : hardyL2ᗮ →L[ℂ] hardyL2ᗮ :=
  (causalOrbitIntegralLinear t).mkContinuous (t:ℝ) (primitive_bound t)

/-- The bounded integration operator retains the literal vector integral. -/
theorem causalOrbitIntegral_apply (t : ℝ≥0) (u : hardyL2ᗮ) :
    causalOrbitIntegral t u = ∫ s in (0:ℝ)..(t:ℝ), causalLowerCauchyEvolution s.toNNReal u := rfl

/-- Finite orbit integration has its direct time-length norm bound. -/
theorem causalOrbitIntegral_norm_le (t : ℝ≥0) (u : hardyL2ᗮ) : ‖causalOrbitIntegral t u‖ ≤ (t:ℝ)*‖u‖ :=
  primitive_bound t u

/-- The real-endpoint vector primitive differentiates to the actual continuous orbit everywhere. -/
theorem causalOrbitPrimitive_hasDerivAt (r : ℝ) (u : hardyL2ᗮ) :
    HasDerivAt (fun x => causalOrbitPrimitive x u) (causalLowerCauchyEvolution r.toNNReal u) r := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_clipped_orbit u).intervalIntegrable 0 r)
    ((continuous_clipped_orbit u).stronglyMeasurableAtFilter volume (𝓝 r))
    (continuous_clipped_orbit u).continuousAt

/-- The primitive starts at zero for every actual lower Hardy datum. -/
theorem causalOrbitPrimitive_zero (u : hardyL2ᗮ) : causalOrbitPrimitive 0 u = 0 := by
  simp only [causalOrbitPrimitive,intervalIntegral.integral_same]

/-- Its initial derivative is exactly the original datum. -/
theorem causalOrbitPrimitive_hasDerivAt_zero (u : hardyL2ᗮ) :
    HasDerivAt (fun x => causalOrbitPrimitive x u) u 0 := by
  simpa only [Real.toNNReal_zero,causalLowerCauchyEvolution_zero] using causalOrbitPrimitive_hasDerivAt 0 u

/-- Normalized short causal orbit averages recover every input in the actual Hilbert norm. -/
theorem causalOrbitPrimitive_average_tendsto (u : hardyL2ᗮ) :
    Tendsto (fun r : ℝ => r⁻¹ • causalOrbitPrimitive r u) (𝓝[>] 0) (𝓝 u) := by
  simpa only [zero_add,causalOrbitPrimitive_zero,sub_zero] using
    (causalOrbitPrimitive_hasDerivAt_zero u).tendsto_slope_zero_right

/-- Finite vector-orbit integration commutes with each actual causal evolution operator. -/
theorem causalOrbitIntegral_commutes (s t : ℝ≥0) (u : hardyL2ᗮ) :
    causalOrbitIntegral s (causalLowerCauchyEvolution t u) =
      causalLowerCauchyEvolution t (causalOrbitIntegral s u) := by
  rw [causalOrbitIntegral_apply,causalOrbitIntegral_apply,
    ← (causalLowerCauchyEvolution t).intervalIntegral_comp_comm
      ((continuous_clipped_orbit u).intervalIntegrable 0 (s:ℝ))]
  apply intervalIntegral.integral_congr
  intro r hr
  change causalLowerCauchyEvolution r.toNNReal (causalLowerCauchyEvolution t u) =
    causalLowerCauchyEvolution t (causalLowerCauchyEvolution r.toNNReal u)
  rw [← causalLowerCauchyEvolution_add,← causalLowerCauchyEvolution_add,add_comm]

end
end RHTower.FokasLenells
