import GaloisForLFunctions.RHTower.FokasLenellsCausalOrbitIntegral

/-!
# Integrated semigroup identities for the actual causal Cauchy operators

Translation of continuous vector integrals gives the exact finite-time
addition law. Its exchange identity places time-averaged data in the actual
integrated generator graph without assuming any raw multiplier domain.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

private theorem clipped_add (s : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    (x+(s:ℝ)).toNNReal = x.toNNReal+s := by
  apply Subtype.ext
  change ((x+(s:ℝ)).toNNReal : ℝ) = ((x.toNNReal+s : ℝ≥0) : ℝ)
  rw [Real.coe_toNNReal (x+(s:ℝ)) (add_nonneg hx s.property),NNReal.coe_add,Real.coe_toNNReal x hx]

/-- Finite-time vector integration obeys the actual semigroup addition identity. -/
theorem causalOrbitIntegral_add (s t : ℝ≥0) (u : hardyL2ᗮ) :
    causalOrbitIntegral (s+t) u = causalOrbitIntegral s u +
      causalLowerCauchyEvolution s (causalOrbitIntegral t u) := by
  have hc : Continuous (fun r : ℝ => causalLowerCauchyEvolution r.toNNReal u) :=
    (causalLowerCauchyEvolution_continuous u).comp continuous_real_toNNReal
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (s:ℝ)) (hc.intervalIntegrable (s:ℝ) ((s:ℝ)+(t:ℝ)))
  rw [causalOrbitIntegral_apply,causalOrbitIntegral_apply,causalOrbitIntegral_apply]
  change (∫ r in (0:ℝ)..((s:ℝ)+(t:ℝ)), causalLowerCauchyEvolution r.toNNReal u) = _
  rw [← hs]
  congr 1
  calc
    (∫ r in (s:ℝ)..((s:ℝ)+(t:ℝ)), causalLowerCauchyEvolution r.toNNReal u) =
        ∫ r in (0:ℝ)..(t:ℝ), causalLowerCauchyEvolution (r+(s:ℝ)).toNNReal u := by
      simpa only [zero_add,add_zero,add_comm] using
        (intervalIntegral.integral_comp_add_right
          (fun r : ℝ => causalLowerCauchyEvolution r.toNNReal u) (a := 0) (b := (t:ℝ)) (s:ℝ)).symm
    _ = ∫ r in (0:ℝ)..(t:ℝ), causalLowerCauchyEvolution s (causalLowerCauchyEvolution r.toNNReal u) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 ≤ r := by
        calc
          0 = min 0 (t:ℝ) := (min_eq_left t.property).symm
          _ ≤ r := hr.1
      change causalLowerCauchyEvolution (r+(s:ℝ)).toNNReal u =
        causalLowerCauchyEvolution s (causalLowerCauchyEvolution r.toNNReal u)
      rw [clipped_add s hr0,add_comm,causalLowerCauchyEvolution_add]
    _ = causalLowerCauchyEvolution s (∫ r in (0:ℝ)..(t:ℝ), causalLowerCauchyEvolution r.toNNReal u) :=
      (causalLowerCauchyEvolution s).intervalIntegral_comp_comm (hc.intervalIntegrable 0 (t:ℝ))

/-- The exchange law identifies the derivative data of every finite-time orbit average. -/
theorem causalOrbitIntegral_exchange (s t : ℝ≥0) (u : hardyL2ᗮ) :
    causalOrbitIntegral s (causalLowerCauchyEvolution t u-u) =
      causalLowerCauchyEvolution s (causalOrbitIntegral t u)-causalOrbitIntegral t u := by
  rw [map_sub,causalOrbitIntegral_commutes]
  have he : causalOrbitIntegral s u + causalLowerCauchyEvolution s (causalOrbitIntegral t u) =
      causalOrbitIntegral t u + causalLowerCauchyEvolution t (causalOrbitIntegral s u) := by
    rw [← causalOrbitIntegral_add,← causalOrbitIntegral_add,add_comm]
  have h := congrArg (fun v : hardyL2ᗮ => v-causalOrbitIntegral s u-causalOrbitIntegral t u) he
  convert h.symm using 1 <;> abel

end
end RHTower.FokasLenells
