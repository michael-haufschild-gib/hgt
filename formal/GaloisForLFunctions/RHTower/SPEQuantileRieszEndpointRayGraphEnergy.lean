import GaloisForLFunctions.RHTower.SPEQuantileRieszEndpointRayLaplacePort

/-!
# Uniform Route-P graph energy on the literal SP-E endpoint port

Route P's radial position-generator graph norm diverges as the positive rate tends to zero.  The
literal SP-E endpoint-ray port never uses that chamber: its source scale is exactly in `[1/2, 1]`.
This module records the exact graph energy and its uniform bound `2` on that source interval.

This removes the zero-rate graph-norm obstruction for the endpoint analytic port only.  It does
not construct the still-missing source-faithful signed free-word lift, nor does it bound the
RH-equivalent completed SP-E current.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-- The literal SP-E endpoint ray has exactly Route P's cubic generator graph energy. -/
theorem routePBurnolApertureEnergy_primeGammaCauchyCubicComplexRayFeature_eq
    {s : ℝ} (hs : 0 < s) :
    routePBurnolApertureEnergy (primeGammaCauchyCubicComplexRayFeature s) =
      1 / (4 * s ^ (3 : ℕ)) := by
  unfold routePBurnolApertureEnergy
  simp_rw [primeGammaCauchyCubicComplexRayFeature_eq_xiWardResolvedRadialGeneratorMode]
  exact integral_norm_xiWardResolvedRadialGeneratorMode_sq hs

/-- The literal endpoint-scale interval `[1/2, 1]` stays uniformly away from P's zero-rate graph
singularity.  The sharp endpoint value is `2`. -/
theorem routePBurnolApertureEnergy_primeGammaCauchyCubicComplexRayFeature_le_two
    {s : ℝ} (hs : 1 / 2 ≤ s) :
    routePBurnolApertureEnergy (primeGammaCauchyCubicComplexRayFeature s) ≤ 2 := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  rw [routePBurnolApertureEnergy_primeGammaCauchyCubicComplexRayFeature_eq hspos]
  have hcube : (1 / 2 : ℝ) ^ (3 : ℕ) ≤ s ^ (3 : ℕ) := by gcongr
  have hden : 0 < 4 * s ^ (3 : ℕ) := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

end GaloisForLFunctions.HTGeometry
