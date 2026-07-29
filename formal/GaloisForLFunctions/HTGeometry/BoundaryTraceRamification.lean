import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Boundary trace ramification

This file isolates the universal local law behind thermal trace quotients with
denominator `1 - exp (-u)`.  A nonzero boundary density has exact square-root
scale.  Consequently it cannot be produced by a norm-differentiable curve
which vanishes at the boundary.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace HTGeometry

variable {E : Type*} [NormedAddCommGroup E]

/-- Thermal first-order boundary density of a normed-space curve. -/
def thermalBoundaryTraceDensity (F : ℝ → E) (u : ℝ) : ℝ :=
  ‖F u‖ ^ 2 / (1 - Real.exp (-u))

/-- Square-root-normalized amplitude associated to the thermal density. -/
def thermalBoundaryRamificationAmplitude (F : ℝ → E) (u : ℝ) : ℝ :=
  ‖F u‖ / Real.sqrt (1 - Real.exp (-u))

/-- Exact square-root ramification law: convergence of the thermal density
forces convergence of its normalized amplitude to the square root of the
density. -/
theorem tendsto_thermalBoundaryRamificationAmplitude
    {F : ℝ → E} {ell : ℝ}
    (hdensity : Tendsto (thermalBoundaryTraceDensity F) (𝓝[>] 0) (nhds ell)) :
    Tendsto (thermalBoundaryRamificationAmplitude F) (𝓝[>] 0)
      (nhds (Real.sqrt ell)) := by
  change Tendsto (fun u => ‖F u‖ / Real.sqrt (1 - Real.exp (-u))) (𝓝[>] 0)
    (nhds (Real.sqrt ell))
  simpa only [thermalBoundaryTraceDensity,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] using hdensity.sqrt

section Differentiable

variable [NormedSpace ℝ E]

/-- A norm-differentiable curve vanishing at the boundary has squared norm
which is little-oh of the thermal first-order scale. -/
theorem tendsto_norm_sq_div_id_nhdsGT_zero_of_hasDerivAt
    {F : ℝ → E} {v : E} (hF : HasDerivAt F v 0) (hF0 : F 0 = 0) :
    Tendsto (fun u : ℝ => ‖F u‖ ^ 2 / u) (𝓝[>] 0) (nhds 0) := by
  have hslope :
      Tendsto (fun u : ℝ => u⁻¹ • F u) (𝓝[>] 0) (nhds v) := by
    simpa only [zero_add, hF0, sub_zero] using hF.tendsto_slope_zero_right
  have hnormSlope :
      Tendsto (fun u : ℝ => ‖u⁻¹ • F u‖) (𝓝[>] 0) (nhds ‖v‖) :=
    hslope.norm
  have hnormF : Tendsto (fun u : ℝ => ‖F u‖) (𝓝[>] 0) (nhds 0) := by
    have hcont : Tendsto F (𝓝[>] 0) (nhds (F 0)) :=
      hF.continuousAt.continuousWithinAt
    simpa only [hF0, norm_zero] using hcont.norm
  have hprod := hnormSlope.mul hnormF
  have heq :
      (fun u : ℝ => ‖u⁻¹ • F u‖ * ‖F u‖) =ᶠ[𝓝[>] 0]
        (fun u : ℝ => ‖F u‖ ^ 2 / u) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hu]
    field_simp
  simpa only [mul_zero] using Filter.Tendsto.congr' heq hprod

/-- The thermal denominator has first-order slope one at the boundary. -/
theorem tendsto_one_sub_exp_neg_slope_nhdsGT_zero :
    Tendsto (fun u : ℝ => u⁻¹ * (1 - Real.exp (-u))) (𝓝[>] 0) (nhds 1) := by
  have hderiv : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) 1 0 := by
    have hneg : HasDerivAt (fun u : ℝ => -u) (-1) 0 :=
      (hasDerivAt_id (𝕜 := ℝ) 0).neg
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-1) 0 := by
      convert hneg.exp using 1
      all_goals norm_num
    simpa only [Pi.sub_apply, sub_neg_eq_add, zero_add] using!
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hexp
  simpa only [zero_add, neg_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul] using
    hderiv.tendsto_slope_zero_right

/-- Reciprocal form of the exact first-order thermal slope. -/
theorem tendsto_id_div_one_sub_exp_neg_nhdsGT_zero :
    Tendsto (fun u : ℝ => u / (1 - Real.exp (-u))) (𝓝[>] 0) (nhds 1) := by
  have hinv := tendsto_one_sub_exp_neg_slope_nhdsGT_zero.inv₀ one_ne_zero
  have heq :
      (fun u : ℝ => (u⁻¹ * (1 - Real.exp (-u)))⁻¹) =ᶠ[𝓝[>] 0]
        (fun u : ℝ => u / (1 - Real.exp (-u))) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hden : 1 - Real.exp (-u) ≠ 0 := by
      have hexp : Real.exp (-u) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (neg_neg_of_pos hu)
      linarith
    field_simp
  simpa only [inv_one] using Filter.Tendsto.congr' heq hinv

/-- Differentiable boundary curves have zero thermal trace density. -/
theorem tendsto_thermalBoundaryTraceDensity_zero_of_hasDerivAt
    {F : ℝ → E} {v : E} (hF : HasDerivAt F v 0) (hF0 : F 0 = 0) :
    Tendsto (thermalBoundaryTraceDensity F) (𝓝[>] 0) (nhds 0) := by
  have hprod :=
    (tendsto_norm_sq_div_id_nhdsGT_zero_of_hasDerivAt hF hF0).mul
      tendsto_id_div_one_sub_exp_neg_nhdsGT_zero
  have heq :
      (fun u : ℝ => (‖F u‖ ^ 2 / u) * (u / (1 - Real.exp (-u)))) =ᶠ[𝓝[>] 0]
        thermalBoundaryTraceDensity F := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hden : 1 - Real.exp (-u) ≠ 0 := by
      have hexp : Real.exp (-u) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (neg_neg_of_pos hu)
      linarith
    rw [thermalBoundaryTraceDensity]
    field_simp
  simpa only [zero_mul] using Filter.Tendsto.congr' heq hprod

/-- Positive thermal boundary density is incompatible with norm
differentiability at a vanishing boundary point. -/
theorem not_hasDerivAt_of_thermalBoundaryTraceDensity_tendsto_pos
    {F : ℝ → E} (hF0 : F 0 = 0) {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (thermalBoundaryTraceDensity F) (𝓝[>] 0) (nhds ell)) :
    ¬ ∃ v : E, HasDerivAt F v 0 := by
  rintro ⟨v, hF⟩
  have hzero := tendsto_thermalBoundaryTraceDensity_zero_of_hasDerivAt hF hF0
  have : ell = 0 := tendsto_nhds_unique hdensity hzero
  linarith

end Differentiable

end HTGeometry
