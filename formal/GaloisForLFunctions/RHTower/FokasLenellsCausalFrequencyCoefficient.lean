import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyProjection
import Mathlib.Analysis.Normed.Module.Span
import Mathlib.Analysis.Normed.Operator.NormedSpace
/-! Canonical scalar coefficients of the actual closed frequency space.
The coordinate comes from the isometry of the genuine unit-frequency line with ℂ.
It reconstructs the actual rank-one projection and has sharp operator norm one. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalFrequencyCoefficientLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalFrequencyCoefficientChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalFrequencyCoefficientChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalFrequencyCoefficientChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace

private def lineCoefficient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (hv : ‖v‖ = 1) (P : E →L[ℂ] E)
    (hP : ∀ u, P u ∈ Submodule.span ℂ {v}) : E →L[ℂ] ℂ :=
  (LinearIsometryEquiv.toSpanUnitSingleton (𝕜 := ℂ) v hv).symm.toLinearIsometry.toContinuousLinearMap.comp
    (P.codRestrict (Submodule.span ℂ {v}) hP)

private theorem lineCoefficient_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (hv : ‖v‖ = 1) (P : E →L[ℂ] E)
    (hP : ∀ u, P u ∈ Submodule.span ℂ {v}) (u : E) :
    lineCoefficient v hv P hP u • v = P u := by
  have h := (LinearIsometryEquiv.toSpanUnitSingleton (𝕜 := ℂ) v hv).apply_symm_apply ⟨P u, hP u⟩
  exact congrArg Subtype.val h

private theorem lineCoefficient_norm_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (hv : ‖v‖ = 1) (P : E →L[ℂ] E)
    (hP : ∀ u, P u ∈ Submodule.span ℂ {v}) (u : E) :
    ‖lineCoefficient v hv P hP u‖ = ‖P u‖ := by
  have h := congrArg norm (lineCoefficient_smul v hv P hP u)
  simpa only [norm_smul, hv, mul_one] using h

private theorem lineCoefficient_eq_of_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (hv : ‖v‖ = 1) (P : E →L[ℂ] E)
    (hP : ∀ u, P u ∈ Submodule.span ℂ {v}) (u : E) (a : ℂ) (hu : P u = a • v) :
    lineCoefficient v hv P hP u = a := by
  have hn : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  exact smul_left_injective ℂ hn ((lineCoefficient_smul v hv P hP u).trans hu)

private theorem lineCoefficient_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (hv : ‖v‖ = 1) (P : E →L[ℂ] E)
    (hP : ∀ u, P u ∈ Submodule.span ℂ {v}) (hfix : P v = v) (hnorm : ‖P‖ = 1) :
    ‖lineCoefficient v hv P hP‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    exact (lineCoefficient_norm_apply v hv P hP u).le.trans
      (P.le_of_opNorm_le hnorm.le u)
  · have hc : lineCoefficient v hv P hP v = 1 :=
      lineCoefficient_eq_of_image v hv P hP v 1 (hfix.trans (one_smul ℂ v).symm)
    have h := (lineCoefficient v hv P hP).le_opNorm v
    simpa only [hc, norm_one, hv, mul_one] using h

private theorem coefficient_projection_law
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : ℝ → E) (P : ℝ → E →L[ℂ] E) (c : ℝ → E →L[ℂ] ℂ)
    (hrec : ∀ η u, c η u • v η = P η u)
    (hmode : ∀ ω η, c ω (v η) = if ω = η then 1 else 0) (ω η : ℝ) (u : E) :
    c ω (P η u) = if ω = η then c ω u else 0 := by
  have h : c ω (P η u) = c η u • c ω (v η) :=
    (congrArg (c ω) (hrec η u).symm).trans (map_smul (c ω) (c η u) (v η))
  by_cases he : ω = η
  · subst η
    simpa only [hmode, if_pos rfl, ite_true, smul_eq_mul, mul_one] using h
  · simpa only [hmode, if_neg he, smul_zero] using h

private theorem mode_norm (b ω : ℝ) : ‖causalFrequencyMode b ω‖ = 1 :=
  norm_causalBoundedUnitEigenchain b ω

private theorem projection_mem_line (b ω : ℝ) (u : causalFrequencySpace b) :
    causalFrequencyProjection b ω u ∈ Submodule.span ℂ {causalFrequencyMode b ω} :=
  (congrArg (fun S : Submodule ℂ (causalFrequencySpace b) =>
    causalFrequencyProjection b ω u ∈ S) (causalFrequencyProjection_range b ω)).mp
      (show causalFrequencyProjection b ω u ∈
        LinearMap.range (causalFrequencyProjection b ω).toLinearMap from ⟨u, rfl⟩)

/-- The canonical scalar amplitude of one genuine frequency component. -/
def causalFrequencyCoefficient (b ω : ℝ) : causalFrequencySpace b →L[ℂ] ℂ :=
  lineCoefficient (causalFrequencyMode b ω) (mode_norm b ω)
    (causalFrequencyProjection b ω) (projection_mem_line b ω)

/-- The coefficient times the actual unit mode is exactly the completed frequency projection. -/
theorem causalFrequencyCoefficient_smul_mode (b ω : ℝ) (u : causalFrequencySpace b) :
    causalFrequencyCoefficient b ω u • causalFrequencyMode b ω = causalFrequencyProjection b ω u :=
  lineCoefficient_smul (causalFrequencyMode b ω) (mode_norm b ω)
    (causalFrequencyProjection b ω) (projection_mem_line b ω) u

/-- Actual modes have Kronecker scalar coefficients: one at their own label and zero elsewhere. -/
theorem causalFrequencyCoefficient_mode (b ω η : ℝ) :
    causalFrequencyCoefficient b ω (causalFrequencyMode b η) = if ω = η then 1 else 0 := by
  apply lineCoefficient_eq_of_image (causalFrequencyMode b ω) (mode_norm b ω)
    (causalFrequencyProjection b ω) (projection_mem_line b ω)
  by_cases h : ω = η
  · subst η
    simpa only [if_pos rfl, ite_true, one_smul] using causalFrequencyProjection_mode b ω ω
  · simpa only [if_neg h, zero_smul] using causalFrequencyProjection_mode b ω η

/-- The scalar amplitude has exactly the norm of its genuine extracted component. -/
theorem norm_causalFrequencyCoefficient_apply (b ω : ℝ) (u : causalFrequencySpace b) :
    ‖causalFrequencyCoefficient b ω u‖ = ‖causalFrequencyProjection b ω u‖ :=
  lineCoefficient_norm_apply (causalFrequencyMode b ω) (mode_norm b ω)
    (causalFrequencyProjection b ω) (projection_mem_line b ω) u

/-- Scalar extraction has sharp norm one on the actual closed frequency space. -/
theorem norm_causalFrequencyCoefficient (b ω : ℝ) : ‖causalFrequencyCoefficient b ω‖ = 1 := by
  apply lineCoefficient_norm (causalFrequencyMode b ω) (mode_norm b ω)
    (causalFrequencyProjection b ω) (projection_mem_line b ω)
  · simpa only [if_pos rfl, ite_true] using causalFrequencyProjection_mode b ω ω
  · exact norm_causalFrequencyProjection b ω

/-- Projection preserves the matching scalar coefficient and kills every other coefficient. -/
theorem causalFrequencyCoefficient_projection (b ω η : ℝ) (u : causalFrequencySpace b) :
    causalFrequencyCoefficient b ω (causalFrequencyProjection b η u) =
      if ω = η then causalFrequencyCoefficient b ω u else 0 :=
  coefficient_projection_law (causalFrequencyMode b) (causalFrequencyProjection b)
    (causalFrequencyCoefficient b) (causalFrequencyCoefficient_smul_mode b)
    (causalFrequencyCoefficient_mode b) ω η u
end
end RHTower.FokasLenells
