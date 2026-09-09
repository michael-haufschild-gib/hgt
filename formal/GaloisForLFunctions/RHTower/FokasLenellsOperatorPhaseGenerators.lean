import GaloisForLFunctions.RHTower.FokasLenellsOperatorPhaseUnitary

/-!
# Conserved exact norms of all actual jump generators

Each existing scalar generator has a parameter-independent pointwise norm.
Passing through its genuine L-infinity class and the exact off-diagonal
matrix norm conserves the full time, space, mixed and second-time budgets.
-/

open MeasureTheory
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem linfty_norm_eq_of_ae_norm (g h : Lp ℂ ∞ (volume : Measure ℝ))
    (he : ∀ᵐ z ∂volume, ‖g z‖ = ‖h z‖) : ‖g‖ = ‖h‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_norm_ae he]

private theorem directSymbol_norm_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSymbol q t x reverse z‖ = ‖directSymbol q 0 0 reverse z‖ := by
  cases reverse
  · change ‖regularJumpReflection (globalSmallScatteringPotential q) t x z‖ =
      ‖regularJumpReflection (globalSmallScatteringPotential q) 0 0 z‖
    rw [(regularJumpReflection_norms _ t x z).1, (regularJumpReflection_norms _ 0 0 z).1]
  · change ‖regularJumpReverseReflection (globalSmallScatteringPotential q) t x z‖ =
      ‖regularJumpReverseReflection (globalSmallScatteringPotential q) 0 0 z‖
    rw [(regularJumpReflection_norms _ t x z).2, (regularJumpReflection_norms _ 0 0 z).2]

/-- The actual direct symbol's essential-supremum norm is conserved by time and space evolution. -/
theorem norm_directLinftySymbol_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directLinftySymbol q t x reverse‖ = ‖directLinftySymbol q 0 0 reverse‖ := by
  apply linfty_norm_eq_of_ae_norm
  filter_upwards [directLinftySymbol_ae q t x reverse, directLinftySymbol_ae q 0 0 reverse] with z h0 h1
  rw [h0, h1]
  exact directSymbol_norm_invariant q t x reverse z

/-- The actual direct multiplication operator has its exact initial norm at every time and position. -/
theorem norm_directMultiplier_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directMultiplier q t x reverse‖ = ‖directMultiplier q 0 0 reverse‖ := by
  rw [norm_directMultiplier_eq_linfty, norm_directMultiplier_eq_linfty, norm_directLinftySymbol_time_space_invariant]

/-- The actual directTime symbol's essential-supremum norm is conserved by time and space evolution. -/
theorem norm_directTimeLinftySymbol_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directTimeLinftySymbol q t x reverse‖ = ‖directTimeLinftySymbol q 0 0 reverse‖ := by
  apply linfty_norm_eq_of_ae_norm
  filter_upwards [directTimeLinftySymbol_ae q t x reverse, directTimeLinftySymbol_ae q 0 0 reverse] with z h0 h1
  rw [h0, h1]
  rw [directTimeSymbol_norm, directTimeSymbol_norm]

/-- The actual directTime multiplication operator has its exact initial norm at every time and position. -/
theorem norm_directTimeMultiplier_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directTimeMultiplier q t x reverse‖ = ‖directTimeMultiplier q 0 0 reverse‖ := by
  rw [norm_directTimeMultiplier_eq_linfty, norm_directTimeMultiplier_eq_linfty, norm_directTimeLinftySymbol_time_space_invariant]

/-- The actual directSpace symbol's essential-supremum norm is conserved by time and space evolution. -/
theorem norm_directSpaceLinftySymbol_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directSpaceLinftySymbol q t x reverse‖ = ‖directSpaceLinftySymbol q 0 0 reverse‖ := by
  apply linfty_norm_eq_of_ae_norm
  filter_upwards [directSpaceLinftySymbol_ae q t x reverse, directSpaceLinftySymbol_ae q 0 0 reverse] with z h0 h1
  rw [h0, h1]
  rw [directSpaceSymbol_norm, directSpaceSymbol_norm]

/-- The actual directSpace multiplication operator has its exact initial norm at every time and position. -/
theorem norm_directSpaceMultiplier_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directSpaceMultiplier q t x reverse‖ = ‖directSpaceMultiplier q 0 0 reverse‖ := by
  rw [norm_directSpaceMultiplier_eq_linfty, norm_directSpaceMultiplier_eq_linfty, norm_directSpaceLinftySymbol_time_space_invariant]

/-- The actual compatibleSecondTime symbol's essential-supremum norm is conserved by time and space evolution. -/
theorem norm_compatibleSecondTimeLinftySymbol_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖compatibleSecondTimeLinftySymbol q t x reverse‖ = ‖compatibleSecondTimeLinftySymbol q 0 0 reverse‖ := by
  apply linfty_norm_eq_of_ae_norm
  filter_upwards [compatibleSecondTimeLinftySymbol_ae q t x reverse, compatibleSecondTimeLinftySymbol_ae q 0 0 reverse] with z h0 h1
  rw [h0, h1]
  rw [directSecondTimeSymbol_norm, directSecondTimeSymbol_norm]

/-- The actual compatibleSecondTime multiplication operator has its exact initial norm at every time and position. -/
theorem norm_compatibleSecondTimeMultiplier_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖compatibleSecondTimeMultiplier q t x reverse‖ = ‖compatibleSecondTimeMultiplier q 0 0 reverse‖ := by
  rw [norm_compatibleSecondTimeMultiplier_eq_linfty, norm_compatibleSecondTimeMultiplier_eq_linfty, norm_compatibleSecondTimeLinftySymbol_time_space_invariant]

/-- The complete directJumpTimeOperator has a conserved exact operator norm. -/
theorem norm_directJumpTimeOperator_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directJumpTimeOperator q t x‖ = ‖directJumpTimeOperator q 0 0‖ := by
  rw [norm_directJumpTimeOperator_eq_linfty, norm_directJumpTimeOperator_eq_linfty,
    norm_directTimeLinftySymbol_time_space_invariant q t x false, norm_directTimeLinftySymbol_time_space_invariant q t x true]

/-- The actual directCauchyTimeOperator retains the initial full jump-generator norm. -/
theorem norm_directCauchyTimeOperator_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchyTimeOperator q t x‖ = ‖directJumpTimeOperator q 0 0‖ := by
  rw [norm_directCauchyTimeOperator_eq_jump, norm_directJumpTimeOperator_time_space_invariant]

/-- The complete directJumpSpaceOperator has a conserved exact operator norm. -/
theorem norm_directJumpSpaceOperator_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directJumpSpaceOperator q t x‖ = ‖directJumpSpaceOperator q 0 0‖ := by
  rw [norm_directJumpSpaceOperator_eq_linfty, norm_directJumpSpaceOperator_eq_linfty,
    norm_directSpaceLinftySymbol_time_space_invariant q t x false, norm_directSpaceLinftySymbol_time_space_invariant q t x true]

/-- The actual directCauchySpaceOperator retains the initial full jump-generator norm. -/
theorem norm_directCauchySpaceOperator_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchySpaceOperator q t x‖ = ‖directJumpSpaceOperator q 0 0‖ := by
  rw [norm_directCauchySpaceOperator_eq_jump, norm_directJumpSpaceOperator_time_space_invariant]

/-- The complete directJumpMixedOperator has a conserved exact operator norm. -/
theorem norm_directJumpMixedOperator_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directJumpMixedOperator q t x‖ = ‖directJumpMixedOperator q 0 0‖ := by
  rw [norm_directJumpMixedOperator_eq_linfty, norm_directJumpMixedOperator_eq_linfty,
    norm_directLinftySymbol_time_space_invariant q t x false, norm_directLinftySymbol_time_space_invariant q t x true]

/-- The actual directCauchyMixedOperator retains the initial full jump-generator norm. -/
theorem norm_directCauchyMixedOperator_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchyMixedOperator q t x‖ = ‖directJumpMixedOperator q 0 0‖ := by
  rw [norm_directCauchyMixedOperator_eq_jump, norm_directJumpMixedOperator_time_space_invariant]

/-- The complete compatibleJumpSecondTimeOperator has a conserved exact operator norm. -/
theorem norm_compatibleJumpSecondTimeOperator_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖compatibleJumpSecondTimeOperator q t x‖ = ‖compatibleJumpSecondTimeOperator q 0 0‖ := by
  rw [norm_compatibleJumpSecondTimeOperator_eq_linfty, norm_compatibleJumpSecondTimeOperator_eq_linfty,
    norm_compatibleSecondTimeLinftySymbol_time_space_invariant q t x false, norm_compatibleSecondTimeLinftySymbol_time_space_invariant q t x true]

/-- The actual compatibleCauchySecondTimeOperator retains the initial full jump-generator norm. -/
theorem norm_compatibleCauchySecondTimeOperator_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖compatibleCauchySecondTimeOperator q t x‖ = ‖compatibleJumpSecondTimeOperator q 0 0‖ := by
  rw [norm_compatibleCauchySecondTimeOperator_eq_jump, norm_compatibleJumpSecondTimeOperator_time_space_invariant]

end
end RHTower.FokasLenells
