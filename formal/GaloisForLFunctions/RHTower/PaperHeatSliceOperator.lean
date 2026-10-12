import GaloisForLFunctions.RHTower.PaperHeatSliceMass
import GaloisForLFunctions.RHTower.RiemannHeatSliceEvolution
import GaloisForLFunctions.HTGeometry.PaperModulationCalkin
import GaloisForLFunctions.HTGeometry.LpContinuousMultiplierNorm

/-!
# The proven ideal trace on the full LA Taylor defect

The operator is literal multiplication on the real-height continuum. The paper's
closed-ideal trace has an exact zero/infinity transition at the native Newman threshold.
No arithmetic source sign is assumed or produced by this representation.
-/

namespace RHTower.PaperHeatSlice
noncomputable section
open MeasureTheory Filter
open RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open scoped Topology ENNReal NNReal

abbrev HeightSpace := Lp ℂ 2 (volume : Measure ℝ)

theorem coeff_eq_nativeTaylor (lam : ℝ≥0) (t : ℝ) (n : ℕ) :
    coeff lam t n = (n.factorial : ℂ)⁻¹ * heatSliceTaylor lam t n := by
  exact (div_eq_mul_inv (iteratedDeriv n (source lam t) 0) (n.factorial : ℂ)).trans (mul_comm _ _)

/-- The multiplier symbol retains every coefficient of the corpus's native evolving jets. -/
theorem mass_eq_nativeTaylor_mass (lam : ℝ≥0) (r : Radius) (t : ℝ) :
    mass lam r t = ∑' n : ℕ,
      max 0 (-((n.factorial : ℂ)⁻¹ * heatSliceTaylor lam t n).re) * (r : ℝ) ^ n := by
  simp only [mass, massTerm, coeff_eq_nativeTaylor]

theorem norm_complex_mass_le (lam : ℝ≥0) (r : Radius) (t : ℝ) :
    ‖(mass lam r t : ℂ)‖ ≤ massBudget lam r := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mass_nonneg lam r t)]
  exact mass_le_budget lam r t

def massOperator (lam : ℝ≥0) (r : Radius) : HeightSpace →L[ℂ] HeightSpace :=
  lpBoundedMulCLM (Complex.continuous_ofReal.comp (continuous_mass lam r)).measurable
    (massBudget_nonneg lam r) (norm_complex_mass_le lam r)

theorem massOperator_apply_ae (lam : ℝ≥0) (r : Radius) (f : HeightSpace) :
    (massOperator lam r f : ℝ → ℂ) =ᵐ[volume] fun t => (mass lam r t : ℂ) * f t :=
  lpBoundedMulCLM_coeFn _ _ _ f

def massCommutant (lam : ℝ≥0) (r : Radius) : paperModulationCommutant :=
  ⟨massOperator lam r, mem_paperModulationCommutant_of_mul _ _ (massOperator_apply_ae lam r)⟩

theorem mass_le_operator_norm (lam : ℝ≥0) (r : Radius) (t : ℝ) :
    mass lam r t ≤ ‖massOperator lam r‖ := by
  have h := norm_symbol_le_of_ae_mul_continuous
    (Complex.continuous_ofReal.comp (continuous_mass lam r)) (massOperator_apply_ae lam r) t
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mass_nonneg lam r t)] using h

theorem massOperator_eq_zero_iff (lam : ℝ≥0) (r : Radius) :
    massOperator lam r = 0 ↔ mass lam r = 0 := by
  constructor
  · intro h
    funext t
    apply le_antisymm _ (mass_nonneg lam r t)
    simpa only [h, norm_zero] using mass_le_operator_norm lam r t
  · intro h
    apply ContinuousLinearMap.ext
    intro f
    change massOperator lam r f = (0 : HeightSpace)
    apply Lp.ext
    filter_upwards [massOperator_apply_ae lam r f, Lp.coeFn_zero ℂ 2 volume] with t ht hz
    have hmass : mass lam r t = 0 := congrFun h t
    simpa only [hmass, Complex.ofReal_zero, zero_mul, hz, Pi.zero_apply] using ht

theorem massOperator_eq_zero_iff_threshold (lam : ℝ≥0) (r : Radius) :
    massOperator lam r = 0 ↔ newmanConstant ≤ lam := by
  rw [massOperator_eq_zero_iff, mass_eq_zero_iff_threshold]

/-- Compact quotient retains the entire all-order source defect norm. -/
theorem massOperator_compactIdealDistance (lam : ℝ≥0) (r : Radius) :
    compactIdealDistance (massOperator lam r) = ‖massOperator lam r‖ :=
  paperModulationCommutant_compactIdealDistance (massCommutant lam r)

theorem massOperator_compact_iff_zero (lam : ℝ≥0) (r : Radius) :
    IsCompactOperator (massOperator lam r) ↔ massOperator lam r = 0 := by
  constructor
  · intro h
    exact congrArg Subtype.val ((paperModulationCommutant_compact_iff_zero (massCommutant lam r)).mp h)
  · intro h
    rw [h]
    exact isCompactOperator_zero

theorem massOperator_compact_iff_threshold (lam : ℝ≥0) (r : Radius) :
    IsCompactOperator (massOperator lam r) ↔ newmanConstant ≤ lam := by
  rw [massOperator_compact_iff_zero, massOperator_eq_zero_iff_threshold]

/-- Exact application of the paper's proven ideal transport to the native LA source. -/
theorem massOperator_traceCost (lam : ℝ≥0) (r : Radius) :
    compactOperatorTraceCost HeightSpace (massOperator lam r) =
      if newmanConstant ≤ lam then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, massOperator_compact_iff_threshold]

theorem massOperator_traceCost_zero_iff (lam : ℝ≥0) (r : Radius) :
    compactOperatorTraceCost HeightSpace (massOperator lam r) = 0 ↔ newmanConstant ≤ lam := by
  rw [compactOperatorTraceCost_eq_zero_iff, massOperator_compact_iff_threshold]

theorem massOperator_traceCost_top_iff (lam : ℝ≥0) (r : Radius) :
    compactOperatorTraceCost HeightSpace (massOperator lam r) = ∞ ↔ (lam : ℝ) < newmanConstant := by
  rw [compactOperatorTraceCost_eq_top_iff, massOperator_compact_iff_threshold, not_le]

theorem massOperator_traceCost_add_compact (lam : ℝ≥0) (r : Radius)
    (K : compactOperatorStarAlgebra HeightSpace) :
    compactOperatorTraceCost HeightSpace (massOperator lam r + K.1) =
      if newmanConstant ≤ lam then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, massOperator_traceCost]

theorem mass_le_norm_sub_compact (lam : ℝ≥0) (r : Radius) (t : ℝ)
    (K : compactOperatorStarAlgebra HeightSpace) :
    mass lam r t ≤ ‖massOperator lam r - K.1‖ :=
  (mass_le_operator_norm lam r t).trans
    (paperModulationCommutant_norm_le_sub_compact (massCommutant lam r) K)

theorem massOperator_zero_traceCost_iff_rh (r : Radius) :
    compactOperatorTraceCost HeightSpace (massOperator 0 r) = 0 ↔ RiemannHypothesis := by
  rw [compactOperatorTraceCost_eq_zero_iff, massOperator_compact_iff_zero,
    massOperator_eq_zero_iff, mass_zero_eq_zero_iff_rh]

end
end RHTower.PaperHeatSlice
