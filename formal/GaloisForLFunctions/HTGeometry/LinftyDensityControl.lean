import GaloisForLFunctions.HTGeometry.FiniteDimensionalDensityControl
import GaloisForLFunctions.HTGeometry.LinftyFiniteConstraintAperture
import Mathlib.MeasureTheory.Measure.Support

/-!
# Surjective finite-dimensional control by bounded densities

A continuous integrable kernel on a finite measure space defines a continuous control from real
`L∞` densities by Bochner pairing.  Normalized indicators of shrinking positive-measure
neighborhoods approximate every kernel column on the measure support.  Since linear ranges in a
finite-dimensional target are closed, surjectivity of finitely supported support columns promotes
to exact surjectivity of the genuine `L∞` density control.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α V : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  (μ : Measure α)

/-- Pair a fixed vector-valued `L¹` kernel against a real `L∞` density. -/
noncomputable def linftyLpPairingRight (K : Lp V 1 μ) : Lp ℝ ∞ μ →L[ℝ] V :=
  ((((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)).lpPairing μ ∞ 1).flip) K

/-- The fixed-kernel pairing is its Bochner integral. -/
theorem linftyLpPairingRight_apply (K : Lp V 1 μ) (w : Lp ℝ ∞ μ) :
    linftyLpPairingRight μ K w = ∫ x, (w x) • K x ∂μ := by
  exact ContinuousLinearMap.lpPairing_eq_integral
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V) w K

/-- Continuous control of a finite-dimensional vector packet by real `L∞` densities. -/
noncomputable def linftyBochnerControl (K : α → V) (hK : MemLp K 1 μ) :
    Lp ℝ ∞ μ →L[ℝ] V :=
  linftyLpPairingRight μ (hK.toLp K)

/-- Pointwise integral formula for the bounded-density control. -/
theorem linftyBochnerControl_apply
    (K : α → V) (hK : MemLp K 1 μ) (w : Lp ℝ ∞ μ) :
    linftyBochnerControl μ K hK w = ∫ x, (w x) • K x ∂μ := by
  rw [linftyBochnerControl, linftyLpPairingRight_apply]
  apply integral_congr_ae
  filter_upwards [hK.coeFn_toLp] with x hx
  rw [hx]

/-- An indicator density maps to the set integral of the kernel. -/
theorem linftyBochnerControl_indicator
    [IsFiniteMeasure μ] (K : α → V) (hK : MemLp K 1 μ)
    (s : Set α) (hs : MeasurableSet s) :
    linftyBochnerControl μ K hK (linftyIndicatorAtom μ s hs) = ∫ x in s, K x ∂μ := by
  rw [linftyBochnerControl_apply]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  have hcoe : ⇑(linftyIndicatorAtom μ s hs) =ᵐ[μ]
      s.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
  filter_upwards [hcoe] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Every kernel column over the measure support is approximated by normalized indicator
densities, hence belongs to the closure of the bounded-density control range. -/
theorem continuous_kernel_mem_closure_range_linftyBochnerControl
    [TopologicalSpace α] [BorelSpace α] [IsFiniteMeasure μ]
    (K : α → V) (hK : MemLp K 1 μ) (hcont : Continuous K) :
    ∀ x ∈ μ.support, K x ∈ closure (Set.range (linftyBochnerControl μ K hK)) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  let s : Set α := {y | dist (K y) (K x) < ε / 2}
  have hsopen : IsOpen s := by
    exact isOpen_lt (hcont.dist continuous_const) continuous_const
  have hxs : x ∈ s := by
    simp [s, hε]
  have hsnhds : s ∈ nhds x := hsopen.mem_nhds hxs
  have hμpos : 0 < μ s :=
    (Measure.mem_support_iff_forall (μ := μ) x).mp hx s hsnhds
  have hμrealpos : 0 < μ.real s :=
    ENNReal.toReal_pos hμpos.ne' (measure_ne_top μ s)
  let w : Lp ℝ ∞ μ :=
    (μ.real s)⁻¹ • linftyIndicatorAtom μ s hsopen.measurableSet
  refine ⟨linftyBochnerControl μ K hK w, ⟨w, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have hKint : Integrable K μ := hK.integrable (by norm_num)
  have hconst : IntegrableOn (fun _ : α => K x) s μ :=
    integrableOn_const
  have hdiff :
      (μ.real s)⁻¹ • (∫ y in s, K y ∂μ) - K x =
        (μ.real s)⁻¹ • (∫ y in s, K y - K x ∂μ) := by
    rw [integral_sub hKint.integrableOn hconst, setIntegral_const]
    rw [smul_sub]
    have hcancel : (μ.real s)⁻¹ • (μ.real s • K x) = K x := by
      rw [← mul_smul, inv_mul_cancel₀ hμrealpos.ne', one_smul]
    rw [hcancel]
  rw [map_smul, linftyBochnerControl_indicator, norm_sub_rev, hdiff]
  have hbound : ‖∫ y in s, K y - K x ∂μ‖ ≤ (ε / 2) * μ.real s := by
    apply norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top μ s)
    filter_upwards [] with y hy
    change dist (K y) (K x) < ε / 2 at hy
    simpa [dist_eq_norm] using hy.le
  calc
    ‖(μ.real s)⁻¹ • (∫ y in s, K y - K x ∂μ)‖ =
        |(μ.real s)⁻¹| * ‖∫ y in s, K y - K x ∂μ‖ := norm_smul _ _
    _ ≤ |(μ.real s)⁻¹| * ((ε / 2) * μ.real s) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = ε / 2 := by
      rw [abs_of_pos (inv_pos.mpr hμrealpos)]
      field_simp
    _ < ε := half_lt_self hε

/-- If finitely supported masses on support points control the finite-dimensional target, then
bounded densities control it exactly. -/
theorem linftyBochnerControl_surjective_of_support_finsupp
    [TopologicalSpace α] [BorelSpace α] [IsFiniteMeasure μ]
    [FiniteDimensional ℝ V]
    (K : α → V) (hK : MemLp K 1 μ) (hcont : Continuous K)
    {κ : Type*} (t : κ → α) (ht : ∀ k, t k ∈ μ.support)
    (hfinite : Function.Surjective (Finsupp.linearCombination ℝ (fun k => K (t k)))) :
    Function.Surjective (linftyBochnerControl μ K hK) := by
  apply continuousLinearMap_surjective_of_finsupp_columns_mem_closure_range
    (linftyBochnerControl μ K hK) (fun k => K (t k)) hfinite
  intro k
  exact continuous_kernel_mem_closure_range_linftyBochnerControl
    μ K hK hcont (t k) (ht k)

end
end GaloisForLFunctions.HTGeometry
