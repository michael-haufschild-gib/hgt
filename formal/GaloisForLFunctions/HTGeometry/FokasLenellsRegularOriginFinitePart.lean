import GaloisForLFunctions.HTGeometry.FokasLenellsRegularTransmissionTaylor

/-!
# The actual transmission-corrected finite part

The upper second-inverse-weight reflection has residue M(q), but its
finite part is not just half the unnormalized fifth coefficient.
Division by transmission contributes minus M(q) times the mixed moment.
-/

open Complex Matrix MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The finite origin coefficient of the actual upper weighted reflection after removing its compatibility pole. -/
def regularUpperOriginFinitePart (q : SchwartzMap ℝ ℂ) : ℂ :=
  rawScatteringFifthCoefficient q 1 0 / 2 - compatibilityMoment q * rawMixedTotal q

/-- Subtract a proposed reciprocal residue from the actual normalized upper reflection channel. -/
def renormalizedRegularUpperReflection (q : SchwartzMap ℝ ℂ) (c : ℂ) (z : ℝ) : ℂ :=
  regularSecondInverseReflection q true z - c/(z : ℂ)

theorem renormalizedRegularUpperReflection_measurable (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    Measurable (renormalizedRegularUpperReflection q c) :=
  (regularSecondInverseReflection_measurable q true).sub
    (measurable_const.div Complex.continuous_ofReal.measurable)

/-- The finite part includes the exact contribution of the first nonconstant transmission coefficient. -/
theorem regularSecondInverseReflection_upper_sub_pole_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (renormalizedRegularUpperReflection q (compatibilityMoment q))
      (𝓝[>] 0) (𝓝 (regularUpperOriginFinitePart q)) := by
  have hT : Tendsto (fun z : ℝ => regularScatteringMatrix q z 1 1) (𝓝[>] 0) (𝓝 1) :=
    (regularTransmission_diagonal_tendsto_zero q 1).mono_left nhdsWithin_le_nhds
  have hM : Tendsto (fun _ : ℝ => compatibilityMoment q) (𝓝[>] 0)
      (𝓝 (compatibilityMoment q)) := tendsto_const_nhds
  have hN := ((originWeightedReflection_sub_pole_tendsto q).div_const (2 : ℂ)).sub
    (hM.mul (regularTransmission_upper_right_quotient_tendsto q))
  have hh := hN.div hT one_ne_zero
  change Tendsto (fun z : ℝ =>
    ((originWeightedReflection q z - 2*compatibilityMoment q/(z : ℂ))/2 -
      compatibilityMoment q*((regularScatteringMatrix q z 1 1-1)/(z : ℂ)))/
        regularScatteringMatrix q z 1 1)
    (𝓝[>] 0) (𝓝 ((rawScatteringFifthCoefficient q 1 0/2 -
      compatibilityMoment q*rawMixedTotal q)/1)) at hh
  simp only [div_one] at hh
  apply hh.congr'
  have hne : ∀ᶠ z in 𝓝[>] (0 : ℝ), regularScatteringMatrix q z 1 1 ≠ 0 :=
    ((regularTransmission_diagonal_tendsto_zero q 1).eventually_ne one_ne_zero).filter_mono nhdsWithin_le_nhds
  filter_upwards [regularSecondInverseReflection_upper_eventually_restore q, hne,
    self_mem_nhdsWithin] with z hrestore ht hz
  have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [renormalizedRegularUpperReflection, hrestore]
  field_simp
  ring

/-- A proposed subtraction changes the actual upper reciprocal residue by exactly that amount. -/
theorem renormalizedRegularUpperReflection_mul_coordinate_tendsto (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    Tendsto (fun z : ℝ => (z : ℂ)*renormalizedRegularUpperReflection q c z)
      (𝓝[>] 0) (𝓝 (compatibilityMoment q-c)) := by
  apply ((regularSecondInverseReflection_upper_residue_tendsto q).sub_const c).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  simp only [renormalizedRegularUpperReflection, mul_sub]
  field_simp

/-- The compatibility moment is the unique pole subtraction that leaves a finite actual normalized reflection limit. -/
theorem renormalizedRegularUpperReflection_finite_limit_iff (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    (∃ d : ℂ, Tendsto (renormalizedRegularUpperReflection q c) (𝓝[>] 0) (𝓝 d)) ↔
      c = compatibilityMoment q := by
  constructor
  · rintro ⟨d,hd⟩
    have hz : Tendsto (fun z : ℝ => (z : ℂ)) (𝓝[>] 0) (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hh := hz.mul hd
    simp only [zero_mul] at hh
    have he := tendsto_nhds_unique (renormalizedRegularUpperReflection_mul_coordinate_tendsto q c) hh
    exact (sub_eq_zero.mp he).symm
  · rintro rfl
    exact ⟨regularUpperOriginFinitePart q, regularSecondInverseReflection_upper_sub_pole_tendsto q⟩

/-- Correct subtraction restores every local Lp condition on one interval for arbitrary Schwartz spatial data. -/
theorem renormalizedRegularUpperReflection_locally_memLp_all (q : SchwartzMap ℝ ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (renormalizedRegularUpperReflection q (compatibilityMoment q)) p
        (volume.restrict (Ioo 0 δ)) := by
  have hb := (regularSecondInverseReflection_upper_sub_pole_tendsto q).norm.eventually_le_const
    (show ‖regularUpperOriginFinitePart q‖ < ‖regularUpperOriginFinitePart q‖+1 by linarith)
  obtain ⟨δ,hδ,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hb
  refine ⟨δ,hδ,fun p => MemLp.of_bound
    (renormalizedRegularUpperReflection_measurable q _).aestronglyMeasurable
      (‖regularUpperOriginFinitePart q‖+1) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact hbound hz

end
end GaloisForLFunctions.HTGeometry.FokasLenells
