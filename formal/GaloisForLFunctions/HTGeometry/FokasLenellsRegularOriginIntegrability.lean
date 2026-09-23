import GaloisForLFunctions.HTGeometry.FokasLenellsRegularOrigin

/-!
# The sharp local second-inverse-weight criterion for actual reflection coefficients

On the positive squared spectral axis, the paper's r2/z^(2 : ℕ) always belongs
to every local L^p. Its r1/z^(2 : ℕ) belongs locally to L^(2 : ℕ) exactly on the
compatibility locus. The proof compares the actual transmission quotient
with the original weighted profile, using a proved neighborhood bound.
-/

open Complex Matrix MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem finite_limit_memLp_window (f : ℝ → ℂ) (hf : Measurable f)
    (c : ℂ) (hc : Tendsto f (𝓝[>] 0) (𝓝 c)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞, MemLp f p (volume.restrict (Ioo 0 δ)) := by
  have hb := hc.norm.eventually_le_const (show ‖c‖ < ‖c‖+1 by linarith)
  obtain ⟨δ,hδ,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hb
  refine ⟨δ,hδ,fun p => MemLp.of_bound hf.aestronglyMeasurable (‖c‖+1) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact hbound hz

private theorem local_upper_controls_weighted (q : SchwartzMap ℝ ℂ) (p : ℝ≥0∞)
    (h : ∃ δ : ℝ, 0 < δ ∧ MemLp (regularSecondInverseReflection q true) p (volume.restrict (Ioo 0 δ))) :
    ∃ δ : ℝ, 0 < δ ∧ MemLp (originWeightedReflection q) p (volume.restrict (Ioo 0 δ)) := by
  obtain ⟨r,hr,hR⟩ := h
  obtain ⟨ε,hε,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (regularSecondInverseReflection_upper_eventually_controls_origin q)
  have hRs : MemLp (regularSecondInverseReflection q true) p (volume.restrict (Ioo 0 (min r ε))) :=
    MemLp.mono_measure (Measure.restrict_mono (Ioo_subset_Ioo le_rfl (min_le_left _ _)) le_rfl) hR
  refine ⟨min r ε,lt_min hr hε,?_⟩
  apply (hRs.norm.const_mul (4 : ℝ)).mono' (originWeightedReflection_measurable q).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact hbound ⟨hz.1,lt_of_lt_of_le hz.2 (min_le_right _ _)⟩

/-- The lower channel (-r2) unconditionally satisfies every local second-inverse-weight L^p bound. -/
theorem regularSecondInverseReflection_lower_locally_memLp_all (q : SchwartzMap ℝ ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (regularSecondInverseReflection q false) p (volume.restrict (Ioo 0 δ)) :=
  finite_limit_memLp_window _ (regularSecondInverseReflection_measurable q false)
    _ (regularSecondInverseReflection_lower_tendsto q)

/-- The upper channel (r1) has the exact compatibility obstruction to the paper's local weighted L^(2 : ℕ) claim. -/
theorem regularSecondInverseReflection_upper_locally_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (regularSecondInverseReflection q true) 2
      (volume.restrict (Ioo 0 δ))) ↔ compatibilityMoment q = 0 := by
  constructor
  · intro h
    exact (originWeightedReflection_locally_memLp_two_iff q).1 (local_upper_controls_weighted q 2 h)
  · intro hm
    obtain ⟨c,hc⟩ := (regularSecondInverseReflection_upper_finite_limit_iff q).2 hm
    obtain ⟨δ,hδ,hW⟩ := finite_limit_memLp_window _ (regularSecondInverseReflection_measurable q true) c hc
    exact ⟨δ,hδ,hW 2⟩

/-- Removing the compatibility obstruction gives one common upper-channel interval for every exponent. -/
theorem regularSecondInverseReflection_upper_locally_memLp_all_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞, MemLp (regularSecondInverseReflection q true) p
      (volume.restrict (Ioo 0 δ))) ↔ compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    exact (regularSecondInverseReflection_upper_locally_memLp_two_iff q).1 ⟨δ,hδ,hW 2⟩
  · intro hm
    obtain ⟨c,hc⟩ := (regularSecondInverseReflection_upper_finite_limit_iff q).2 hm
    exact finite_limit_memLp_window _ (regularSecondInverseReflection_measurable q true) c hc

/-- Explicit small Gaussian data fail the actual upper normalized coefficient's weighted claim on every window. -/
theorem regularSecondInverseReflection_upper_globalSmallGaussian_not_memLp_two (a r : ℝ) :
    ¬ MemLp (regularSecondInverseReflection (globalSmallScatteringPotential (compatibilityGaussian a)) true) 2
      (volume.restrict (Ioo 0 (Real.exp r))) := by
  intro h
  exact compatibilityMoment_globalSmallGaussian_ne_zero a
    ((regularSecondInverseReflection_upper_locally_memLp_two_iff _).1 ⟨Real.exp r,Real.exp_pos r,h⟩)

/-- Odd profiles satisfy the actual upper weighted conclusion, with all exponents on one interval. -/
theorem regularSecondInverseReflection_upper_oddInitialPart_memLp_all (q : SchwartzMap ℝ ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (regularSecondInverseReflection (oddInitialPart q) true) p (volume.restrict (Ioo 0 δ)) :=
  (regularSecondInverseReflection_upper_locally_memLp_all_iff _).2 (compatibilityMoment_oddInitialPart q)

/-- Both actual normalized channels satisfy the paper's local L^(2 : ℕ) conclusion exactly on the compatibility locus. -/
theorem regularSecondInverseReflection_both_locally_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    ((∃ δ : ℝ, 0 < δ ∧ MemLp (regularSecondInverseReflection q false) 2 (volume.restrict (Ioo 0 δ))) ∧
     (∃ δ : ℝ, 0 < δ ∧ MemLp (regularSecondInverseReflection q true) 2 (volume.restrict (Ioo 0 δ)))) ↔
      compatibilityMoment q = 0 := by
  constructor
  · intro h
    exact (regularSecondInverseReflection_upper_locally_memLp_two_iff q).1 h.2
  · intro hm
    obtain ⟨δ,hδ,hW⟩ := regularSecondInverseReflection_lower_locally_memLp_all q
    exact ⟨⟨δ,hδ,hW 2⟩,(regularSecondInverseReflection_upper_locally_memLp_two_iff q).2 hm⟩

end
end GaloisForLFunctions.HTGeometry.FokasLenells
