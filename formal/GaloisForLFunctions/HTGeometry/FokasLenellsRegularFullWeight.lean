import GaloisForLFunctions.HTGeometry.FokasLenellsRegularNegativeOrigin
import GaloisForLFunctions.HTGeometry.FokasLenellsRegularSecondInverseJump

/-!
# The full-real-line second-inverse-weight classification

The exact signed-z gauge supplies both sides of the origin. The existing
global first inverse weight supplies both tails. Together they give the
sharp replacement for the weighted part of Proposition 3.10: the lower
channel always satisfies it for the constructed small Schwartz data;
the upper channel satisfies it exactly on the compatibility locus.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem two_limits_memLp_window (f : ℝ → ℂ) (hf : Measurable f) (c d : ℂ)
    (hc : Tendsto f (𝓝[>] 0) (𝓝 c))
    (hd : Tendsto (fun z : ℝ => f (-z)) (𝓝[>] 0) (𝓝 d)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞, MemLp f p (volume.restrict (Ioo (-δ) δ)) := by
  have hcp := hc.norm.eventually_le_const (show ‖c‖ < ‖c‖+1 by linarith)
  have hdp := hd.norm.eventually_le_const (show ‖d‖ < ‖d‖+1 by linarith)
  obtain ⟨εp,hεp,hp⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hcp
  obtain ⟨εn,hεn,hn⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hdp
  refine ⟨min εp εn,lt_min hεp hεn,fun p => MemLp.of_bound hf.aestronglyMeasurable
    (max (max (‖c‖+1) (‖d‖+1)) ‖f 0‖) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  rcases lt_trichotomy z 0 with hneg | hzero | hpos
  · have hzn : -z ∈ Ioo 0 εn := ⟨neg_pos.mpr hneg, by linarith [min_le_right εp εn, hz.1]⟩
    have hh := hn hzn
    change ‖f (-(-z))‖ ≤ ‖d‖+1 at hh
    simp only [neg_neg] at hh
    exact hh.trans ((le_max_right _ _).trans (le_max_left _ _))
  · subst z
    exact le_max_right _ _
  · have hzp : z ∈ Ioo 0 εp := ⟨hpos,lt_of_lt_of_le hz.2 (min_le_left _ _)⟩
    exact (hp hzp).trans ((le_max_left _ _).trans (le_max_left _ _))

/-- The actual lower weighted channel is locally in every Lp across both sides of the origin. -/
theorem regularSecondInverseReflection_lower_two_sided_locally_memLp_all (q : SchwartzMap ℝ ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (regularSecondInverseReflection q false) p (volume.restrict (Ioo (-δ) δ)) :=
  two_limits_memLp_window _ (regularSecondInverseReflection_measurable q false) _ _
    (regularSecondInverseReflection_lower_tendsto q) (regularSecondInverseReflection_lower_negative_tendsto q)

/-- The upper weighted channel is locally in every Lp across the full origin exactly at compatibility. -/
theorem regularSecondInverseReflection_upper_two_sided_locally_memLp_all_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (regularSecondInverseReflection q true) p (volume.restrict (Ioo (-δ) δ))) ↔
      compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨δ,hδ,hW⟩
    apply (regularSecondInverseReflection_upper_locally_memLp_two_iff q).1
    refine ⟨δ,hδ,?_⟩
    exact MemLp.mono_measure
      (Measure.restrict_mono (Ioo_subset_Ioo (by linarith : -δ ≤ 0) le_rfl) le_rfl) (hW 2)
  · intro hm
    obtain ⟨c,hc⟩ := (regularSecondInverseReflection_upper_finite_limit_iff q).2 hm
    obtain ⟨d,hd⟩ := (regularSecondInverseReflection_upper_negative_finite_limit_iff q).2 hm
    exact two_limits_memLp_window _ (regularSecondInverseReflection_measurable q true) c d hc hd

private theorem regular_second_inverse_full_of_local (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (h : ∃ δ : ℝ, 0 < δ ∧ MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) 2
      (volume.restrict (Ioo (-δ) δ))) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) 2 volume := by
  obtain ⟨δ,hδ,hlocal⟩ := h
  have hfirst := (regularInverseFrequencyReflection_memLp q reverse).restrict ((Ioo (-δ) δ)ᶜ)
  have htail : MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) 2
      (volume.restrict ((Ioo (-δ) δ)ᶜ)) := by
    apply (hfirst.norm.const_mul (δ⁻¹)).mono'
      (regularSecondInverseReflection_measurable _ reverse).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with z hz
    have hlarge : δ ≤ |z| := by
      by_contra hh
      have hsmall : |z| < δ := lt_of_not_ge hh
      exact hz (abs_lt.mp hsmall)
    rw [regularSecondInverseReflection_globalSmall_eq, norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) hδ hlarge).trans_eq (by ring)
  have hL := (memLp_indicator_iff_restrict measurableSet_Ioo).2 hlocal
  have hR := (memLp_indicator_iff_restrict measurableSet_Ioo.compl).2 htail
  apply MemLp.ae_eq ?_ (hL.add hR)
  apply Eventually.of_forall
  intro z
  change (Ioo (-δ) δ).indicator (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) z +
    ((Ioo (-δ) δ)ᶜ).indicator (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) z = _
  by_cases hz : z ∈ Ioo (-δ) δ <;> simp [hz]

/-- The paper's second inverse weight for the lower (-r2) channel holds on the entire real line. -/
theorem regularSecondInverseReflection_lower_globalSmall_memLp (q : SchwartzMap ℝ ℂ) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) false) 2 volume := by
  obtain ⟨δ,hδ,hW⟩ := regularSecondInverseReflection_lower_two_sided_locally_memLp_all (globalSmallScatteringPotential q)
  exact regular_second_inverse_full_of_local q false ⟨δ,hδ,hW 2⟩

/-- The exact full-real-line replacement for the upper (r1) weighted claim is the nonlinear compatibility condition. -/
theorem regularSecondInverseReflection_upper_globalSmall_memLp_iff (q : SchwartzMap ℝ ℂ) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) true) 2 volume ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · intro h
    exact (regularSecondInverseReflection_upper_globalSmall_positive_memLp_iff q).1 (h.restrict (Ioi 0))
  · intro hm
    obtain ⟨δ,hδ,hW⟩ := (regularSecondInverseReflection_upper_two_sided_locally_memLp_all_iff
      (globalSmallScatteringPotential q)).2 hm
    exact regular_second_inverse_full_of_local q true ⟨δ,hδ,hW 2⟩

/-- The global condition is an explicit cubic balance in the original unscaled Schwartz profile. -/
theorem regularSecondInverseReflection_upper_globalSmall_iff_balance (q : SchwartzMap ℝ ℂ) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) true) 2 volume ↔
      (∫ x : ℝ, q x) = I*(globalScatteringScale q : ℂ)^2*parityCoupling q := by
  rw [regularSecondInverseReflection_upper_globalSmall_memLp_iff,
    ← regularSecondInverseReflection_upper_globalSmall_positive_memLp_iff]
  exact regularSecondInverseReflection_upper_globalSmall_positive_iff_balance q

/-- Compatible examples with arbitrary prescribed unscaled fifth coefficient satisfy the full weighted assertion. -/
theorem regularSecondInverseReflection_upper_globalSmall_quinticGaussianProfile_memLp (a : ℝ) (c : ℂ) :
    MemLp (regularSecondInverseReflection (globalSmallScatteringPotential (quinticGaussianProfile a c)) true) 2 volume :=
  (regularSecondInverseReflection_upper_globalSmall_memLp_iff _).2
    (compatibilityMoment_globalSmall_quinticGaussianProfile a c)

/-- The full-real-line lower weighted estimate survives every physical time and position phase. -/
theorem regularSecondInverseJump_lower_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    MemLp (regularSecondInverseJump q t x false) 2 volume :=
  (regularSecondInverseJump_memLp_iff q t x false 2 volume).2
    (regularSecondInverseReflection_lower_globalSmall_memLp q)

/-- The upper full-real-line jump estimate is equivalent to the same compatibility condition at every time and position. -/
theorem regularSecondInverseJump_upper_memLp_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    MemLp (regularSecondInverseJump q t x true) 2 volume ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  rw [regularSecondInverseJump_memLp_iff, regularSecondInverseReflection_upper_globalSmall_memLp_iff]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
