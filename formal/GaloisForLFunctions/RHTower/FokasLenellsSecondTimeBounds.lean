import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeSymbols

/-!
# Bounded second time generators

The origin limits and the globally bounded first inverse weight give a
uniform bound for the second generator. The upper channel is bounded
exactly at compatibility. The odd projection constructs compatible data
internally and therefore supplies bounded operators without hypotheses.
-/

open MeasureTheory Complex Matrix Filter Topology Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem second_inverse_bounded_of_limits (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (c d : ℂ)
    (hc : Tendsto (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) (𝓝[>] 0) (𝓝 c))
    (hd : Tendsto (fun z : ℝ => regularSecondInverseReflection (globalSmallScatteringPotential q) reverse (-z))
      (𝓝[>] 0) (𝓝 d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, ‖regularSecondInverseReflection (globalSmallScatteringPotential q) reverse z‖ ≤ C := by
  let f := regularSecondInverseReflection (globalSmallScatteringPotential q) reverse
  have hcp := hc.norm.eventually_le_const (show ‖c‖ < ‖c‖+1 by linarith)
  have hdp := hd.norm.eventually_le_const (show ‖d‖ < ‖d‖+1 by linarith)
  obtain ⟨εp,hεp,hp⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hcp
  obtain ⟨εn,hεn,hn⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hdp
  let δ := min εp εn
  have hδ : 0 < δ := lt_min hεp hεn
  let K := max (max (‖c‖+1) (‖d‖+1)) ‖f 0‖
  refine ⟨max K (regularReflectionFrequencyBudget q/δ),
    (norm_nonneg (f 0)).trans ((le_max_right _ _).trans (le_max_left _ _)),fun z => ?_⟩
  by_cases hz : z ∈ Ioo (-δ) δ
  · apply le_trans (b := K) _ (le_max_left _ _)
    rcases lt_trichotomy z 0 with hneg | hzero | hpos
    · have hzn : -z ∈ Ioo 0 εn := ⟨neg_pos.mpr hneg,by linarith [min_le_right εp εn,hz.1]⟩
      have hh := hn hzn
      change ‖f (-(-z))‖ ≤ ‖d‖+1 at hh
      simp only [neg_neg] at hh
      exact hh.trans ((le_max_right _ _).trans (le_max_left _ _))
    · subst z
      exact le_max_right _ _
    · have hzp : z ∈ Ioo 0 εp := ⟨hpos,lt_of_lt_of_le hz.2 (min_le_left εp εn)⟩
      exact (hp hzp).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have hlarge : δ ≤ |z| := by
      by_contra hh
      exact hz (abs_lt.mp (lt_of_not_ge hh))
    apply le_trans (b := regularReflectionFrequencyBudget q/δ) _ (le_max_right _ _)
    rw [regularSecondInverseReflection_globalSmall_eq,norm_div,Complex.norm_real,Real.norm_eq_abs]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) hδ hlarge).trans
      (div_le_div_of_nonneg_right (regularInverseFrequencyReflection_bound q reverse z) hδ.le)

/-- The lower second inverse channel is globally bounded for arbitrary constructed small data. -/
theorem regularSecondInverseReflection_lower_globalSmall_bounded (q : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, ‖regularSecondInverseReflection (globalSmallScatteringPotential q) false z‖ ≤ C :=
  second_inverse_bounded_of_limits q false _ _ (regularSecondInverseReflection_lower_tendsto _)
    (regularSecondInverseReflection_lower_negative_tendsto _)

/-- Compatibility is also the exact global boundedness gate for the upper second inverse channel. -/
theorem regularSecondInverseReflection_upper_globalSmall_bounded_iff (q : SchwartzMap ℝ ℂ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, ‖regularSecondInverseReflection (globalSmallScatteringPotential q) true z‖ ≤ C) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · rintro ⟨C,_,hC⟩
    apply (regularSecondInverseReflection_upper_locally_memLp_two_iff _).1
    exact ⟨1,by norm_num,MemLp.of_bound (regularSecondInverseReflection_measurable _ true).aestronglyMeasurable
      C (Eventually.of_forall hC)⟩
  · intro hm
    obtain ⟨c,hc⟩ := (regularSecondInverseReflection_upper_finite_limit_iff _).2 hm
    obtain ⟨d,hd⟩ := (regularSecondInverseReflection_upper_negative_finite_limit_iff _).2 hm
    exact second_inverse_bounded_of_limits q true c d hc hd

/-- Smallness normalization preserves compatibility of the entire odd Schwartz subspace. -/
theorem compatibilityMoment_globalSmall_oddInitialPart (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment (globalSmallScatteringPotential (oddInitialPart q)) = 0 := by
  rw [globalSmallScatteringPotential,← oddInitialPart_smul,compatibilityMoment_oddInitialPart]

/-- Both second inverse channels of internally constructed odd data are globally bounded. -/
theorem regularSecondInverseReflection_globalSmall_oddInitialPart_bounded (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ,
      ‖regularSecondInverseReflection (globalSmallScatteringPotential (oddInitialPart q)) reverse z‖ ≤ C := by
  cases reverse
  · exact regularSecondInverseReflection_lower_globalSmall_bounded _
  · exact (regularSecondInverseReflection_upper_globalSmall_bounded_iff _).2
      (compatibilityMoment_globalSmall_oddInitialPart q)

/-- A selected finite budget for the actual second-time symbol of odd projected data. -/
def compatibleSecondTimeBudget (q : SchwartzMap ℝ ℂ) (reverse : Bool) : ℝ :=
  (1/4 : ℝ)*(regularSecondInverseReflection_globalSmall_oddInitialPart_bounded q reverse).choose

theorem compatibleSecondTimeBudget_nonneg (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    0 ≤ compatibleSecondTimeBudget q reverse :=
  mul_nonneg (by positivity) (regularSecondInverseReflection_globalSmall_oddInitialPart_bounded q reverse).choose_spec.1

/-- The bound is simultaneous in both physical parameters and every spectral point. -/
theorem directSecondTimeSymbol_oddInitialPart_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSecondTimeSymbol (oddInitialPart q) t x reverse z‖ ≤ compatibleSecondTimeBudget q reverse := by
  rw [directSecondTimeSymbol_norm]
  exact mul_le_mul_of_nonneg_left
    ((regularSecondInverseReflection_globalSmall_oddInitialPart_bounded q reverse).choose_spec.2 z) (by positivity)

/-- Both actual second-time symbols of every odd projected profile belong to L2. -/
theorem directSecondTimeSymbol_oddInitialPart_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    MemLp (directSecondTimeSymbol (oddInitialPart q) t x reverse) 2 volume := by
  cases reverse
  · exact directSecondTimeSymbol_lower_memLp _ t x
  · exact (directSecondTimeSymbol_upper_memLp_iff _ t x).2 (compatibilityMoment_globalSmall_oddInitialPart q)

end
end RHTower.FokasLenells
