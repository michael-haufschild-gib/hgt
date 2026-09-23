import GaloisForLFunctions.HTGeometry.FokasLenellsContourMoment

/-!
# The sharp fifth-order condition on all four actual spectral rays

The source twist preserves the moment's zero locus. The exact ray norms
transport the real-axis criterion with the physical complex parameter.
Combining all four rays in a finite product also gives one uniform Big-O
bound, rather than four unrelated asymptotic assertions.
-/

open Complex Matrix MeasureTheory Filter Topology Asymptotics
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem contourReflection_fifth_bigO_transport (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) :
    ((fun κ : ℝ => contourReflectionAmplitude q vertical negative κ) =O[atBot]
      fun κ => (contourParameter vertical negative κ)^(5 : ℕ)) ↔
    ((fun κ : ℝ => reflectionAmplitude (contourSource q vertical) κ) =O[atBot]
      fun κ => (Real.exp κ : ℂ)^(5 : ℕ)) := by
  simp only [isBigO_iff,contourReflectionAmplitude_norm,norm_pow,contourParameter_norm,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

/-- The physical fifth-order decay condition is the same on every actual ray of the spectral cross. -/
theorem contourReflection_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    ((fun κ : ℝ => contourReflectionAmplitude q vertical negative κ) =O[atBot]
      fun κ => (contourParameter vertical negative κ)^(5 : ℕ)) ↔ compatibilityMoment q = 0 := by
  rw [contourReflection_fifth_bigO_transport,reflectionAmplitude_isBigO_fifth_iff,
    compatibilityMoment_contourSource_zero_iff]

theorem contourReverseReflection_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    ((fun κ : ℝ => contourReverseReflectionAmplitude q vertical negative κ) =O[atBot]
      fun κ => (contourParameter vertical negative κ)^(5 : ℕ)) ↔ compatibilityMoment q = 0 := by
  have he : (fun κ : ℝ => contourReverseReflectionAmplitude q vertical negative κ) =
      fun κ => -contourReflectionAmplitude q vertical negative κ := by
    funext κ
    exact contourReverseReflectionAmplitude_eq_neg q vertical negative κ
  rw [he,isBigO_neg_left,contourReflection_isBigO_fifth_iff]

private theorem contour_physical_fifth_norm (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    ((fun κ : ℝ => contourReflectionAmplitude q vertical negative κ) =O[atBot]
      fun κ => (Real.exp κ : ℂ)^(5 : ℕ)) ↔
    ((fun κ : ℝ => contourReflectionAmplitude q vertical negative κ) =O[atBot]
      fun κ => (contourParameter vertical negative κ)^(5 : ℕ)) := by
  simp only [isBigO_iff,norm_pow,contourParameter_norm,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

/-- One finite-product norm controls all four rays with a single asymptotic constant and neighborhood. -/
theorem contourReflections_uniform_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun κ : ℝ => fun vertical negative : Bool => contourReflectionAmplitude q vertical negative κ)
      =O[atBot] fun κ => (Real.exp κ : ℂ)^(5 : ℕ)) ↔ compatibilityMoment q = 0 := by
  simp only [isBigO_pi,contour_physical_fifth_norm,contourReflection_isBigO_fifth_iff,
    forall_const]

/-- Odd projected data satisfy the physical fifth-order estimate simultaneously on every ray. -/
theorem contourReflections_oddInitialPart_uniform_isBigO_fifth (q : SchwartzMap ℝ ℂ) :
    (fun κ : ℝ => fun vertical negative : Bool => contourReflectionAmplitude (oddInitialPart q) vertical negative κ)
      =O[atBot] fun κ => (Real.exp κ : ℂ)^(5 : ℕ) :=
  (contourReflections_uniform_isBigO_fifth_iff _).mpr (compatibilityMoment_oddInitialPart q)

/-- Even projected initial data need exactly zero mass on the full spectral cross as well. -/
theorem contourReflections_evenInitialPart_uniform_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun κ : ℝ => fun vertical negative : Bool => contourReflectionAmplitude (evenInitialPart q) vertical negative κ)
      =O[atBot] fun κ => (Real.exp κ : ℂ)^(5 : ℕ)) ↔ (∫ x : ℝ, q x) = 0 := by
  rw [contourReflections_uniform_isBigO_fifth_iff,compatibilityMoment_evenInitialPart]

/-- The explicitly small Gaussian violates the fifth-order assertion separately on every physical ray. -/
theorem contourReflection_globalSmallGaussian_not_isBigO_fifth (a : ℝ) (vertical negative : Bool) :
    ¬ ((fun κ : ℝ => contourReflectionAmplitude (globalSmallScatteringPotential (compatibilityGaussian a)) vertical negative κ)
      =O[atBot] fun κ => (contourParameter vertical negative κ)^(5 : ℕ)) := by
  rw [contourReflection_isBigO_fifth_iff]
  exact compatibilityMoment_globalSmallGaussian_ne_zero a

theorem contourReverseReflection_globalSmallGaussian_not_isBigO_fifth (a : ℝ) (vertical negative : Bool) :
    ¬ ((fun κ : ℝ => contourReverseReflectionAmplitude (globalSmallScatteringPotential (compatibilityGaussian a)) vertical negative κ)
      =O[atBot] fun κ => (contourParameter vertical negative κ)^(5 : ℕ)) := by
  rw [contourReverseReflection_isBigO_fifth_iff]
  exact compatibilityMoment_globalSmallGaussian_ne_zero a

end
end GaloisForLFunctions.HTGeometry.FokasLenells
