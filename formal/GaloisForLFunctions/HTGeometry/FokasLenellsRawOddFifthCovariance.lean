import GaloisForLFunctions.HTGeometry.FokasLenellsRawOddSharpFifth

/-!
# The evaluated odd-data fifth coefficient on every physical spectral ray

The imaginary source twist changes the first moment by -I. The physical
fifth denominator contributes the compensating I, making the fifth trace
identical on all four rays. Complex scaling and smallness normalization
retain the exact linear first-moment law on the odd subspace.
-/

open Complex Matrix MeasureTheory Filter Topology Asymptotics
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem oddInitialPart_smul (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    oddInitialPart (c • q) = c • oddInitialPart q := by
  ext x
  simp only [oddInitialPart_apply,_root_.smul_apply,smul_eq_mul]
  ring

theorem oddInitialPart_twistedPotential (q : SchwartzMap ℝ ℂ) :
    oddInitialPart (twistedPotential q) = twistedPotential (oddInitialPart q) := by
  ext x
  simp only [oddInitialPart_apply,twistedPotential_apply,neg_neg]
  ring

theorem oddInitialPart_contourSource (q : SchwartzMap ℝ ℂ) (vertical : Bool) :
    oddInitialPart (contourSource q vertical) = contourSource (oddInitialPart q) vertical := by
  cases vertical <;> simp [contourSource,oddInitialPart_twistedPotential]

/-- The imaginary source twist has the exact first-moment phase needed for contour invariance. -/
theorem integral_coordinate_twistedPotential (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (x : ℂ)*twistedPotential q x) = -I*∫ x : ℝ, (x : ℂ)*q x := by
  have he : (fun x : ℝ => (x : ℂ)*twistedPotential q x) =
      fun x : ℝ => -I*(((-x : ℝ) : ℂ)*q (-x)) := by
    funext x
    rw [twistedPotential_apply,Complex.ofReal_neg]
    ring
  rw [he,integral_const_mul,integral_neg_eq_self (fun x : ℝ => (x : ℂ)*q x) volume]

/-- Exact physical fifth quotient, with both square-root signs canceled. -/
theorem contourReflection_fifth_quotient_eq (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    contourReflectionAmplitude q vertical negative κ/(contourParameter vertical negative κ)^5 =
      (if vertical then I else 1)*(reflectionAmplitude (contourSource q vertical) κ/(Real.exp κ : ℂ)^5) := by
  rw [← signedOriginWeightedReflection_eq_contour]
  have hp : 0 < (Real.exp κ)^2 := sq_pos_of_pos (Real.exp_pos κ)
  cases vertical <;> simp [contourSquaredParameter,signedOriginWeightedReflection,
    hp.le,not_le.mpr (neg_neg_of_pos hp),originWeightedReflection_exp,contourSource]

/-- The evaluated fifth trace is identical on all four actual physical rays for odd initial data. -/
theorem contourReflection_oddInitialPart_fifth_quotient_tendsto (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) :
    Tendsto (fun κ : ℝ => contourReflectionAmplitude (oddInitialPart q) vertical negative κ/
      (contourParameter vertical negative κ)^5) atBot (𝓝 (4*I*∫ x : ℝ, (x : ℂ)*q x)) := by
  have hh := (reflectionAmplitude_oddInitialPart_fifth_quotient_tendsto (contourSource q vertical)).const_mul
    (if vertical then I else 1)
  have hf : (fun κ : ℝ => contourReflectionAmplitude (oddInitialPart q) vertical negative κ/
      (contourParameter vertical negative κ)^5) = fun κ : ℝ =>
      (if vertical then I else 1)*(reflectionAmplitude (oddInitialPart (contourSource q vertical)) κ/(Real.exp κ : ℂ)^5) := by
    funext κ
    rw [contourReflection_fifth_quotient_eq,oddInitialPart_contourSource]
  rw [hf]
  have hc : (if vertical then I else 1)*(4*I*∫ x : ℝ, (x : ℂ)*contourSource q vertical x) =
      4*I*∫ x : ℝ, (x : ℂ)*q x := by
    cases vertical
    · simp [contourSource]
    · simp only [↓reduceIte,contourSource,integral_coordinate_twistedPotential]
      ring_nf
      simp only [I_pow_three]
      ring
  simpa only [hc] using hh

/-- The reverse fifth trace has the opposite sign on every physical ray. -/
theorem contourReverseReflection_oddInitialPart_fifth_quotient_tendsto (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) :
    Tendsto (fun κ : ℝ => contourReverseReflectionAmplitude (oddInitialPart q) vertical negative κ/
      (contourParameter vertical negative κ)^5) atBot (𝓝 (-4*I*∫ x : ℝ, (x : ℂ)*q x)) := by
  simpa only [contourReverseReflectionAmplitude_eq_neg,neg_div,neg_mul] using
    (contourReflection_oddInitialPart_fifth_quotient_tendsto q vertical negative).neg

/-- Each physical ray improves beyond fifth order exactly at the same first-moment boundary. -/
theorem contourReflection_oddInitialPart_isLittleO_fifth_iff (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) :
    ((fun κ : ℝ => contourReflectionAmplitude (oddInitialPart q) vertical negative κ) =o[atBot]
      fun κ => (contourParameter vertical negative κ)^5) ↔ (∫ x : ℝ, (x : ℂ)*q x) = 0 := by
  constructor
  · intro h
    have hz := tendsto_nhds_unique (contourReflection_oddInitialPart_fifth_quotient_tendsto q vertical negative)
      h.tendsto_div_nhds_zero
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) I_ne_zero)
  · intro hm
    apply (isLittleO_iff_tendsto' ?_).2
    · simpa only [hm,mul_zero] using contourReflection_oddInitialPart_fifth_quotient_tendsto q vertical negative
    · exact Eventually.of_forall fun κ h => (pow_ne_zero 5 (contourParameter_ne_zero vertical negative κ) h).elim

/-- Complex amplitude scaling is exactly linear at fifth order throughout the compatible odd subspace. -/
theorem rawScatteringFifthCoefficient_scaled_oddInitialPart (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    rawScatteringFifthCoefficient (c • oddInitialPart q) 1 0 =
      c*(4*I*∫ x : ℝ, (x : ℂ)*q x) := by
  rw [← oddInitialPart_smul,rawScatteringFifthCoefficient_oddInitialPart_lower]
  have he : (fun x : ℝ => (x : ℂ)*(c • q) x) = fun x : ℝ => c*((x : ℂ)*q x) := by
    funext x
    simp only [_root_.smul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul]
  ring

/-- The actual smallness normalization preserves the exact fifth trace up to its explicit positive scale. -/
theorem rawScatteringFifthCoefficient_globalSmall_oddInitialPart (q : SchwartzMap ℝ ℂ) :
    rawScatteringFifthCoefficient (globalSmallScatteringPotential (oddInitialPart q)) 1 0 =
      (globalScatteringScale (oddInitialPart q) : ℂ)*(4*I*∫ x : ℝ, (x : ℂ)*q x) := by
  rw [globalSmallScatteringPotential,rawScatteringFifthCoefficient_scaled_oddInitialPart]

/-- A globally small compatible profile retains a nonzero fifth coefficient. -/
theorem rawScatteringFifthCoefficient_globalSmall_quinticGaussianProfile_one_ne_zero (a : ℝ) :
    rawScatteringFifthCoefficient (globalSmallScatteringPotential (quinticGaussianProfile a 1)) 1 0 ≠ 0 := by
  have hc := rawScatteringFifthCoefficient_quinticGaussianProfile a 1
  change rawScatteringFifthCoefficient (oddInitialPart _) 1 0 = 1 at hc
  rw [rawScatteringFifthCoefficient_oddInitialPart_lower] at hc
  change rawScatteringFifthCoefficient (globalSmallScatteringPotential (oddInitialPart _)) 1 0 ≠ 0
  rw [rawScatteringFifthCoefficient_globalSmall_oddInitialPart,hc,mul_one]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (globalScatteringScale_pos _))

/-- Explicit small-data normalization keeps the entire prescribed-trace family compatible. -/
theorem compatibilityMoment_globalSmall_quinticGaussianProfile (a : ℝ) (c : ℂ) :
    compatibilityMoment (globalSmallScatteringPotential (quinticGaussianProfile a c)) = 0 := by
  rw [quinticGaussianProfile,globalSmallScatteringPotential,← oddInitialPart_smul,
    compatibilityMoment_oddInitialPart]

/-- Fifth order remains sharp even within the corpus's explicitly globally small compatible data. -/
theorem rawReflection_globalSmall_quinticGaussianProfile_one_not_isLittleO_fifth (a : ℝ) :
    ¬ ((fun k : ℝ => rawScatteringMatrix (globalSmallScatteringPotential (quinticGaussianProfile a 1)) k 1 0)
      =o[𝓝[≠] 0] fun k => (k : ℂ)^5) := by
  intro h
  have ht := rawReflection_sub_cubic_quotient_tendsto
    (globalSmallScatteringPotential (quinticGaussianProfile a 1))
  simp only [compatibilityMoment_globalSmall_quinticGaussianProfile,mul_zero,sub_zero] at ht
  exact rawScatteringFifthCoefficient_globalSmall_quinticGaussianProfile_one_ne_zero a
    (tendsto_nhds_unique ht h.tendsto_div_nhds_zero)

/-- On odd projected derivatives, the next cancellation is exactly zero mass of the parent profile. -/
theorem rawReflection_oddDerivative_isLittleO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix (oddInitialPart (SchwartzMap.derivCLM ℂ ℂ q)) k 1 0)
      =o[𝓝[≠] 0] fun k => (k : ℂ)^5) ↔ (∫ x : ℝ, q x) = 0 := by
  rw [rawReflection_oddInitialPart_isLittleO_fifth_iff]
  simp only [SchwartzMap.derivCLM_apply,integral_coordinate_derivative,neg_eq_zero]

/-- Two existing Schwartz derivatives supply an unconditional family beyond fifth order. -/
theorem rawReflection_oddSecondDerivative_isLittleO_fifth (q : SchwartzMap ℝ ℂ) :
    (fun k : ℝ => rawScatteringMatrix
      (oddInitialPart (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))) k 1 0)
      =o[𝓝[≠] 0] fun k => (k : ℂ)^5 := by
  rw [rawReflection_oddDerivative_isLittleO_fifth_iff]
  simpa only [SchwartzMap.derivCLM_apply] using RHTower.integral_deriv_schwartz_eq_zero q

/-- The same unconditional derivative family improves beyond fifth order on every actual contour ray. -/
theorem contourReflection_oddSecondDerivative_isLittleO_fifth (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) :
    (fun κ : ℝ => contourReflectionAmplitude
      (oddInitialPart (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))) vertical negative κ)
      =o[atBot] fun κ => (contourParameter vertical negative κ)^5 := by
  rw [contourReflection_oddInitialPart_isLittleO_fifth_iff]
  simp only [SchwartzMap.derivCLM_apply,integral_coordinate_derivative,neg_eq_zero]
  exact RHTower.integral_deriv_schwartz_eq_zero q

end
end GaloisForLFunctions.HTGeometry.FokasLenells
