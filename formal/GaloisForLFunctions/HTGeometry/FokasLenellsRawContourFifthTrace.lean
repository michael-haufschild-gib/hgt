import GaloisForLFunctions.HTGeometry.FokasLenellsRawTwistScattering

/-!
# One actual fifth trace on all contour rays

After removing the cubic compatibility term, all four original spectral
rays have the same fifth trace for arbitrary Schwartz profiles. In the
squared coordinate this gives one two-sided finite part of the signed
weighted original reflection.
-/

open Complex Matrix MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem two_ray_tendsto (f : ℝ → ℂ) (c : ℂ)
    (hp : Tendsto f (𝓝[>] 0) (𝓝 c))
    (hn : Tendsto (fun z : ℝ => f (-z)) (𝓝[>] 0) (𝓝 c)) :
    Tendsto f (𝓝[≠] 0) (𝓝 c) := by
  have hneg : Tendsto (fun z : ℝ => -z) (𝓝[<] 0) (𝓝[>] 0) := by
    simpa only [neg_zero] using (tendsto_neg_nhdsLT (a := (0 : ℝ)))
  have hl := hn.comp hneg
  change Tendsto (fun z : ℝ => f (-(-z))) (𝓝[<] 0) (𝓝 c) at hl
  simp only [neg_neg] at hl
  rw [← nhdsLT_sup_nhdsGT]
  exact hl.sup hp

/-- The original logarithmic-frequency amplitude retains the genuine fifth trace after cubic subtraction. -/
theorem reflectionAmplitude_sub_cubic_fifth_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun κ : ℝ => (reflectionAmplitude q κ - (Real.exp κ : ℂ)^3*(2*compatibilityMoment q)) /
      (Real.exp κ : ℂ)^5) atBot (𝓝 (rawScatteringFifthCoefficient q 1 0)) := by
  have he : Tendsto Real.exp atBot (𝓝[≠] (0 : ℝ)) :=
    Real.tendsto_exp_atBot_nhdsGT.mono_right (nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx))
  have hh := (rawReflection_sub_cubic_quotient_tendsto q).comp he
  change Tendsto (fun κ : ℝ => (rawScatteringMatrix q (Real.exp κ) 1 0 -
    (Real.exp κ : ℂ)^3*(2*compatibilityMoment q))/(Real.exp κ : ℂ)^5) atBot
      (𝓝 (rawScatteringFifthCoefficient q 1 0)) at hh
  simpa only [rawScatteringMatrix_exp_eq, reflectionAmplitude] using hh

/-- The exact source twist also transports the subtracted cubic term with the physical fifth power. -/
theorem contourReflection_sub_cubic_fifth_quotient_eq (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    (contourReflectionAmplitude q vertical negative κ -
      (contourParameter vertical negative κ)^3*(2*compatibilityMoment q)) /
        (contourParameter vertical negative κ)^5 =
    (if vertical then I else 1)*
      ((reflectionAmplitude (contourSource q vertical) κ -
        (Real.exp κ : ℂ)^3*(2*compatibilityMoment (contourSource q vertical))) /(Real.exp κ : ℂ)^5) := by
  have he : (Real.exp κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero κ)
  have hi6 : (I : ℂ)^6 = -1 := by
    calc
      Complex.I^6 = Complex.I^4*Complex.I^2 := by ring
      _ = -1 := by rw [I_pow_four, I_sq, one_mul]
  have hi7 : (I : ℂ)^7 = -I := by
    calc
      Complex.I^7 = Complex.I^6*Complex.I := by ring
      _ = -I := by rw [hi6, neg_one_mul]
  rw [contourReflectionAmplitude_eq, compatibilityMoment_contourSource]
  cases vertical <;> cases negative <;>
    simp [contourParameter] <;> field_simp <;> ring_nf <;> simp [hi6, hi7]

/-- Every physical contour ray has the same actual fifth scattering trace after its cubic compatibility term is removed. -/
theorem contourReflection_sub_cubic_fifth_quotient_tendsto (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Tendsto (fun κ : ℝ => (contourReflectionAmplitude q vertical negative κ -
      (contourParameter vertical negative κ)^3*(2*compatibilityMoment q)) /
        (contourParameter vertical negative κ)^5) atBot (𝓝 (rawScatteringFifthCoefficient q 1 0)) := by
  have hh := (reflectionAmplitude_sub_cubic_fifth_quotient_tendsto (contourSource q vertical)).const_mul
    (if vertical then I else 1)
  have he : (if vertical then I else 1)*rawScatteringFifthCoefficient (contourSource q vertical) 1 0 =
      rawScatteringFifthCoefficient q 1 0 := by
    cases vertical <;> simp only [contourSource, Bool.false_eq_true, ↓reduceIte, one_mul,
      rawScatteringFifthCoefficient_twisted_lower, neg_mul, mul_neg, ← mul_assoc, I_mul_I,
      neg_neg]
  rw [he] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun κ => (contourReflection_sub_cubic_fifth_quotient_eq q vertical negative κ).symm)

/-- The reverse channel has the opposite cubic-subtracted fifth trace on every physical ray. -/
theorem contourReverseReflection_sub_cubic_fifth_quotient_tendsto (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Tendsto (fun κ : ℝ => (contourReverseReflectionAmplitude q vertical negative κ -
      (contourParameter vertical negative κ)^3*(-2*compatibilityMoment q)) /
        (contourParameter vertical negative κ)^5) atBot (𝓝 (-rawScatteringFifthCoefficient q 1 0)) := by
  apply (contourReflection_sub_cubic_fifth_quotient_tendsto q vertical negative).neg.congr'
  apply Eventually.of_forall
  intro κ
  dsimp only
  rw [contourReverseReflectionAmplitude_eq_neg]
  ring

/-- The signed original weighted profile has one common pole-subtracted finite trace from both sides of zero. -/
theorem signedOriginWeightedReflection_sub_pole_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => signedOriginWeightedReflection q z - 2*compatibilityMoment q/(z : ℂ))
      (𝓝[≠] 0) (𝓝 (rawScatteringFifthCoefficient q 1 0)) := by
  apply two_ray_tendsto
  · apply (originWeightedReflection_sub_pole_tendsto q).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    change 0 < z at hz
    simp [signedOriginWeightedReflection, le_of_lt hz]
  · have hh := (originWeightedReflection_sub_pole_tendsto (twistedPotential q)).const_mul I
    have he : I*rawScatteringFifthCoefficient (twistedPotential q) 1 0 = rawScatteringFifthCoefficient q 1 0 := by
      rw [rawScatteringFifthCoefficient_twisted_lower]
      simp only [neg_mul, mul_neg, ← mul_assoc, I_mul_I, neg_neg, one_mul]
    rw [he] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    change 0 < z at hz
    simp only [signedOriginWeightedReflection, not_le.mpr (neg_neg_of_pos hz), ↓reduceIte,
      neg_neg, compatibilityMoment_twistedPotential, Complex.ofReal_neg]
    ring_nf
    simp

end
end GaloisForLFunctions.HTGeometry.FokasLenells
