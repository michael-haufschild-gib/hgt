import GaloisForLFunctions.HTGeometry.FokasLenellsRawContourFifthTrace
import GaloisForLFunctions.HTGeometry.FokasLenellsRegularOriginFinitePart
import GaloisForLFunctions.HTGeometry.FokasLenellsRegularNegativeOrigin

/-!
# A common finite part for the actual upper reflection on the full line

The actual transmission exchange, the mixed-moment invariance, and the
fifth trace covariance match both origin sides. Removing the unique
compatibility pole and filling its computed finite value gives a
continuous origin completion for arbitrary Schwartz spatial profiles.
-/

open Complex Matrix MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem common_two_ray_limit (f : ℝ → ℂ) (c : ℂ)
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

/-- The upper actual negative-ray transmission is the lower positive-ray transmission of the twisted profile. -/
theorem regularTransmission_upper_negative_exp_swap (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    regularScatteringMatrix q (-((Real.exp κ)^(2 : ℕ))) 1 1 =
      regularScatteringMatrix (twistedPotential q) ((Real.exp κ)^(2 : ℕ)) 0 0 := by
  rw [regularScatteringMatrix_negative_exp]
  change transmission (twistedPotential q) κ = _
  rw [regularTransmission_exp_eq_raw, rawScatteringMatrix_exp_eq]
  rfl

/-- The actual upper transmission has one common first coefficient in the signed squared spectral coordinate. -/
theorem regularTransmission_upper_two_sided_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => (regularScatteringMatrix q z 1 1-1)/(z : ℂ))
      (𝓝[≠] 0) (𝓝 (rawMixedTotal q)) := by
  apply common_two_ray_limit
  · exact regularTransmission_upper_right_quotient_tendsto q
  · have hh := (regularTransmission_lower_right_quotient_tendsto (twistedPotential q)).neg
    simp only [neg_neg, rawMixedTotal_twistedPotential] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    change 0 < z at hz
    have hd := regularTransmission_upper_negative_exp_swap q (Real.log (Real.sqrt z))
    rw [Real.exp_log (Real.sqrt_pos.mpr hz), Real.sq_sqrt hz.le] at hd
    change -((regularScatteringMatrix (twistedPotential q) z 0 0-1)/(z : ℂ)) =
      (regularScatteringMatrix q (-z) 1 1-1)/((-z : ℝ) : ℂ)
    rw [hd, Complex.ofReal_neg, div_neg]

private theorem regular_upper_signed_factor (q : SchwartzMap ℝ ℂ) (z : ℝ) (hz : z ≠ 0) :
    regularSecondInverseReflection q true z =
      signedOriginWeightedReflection q z/(2*regularScatteringMatrix q z 1 1) := by
  rcases lt_or_gt_of_ne hz with hn | hp
  · have hpos : 0 < -z := neg_pos.mpr hn
    have hh := (regularSecondInverseReflection_negative_exp_factor q (Real.log (Real.sqrt (-z)))).2
    rw [Real.exp_log (Real.sqrt_pos.mpr hpos), Real.sq_sqrt hpos.le, neg_neg] at hh
    simpa only [signedOriginWeightedReflection, not_le.mpr hn, ↓reduceIte] using hh
  · have hh := (regularSecondInverseReflection_exp_factor q (Real.log (Real.sqrt z))).2
    rw [Real.exp_log (Real.sqrt_pos.mpr hp), Real.sq_sqrt hp.le] at hh
    simpa only [signedOriginWeightedReflection, hp.le, ↓reduceIte] using hh

/-- Removing the actual compatibility pole gives the same transmission-corrected finite part from both sides. -/
theorem regularSecondInverseReflection_upper_two_sided_sub_pole_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (renormalizedRegularUpperReflection q (compatibilityMoment q))
      (𝓝[≠] 0) (𝓝 (regularUpperOriginFinitePart q)) := by
  have hT : Tendsto (fun z : ℝ => regularScatteringMatrix q z 1 1) (𝓝[≠] 0) (𝓝 1) :=
    (regularTransmission_diagonal_tendsto_zero q 1).mono_left nhdsWithin_le_nhds
  have hM : Tendsto (fun _ : ℝ => compatibilityMoment q) (𝓝[≠] 0)
      (𝓝 (compatibilityMoment q)) := tendsto_const_nhds
  have hN := ((signedOriginWeightedReflection_sub_pole_tendsto q).div_const (2 : ℂ)).sub
    (hM.mul (regularTransmission_upper_two_sided_quotient_tendsto q))
  have hh := hN.div hT one_ne_zero
  change Tendsto (fun z : ℝ =>
    ((signedOriginWeightedReflection q z-2*compatibilityMoment q/(z : ℂ))/2 -
      compatibilityMoment q*((regularScatteringMatrix q z 1 1-1)/(z : ℂ)))/
        regularScatteringMatrix q z 1 1)
    (𝓝[≠] 0) (𝓝 ((rawScatteringFifthCoefficient q 1 0/2 -
      compatibilityMoment q*rawMixedTotal q)/1)) at hh
  simp only [div_one] at hh
  apply hh.congr'
  have hne : ∀ᶠ z in 𝓝[≠] (0 : ℝ), regularScatteringMatrix q z 1 1 ≠ 0 :=
    ((regularTransmission_diagonal_tendsto_zero q 1).eventually_ne one_ne_zero).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne, self_mem_nhdsWithin] with z ht hz
  have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
  rw [renormalizedRegularUpperReflection, regular_upper_signed_factor q z hz]
  field_simp
  ring

/-- The same single residue is the unique subtraction giving a finite two-sided normalized limit. -/
theorem renormalizedRegularUpperReflection_two_sided_finite_limit_iff (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    (∃ d : ℂ, Tendsto (renormalizedRegularUpperReflection q c) (𝓝[≠] 0) (𝓝 d)) ↔
      c = compatibilityMoment q := by
  constructor
  · rintro ⟨d,hd⟩
    exact (renormalizedRegularUpperReflection_finite_limit_iff q c).1
      ⟨d,hd.mono_left (nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx))⟩
  · rintro rfl
    exact ⟨regularUpperOriginFinitePart q, regularSecondInverseReflection_upper_two_sided_sub_pole_tendsto q⟩

/-- Fill the pole-subtracted actual upper profile with its uniquely computed origin value. -/
def completedRegularUpperReflection (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℂ :=
  if z = 0 then regularUpperOriginFinitePart q
  else renormalizedRegularUpperReflection q (compatibilityMoment q) z

/-- The completed actual normalized profile is continuous at the spectral origin for every Schwartz profile. -/
theorem completedRegularUpperReflection_continuousAt_zero (q : SchwartzMap ℝ ℂ) :
    ContinuousAt (completedRegularUpperReflection q) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  have hz0 : completedRegularUpperReflection q 0 = regularUpperOriginFinitePart q := by
    simp [completedRegularUpperReflection]
  rw [hz0]
  apply (regularSecondInverseReflection_upper_two_sided_sub_pole_tendsto q).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change z ≠ 0 at hz
  simp [completedRegularUpperReflection, hz]

/-- Odd profiles have an explicitly evaluated normalized finite trace given by their first spatial moment. -/
theorem regularUpperOriginFinitePart_oddInitialPart (q : SchwartzMap ℝ ℂ) :
    regularUpperOriginFinitePart (oddInitialPart q) = 2*I*(∫ x : ℝ, (x : ℂ)*q x) := by
  simp only [regularUpperOriginFinitePart, rawScatteringFifthCoefficient_oddInitialPart_lower,
    compatibilityMoment_oddInitialPart, zero_mul, sub_zero]
  ring

/-- The compatible Gaussian-derivative family realizes every normalized finite origin value. -/
theorem regularUpperOriginFinitePart_quinticGaussianProfile (a : ℝ) (c : ℂ) :
    regularUpperOriginFinitePart (quinticGaussianProfile a c) = c/2 := by
  simp only [regularUpperOriginFinitePart, rawScatteringFifthCoefficient_quinticGaussianProfile,
    compatibilityMoment_quinticGaussianProfile, zero_mul, sub_zero]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
