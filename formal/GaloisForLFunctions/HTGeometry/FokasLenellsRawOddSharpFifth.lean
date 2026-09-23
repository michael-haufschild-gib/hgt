import GaloisForLFunctions.HTGeometry.FokasLenellsRawOddFifthCoefficient

/-!
# Sharp fifth-order reflection inside the compatible odd subspace

The evaluated fifth coefficient determines the exact boundary between
fifth-order and little-o fifth-order reflection. Projected derivatives of
normalized Gaussians realize every complex fifth coefficient while remaining
compatible, so compatibility alone forces no further cancellation.
-/

open Complex Matrix MeasureTheory Filter Topology Asymptotics
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The actual odd-data reflection quotient has an explicitly evaluated fifth-order limit. -/
theorem rawReflection_oddInitialPart_fifth_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℝ => rawScatteringMatrix (oddInitialPart q) k 1 0/(k : ℂ)^(5 : ℕ))
      (𝓝[≠] 0) (𝓝 (4*I*∫ x : ℝ, (x : ℂ)*q x)) := by
  simpa only [compatibilityMoment_oddInitialPart,mul_zero,sub_zero,
    rawScatteringFifthCoefficient_oddInitialPart_lower] using
      rawReflection_sub_cubic_quotient_tendsto (oddInitialPart q)

/-- Little-o improvement within the compatible odd subspace needs exactly one further moment cancellation. -/
theorem rawReflection_oddInitialPart_isLittleO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix (oddInitialPart q) k 1 0) =o[𝓝[≠] 0]
      fun k => (k : ℂ)^(5 : ℕ)) ↔ (∫ x : ℝ, (x : ℂ)*q x) = 0 := by
  constructor
  · intro h
    have hz := tendsto_nhds_unique (rawReflection_oddInitialPart_fifth_quotient_tendsto q)
      h.tendsto_div_nhds_zero
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) I_ne_zero)
  · intro hm
    apply (isLittleO_iff_tendsto' ?_).2
    · simpa only [hm,mul_zero] using rawReflection_oddInitialPart_fifth_quotient_tendsto q
    · filter_upwards [self_mem_nhdsWithin] with k hk
      exact fun h => (pow_ne_zero 5 (Complex.ofReal_ne_zero.mpr hk) h).elim

private theorem odd_exp_tendsto_punctured : Tendsto Real.exp atBot (𝓝[≠] (0 : ℝ)) :=
  Real.tendsto_exp_atBot_nhdsGT.mono_right
    (nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx))

/-- The original logarithmic-frequency amplitude has the same evaluated fifth coefficient. -/
theorem reflectionAmplitude_oddInitialPart_fifth_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun κ : ℝ => reflectionAmplitude (oddInitialPart q) κ/(Real.exp κ : ℂ)^(5 : ℕ))
      atBot (𝓝 (4*I*∫ x : ℝ, (x : ℂ)*q x)) := by
  have hh := (rawReflection_oddInitialPart_fifth_quotient_tendsto q).comp odd_exp_tendsto_punctured
  change Tendsto (fun κ : ℝ => rawScatteringMatrix (oddInitialPart q) (Real.exp κ) 1 0/(Real.exp κ : ℂ)^(5 : ℕ))
    atBot (𝓝 (4*I*∫ x : ℝ, (x : ℂ)*q x)) at hh
  simpa only [rawScatteringMatrix_exp_eq,reflectionAmplitude] using hh

/-- Reverse original reflection has the opposite evaluated fifth coefficient. -/
theorem reverseReflectionAmplitude_oddInitialPart_fifth_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun κ : ℝ => reverseReflectionAmplitude (oddInitialPart q) κ/(Real.exp κ : ℂ)^(5 : ℕ))
      atBot (𝓝 (-4*I*∫ x : ℝ, (x : ℂ)*q x)) := by
  have hh := (reflectionAmplitude_oddInitialPart_fifth_quotient_tendsto q).neg
  simpa only [reverseReflectionAmplitude_eq_neg,neg_div,neg_mul] using hh

/-- Original odd-data reflection improves beyond fifth order exactly at zero spatial first moment. -/
theorem reflectionAmplitude_oddInitialPart_isLittleO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun κ : ℝ => reflectionAmplitude (oddInitialPart q) κ) =o[atBot]
      fun κ => (Real.exp κ : ℂ)^(5 : ℕ)) ↔ (∫ x : ℝ, (x : ℂ)*q x) = 0 := by
  constructor
  · intro h
    have hz := tendsto_nhds_unique (reflectionAmplitude_oddInitialPart_fifth_quotient_tendsto q)
      h.tendsto_div_nhds_zero
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) I_ne_zero)
  · intro hm
    apply (isLittleO_iff_tendsto' ?_).2
    · simpa only [hm,mul_zero] using reflectionAmplitude_oddInitialPart_fifth_quotient_tendsto q
    · exact Eventually.of_forall fun κ h =>
        (pow_ne_zero 5 (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos κ))) h).elim

/-- A compatible Schwartz profile with an arbitrarily prescribed complex fifth coefficient. -/
def quinticGaussianProfile (a : ℝ) (c : ℂ) : SchwartzMap ℝ ℂ :=
  oddInitialPart (SchwartzMap.derivCLM ℂ ℂ ((I*c/4) • compatibilityGaussian a))

@[simp] theorem compatibilityMoment_quinticGaussianProfile (a : ℝ) (c : ℂ) :
    compatibilityMoment (quinticGaussianProfile a c) = 0 :=
  compatibilityMoment_oddInitialPart _

/-- The actual fifth coefficient is surjective even after imposing exact compatibility. -/
theorem rawScatteringFifthCoefficient_quinticGaussianProfile (a : ℝ) (c : ℂ) :
    rawScatteringFifthCoefficient (quinticGaussianProfile a c) 1 0 = c := by
  rw [quinticGaussianProfile,rawScatteringFifthCoefficient_oddDerivative_lower]
  simp only [_root_.smul_apply,smul_eq_mul,integral_const_mul,integral_compatibilityGaussian,mul_one]
  ring_nf
  simp only [I_sq]
  ring

/-- Every complex fifth coefficient occurs among genuine compatible scattering matrices. -/
theorem rawScatteringFifthCoefficient_surjective_on_compatible :
    ∀ c : ℂ, ∃ q : SchwartzMap ℝ ℂ, compatibilityMoment q = 0 ∧
      rawScatteringFifthCoefficient q 1 0 = c := by
  intro c
  exact ⟨quinticGaussianProfile 0 c,compatibilityMoment_quinticGaussianProfile 0 c,
    rawScatteringFifthCoefficient_quinticGaussianProfile 0 c⟩

/-- The positive-z weighted profile has the exact fifth trace on these compatible examples. -/
theorem originWeightedReflection_quinticGaussianProfile_tendsto (a : ℝ) (c : ℂ) :
    Tendsto (originWeightedReflection (quinticGaussianProfile a c)) (𝓝[>] 0) (𝓝 c) := by
  simpa only [compatibilityMoment_quinticGaussianProfile,mul_zero,zero_div,sub_zero,
    rawScatteringFifthCoefficient_quinticGaussianProfile] using
      originWeightedReflection_sub_pole_tendsto (quinticGaussianProfile a c)

/-- A concrete compatible family has exactly fifth order and cannot satisfy a little-o fifth estimate. -/
theorem rawReflection_quinticGaussianProfile_one_not_isLittleO_fifth (a : ℝ) :
    ¬ ((fun k : ℝ => rawScatteringMatrix (quinticGaussianProfile a 1) k 1 0) =o[𝓝[≠] 0]
      fun k => (k : ℂ)^(5 : ℕ)) := by
  intro h
  have ht : Tendsto (fun k : ℝ => rawScatteringMatrix (quinticGaussianProfile a 1) k 1 0/(k : ℂ)^(5 : ℕ))
      (𝓝[≠] 0) (𝓝 1) := by
    simpa only [compatibilityMoment_quinticGaussianProfile,mul_zero,sub_zero,
      rawScatteringFifthCoefficient_quinticGaussianProfile] using
        rawReflection_sub_cubic_quotient_tendsto (quinticGaussianProfile a 1)
  exact one_ne_zero (tendsto_nhds_unique ht h.tendsto_div_nhds_zero)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
