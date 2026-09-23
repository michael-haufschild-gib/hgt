import GaloisForLFunctions.HTGeometry.FokasLenellsRawReflectionOrder

/-!
# The reverse channel and the complete cubic scattering matrix

The already proved spatial reflection involution transports the newly
evaluated cubic coefficient to the reverse channel. The remaining diagonal
entries vanish directly in the actual third integrand. Thus the whole third
coefficient is one explicit antisymmetric matrix.
-/

open Complex Matrix MeasureTheory Filter Topology Asymptotics
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem rawReverseReflection_cubic_quotient_unevaluated (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℝ => rawScatteringMatrix q k 0 1/(k : ℂ)^(3 : ℕ))
      (𝓝[≠] 0) (𝓝 (rawScatteringCubicCoefficient q 0 1)) := by
  have hc : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) := by fun_prop
  have hh := (hc.tendsto (rawScatteringCubicCoefficient q)).comp
    (rawScatteringMatrix_cubic_quotient_tendsto q)
  change Tendsto (fun k : ℝ =>
    (((k : ℂ)^(3 : ℕ))⁻¹ • (rawScatteringMatrix q k-1-(k : ℂ)^(2 : ℕ) • rawScatteringQuadraticCoefficient q)) 0 1)
    (𝓝[≠] 0) (𝓝 (rawScatteringCubicCoefficient q 0 1)) at hh
  simpa only [Matrix.smul_apply,Matrix.sub_apply,Matrix.one_apply_ne (by omega : (0 : Fin 2) ≠ 1),
    rawScatteringQuadraticCoefficient_upper,smul_zero,sub_zero,smul_eq_mul,mul_zero,zero_mul,
    div_eq_mul_inv,mul_comm] using hh

/-- The reverse reflection cubic coefficient has the exact opposite sign. -/
theorem rawScatteringCubicCoefficient_upper (q : SchwartzMap ℝ ℂ) :
    rawScatteringCubicCoefficient q 0 1 = -2*compatibilityMoment q := by
  have hp : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 :=
    nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx)
  have hh := ((rawReverseReflection_cubic_quotient_unevaluated q).mono_left hp).comp
    Real.tendsto_exp_atBot_nhdsGT
  change Tendsto (fun κ : ℝ => rawScatteringMatrix q (Real.exp κ) 0 1/(Real.exp κ : ℂ)^(3 : ℕ))
    atBot (𝓝 (rawScatteringCubicCoefficient q 0 1)) at hh
  have he : (fun κ : ℝ => rawScatteringMatrix q (Real.exp κ) 0 1/(Real.exp κ : ℂ)^(3 : ℕ)) =
      fun κ => -(reflectionAmplitude q κ/(Real.exp κ : ℂ)^(3 : ℕ)) := by
    funext κ
    rw [rawScatteringMatrix_exp_eq]
    change reverseReflectionAmplitude q κ/(Real.exp κ : ℂ)^(3 : ℕ) = _
    rw [reverseReflectionAmplitude_eq_neg,neg_div]
  rw [he] at hh
  have hz := tendsto_nhds_unique hh (reflectionAmplitude_cubic_quotient_tendsto q).neg
  simpa only [neg_mul] using hz

/-- Both actual diagonal third integrands vanish at zero frequency. -/
theorem rawThirdIntegrand_zero_diagonal (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (rawThirdIntegrand q 0 (1,0) x).1 = 0 ∧ (rawThirdIntegrand q 0 (0,1) x).2 = 0 := by
  unfold rawThirdIntegrand
  simp only [rawSecondSlope_zero_eq,rawInteractionSolution_zero_frequency,
    rawDividedOperator_apply,rawCubicOperator_zero_apply,rawSecondPrimitive,
    Prod.fst_add,Prod.snd_add,mul_zero,add_zero,and_self]

theorem rawCubicEndpointMatrix_zero_diagonal (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawCubicEndpointMatrix q 0 left 0 0 = 0 ∧ rawCubicEndpointMatrix q 0 left 1 1 = 0 := by
  have hi := (rawOrientedThirdIntegrand_integrable q 0 (1,0) left).integrableOn (s := Set.Ioi 0)
  have hj := (rawOrientedThirdIntegrand_integrable q 0 (0,1) left).integrableOn (s := Set.Ioi 0)
  change (∫ x in Set.Ioi (0 : ℝ), rawOrientedThirdIntegrand q 0 (1,0) left x).1 = 0 ∧
    (∫ x in Set.Ioi (0 : ℝ), rawOrientedThirdIntegrand q 0 (0,1) left x).2 = 0
  rw [fst_integral hi,snd_integral hj]
  cases left <;> simp only [rawOrientedThirdIntegrand,Bool.false_eq_true,↓reduceIte,Prod.fst_neg,Prod.snd_neg,
    (rawThirdIntegrand_zero_diagonal q _).1,(rawThirdIntegrand_zero_diagonal q _).2,
    neg_zero,integral_zero,and_self]

/-- The full actual third-order coefficient is determined by one compatibility moment. -/
theorem rawScatteringCubicCoefficient_eq (q : SchwartzMap ℝ ℂ) :
    rawScatteringCubicCoefficient q = !![0,-2*compatibilityMoment q;2*compatibilityMoment q,0] := by
  have hd (i : Fin 2) : rawScatteringCubicCoefficient q i i = 0 := by
    unfold rawScatteringCubicCoefficient
    rw [rawQuadraticEndpointMatrix_eq,rawQuadraticEndpointMatrix_eq]
    fin_cases i <;>
      simp [rawFirstCoefficientMatrix,Matrix.adjugate_fin_two,
        (rawCubicEndpointMatrix_zero_diagonal q false).1,(rawCubicEndpointMatrix_zero_diagonal q false).2,
        (rawCubicEndpointMatrix_zero_diagonal q true).1,(rawCubicEndpointMatrix_zero_diagonal q true).2]
  ext i j
  fin_cases i <;> fin_cases j
  · exact hd 0
  · exact rawScatteringCubicCoefficient_upper q
  · exact rawScatteringCubicCoefficient_lower q
  · exact hd 1

/-- The reverse channel shares the same exact compatibility locus. -/
theorem rawReverseReflection_cubic_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℝ => rawScatteringMatrix q k 0 1/(k : ℂ)^(3 : ℕ))
      (𝓝[≠] 0) (𝓝 (-2*compatibilityMoment q)) := by
  simpa only [rawScatteringCubicCoefficient_upper] using rawReverseReflection_cubic_quotient_unevaluated q

theorem reverseReflectionAmplitude_cubic_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun κ : ℝ => reverseReflectionAmplitude q κ/(Real.exp κ : ℂ)^(3 : ℕ))
      atBot (𝓝 (-2*compatibilityMoment q)) := by
  have he : (fun κ : ℝ => reverseReflectionAmplitude q κ/(Real.exp κ : ℂ)^(3 : ℕ)) =
      fun κ => -(reflectionAmplitude q κ/(Real.exp κ : ℂ)^(3 : ℕ)) := by
    funext κ
    rw [reverseReflectionAmplitude_eq_neg,neg_div]
  rw [he]
  simpa only [neg_mul] using (reflectionAmplitude_cubic_quotient_tendsto q).neg

/-- The reverse spatial channel has the same unconditional cubic bound. -/
theorem rawReverseReflection_isBigO_cubic (q : SchwartzMap ℝ ℂ) :
    (fun k : ℝ => rawScatteringMatrix q k 0 1) =O[𝓝[≠] 0] fun k => (k : ℂ)^(3 : ℕ) := by
  refine isBigO_of_div_tendsto_nhds ?_ _ (rawReverseReflection_cubic_quotient_tendsto q)
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact fun h => (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hk) h).elim

/-- Both reflection channels improve beyond cubic order on exactly the same initial-data locus. -/
theorem rawReverseReflection_isLittleO_cubic_iff (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix q k 0 1) =o[𝓝[≠] 0] fun k => (k : ℂ)^(3 : ℕ)) ↔
      compatibilityMoment q = 0 := by
  constructor
  · intro h
    have hz := tendsto_nhds_unique (rawReverseReflection_cubic_quotient_tendsto q) h.tendsto_div_nhds_zero
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h
    apply (isLittleO_iff_tendsto' ?_).mpr
    · simpa only [h,mul_zero] using rawReverseReflection_cubic_quotient_tendsto q
    · filter_upwards [self_mem_nhdsWithin] with k hk
      exact fun he => (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hk) he).elim

/-- The original reverse amplitude fails fifth-order decay for the same explicit small Gaussian. -/
theorem reverseReflectionAmplitude_globalSmallGaussian_not_isBigO_fifth (a : ℝ) :
    ¬ ((fun κ : ℝ => reverseReflectionAmplitude (globalSmallScatteringPotential (compatibilityGaussian a)) κ)
      =O[atBot] fun κ => (Real.exp κ : ℂ)^(5 : ℕ)) := by
  have he : (fun κ : ℝ => reverseReflectionAmplitude (globalSmallScatteringPotential (compatibilityGaussian a)) κ) =
      fun κ => -reflectionAmplitude (globalSmallScatteringPotential (compatibilityGaussian a)) κ := by
    funext κ
    exact reverseReflectionAmplitude_eq_neg _ κ
  rw [he,isBigO_neg_left]
  exact reflectionAmplitude_globalSmallGaussian_not_isBigO_fifth a

end
end GaloisForLFunctions.HTGeometry.FokasLenells
