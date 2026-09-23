import GaloisForLFunctions.HTGeometry.FokasLenellsRawCubicMoment

/-!
# Sharp cubic reflection and the fifth-order obstruction

The spatial scattering problem always has cubic reflection. Its improvement
to little-o of the cubic scale is equivalent to one exact compatibility
moment. The normalized Gaussian, including the explicit small-data family,
violates the fifth-order assertion of Proposition 3.8 when only spatial
initial-data assumptions are imposed.
-/

open Complex Matrix MeasureTheory Filter Topology Asymptotics
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem raw_cubic_denominator_nonzero :
    ∀ᶠ k : ℝ in 𝓝[≠] 0, (k : ℂ)^(3 : ℕ) ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hk)

/-- The unconditional spatial estimate is cubic at the origin. -/
theorem rawReflection_isBigO_cubic (q : SchwartzMap ℝ ℂ) :
    (fun k : ℝ => rawScatteringMatrix q k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^(3 : ℕ) := by
  refine isBigO_of_div_tendsto_nhds ?_ _ (rawReflection_cubic_quotient_tendsto q)
  filter_upwards [raw_cubic_denominator_nonzero] with k hk
  exact fun h => (hk h).elim

/-- Cancellation at the cubic scale holds precisely on the compatibility locus. -/
theorem rawReflection_isLittleO_cubic_iff (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix q k 1 0) =o[𝓝[≠] 0] fun k => (k : ℂ)^(3 : ℕ)) ↔
      compatibilityMoment q = 0 := by
  constructor
  · intro h
    have hz := tendsto_nhds_unique (rawReflection_cubic_quotient_tendsto q) h.tendsto_div_nhds_zero
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h
    apply (isLittleO_iff_tendsto' ?_).mpr
    · simpa only [h,mul_zero] using rawReflection_cubic_quotient_tendsto q
    · filter_upwards [raw_cubic_denominator_nonzero] with k hk
      exact fun he => (hk he).elim

private theorem raw_fifth_isLittleO_cubic :
    (fun k : ℝ => (k : ℂ)^(5 : ℕ)) =o[𝓝[≠] 0] fun k => (k : ℂ)^(3 : ℕ) := by
  have hc : Tendsto (fun k : ℝ => (k : ℂ)) (𝓝[≠] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  exact (isLittleO_pow_pow (𝕜 := ℂ) (by omega : 3 < 5)).comp_tendsto hc

/-- Fifth-order scattering requires, as an exact necessary condition, the compatibility moment. -/
private theorem rawReflection_fifth_order_requires_compatibility (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix q k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^(5 : ℕ)) →
      compatibilityMoment q = 0 := by
  intro h
  exact (rawReflection_isLittleO_cubic_iff q).mp (h.trans_isLittleO raw_fifth_isLittleO_cubic)

/-- A rapidly decreasing Gaussian is a closed counterexample to unconditional fifth-order spatial scattering. -/
theorem rawReflection_gaussian_not_isBigO_fifth (a : ℝ) :
    ¬ ((fun k : ℝ => rawScatteringMatrix (compatibilityGaussian a) k 1 0) =O[𝓝[≠] 0]
      fun k => (k : ℂ)^(5 : ℕ)) := by
  intro h
  have hz := rawReflection_fifth_order_requires_compatibility (compatibilityGaussian a) h
  rw [compatibilityMoment_gaussian] at hz
  exact one_ne_zero hz

/-- The counterexample persists under the previously certified global smallness normalization. -/
theorem rawReflection_globalSmallGaussian_not_isBigO_fifth (a : ℝ) :
    ¬ ((fun k : ℝ => rawScatteringMatrix (globalSmallScatteringPotential (compatibilityGaussian a)) k 1 0)
      =O[𝓝[≠] 0] fun k => (k : ℂ)^(5 : ℕ)) := by
  intro h
  exact compatibilityMoment_globalSmallGaussian_ne_zero a
    (rawReflection_fifth_order_requires_compatibility _ h)

/-- The already constructed logarithmic-frequency reflection amplitude has the same exact cubic limit. -/
theorem reflectionAmplitude_cubic_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun κ : ℝ => reflectionAmplitude q κ/(Real.exp κ : ℂ)^(3 : ℕ))
      atBot (𝓝 (2*compatibilityMoment q)) := by
  have hp : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 :=
    nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx)
  have hh := ((rawReflection_cubic_quotient_tendsto q).mono_left hp).comp
    Real.tendsto_exp_atBot_nhdsGT
  change Tendsto (fun κ : ℝ => rawScatteringMatrix q (Real.exp κ) 1 0/(Real.exp κ : ℂ)^(3 : ℕ))
    atBot (𝓝 (2*compatibilityMoment q)) at hh
  simpa only [rawScatteringMatrix_exp_eq,reflectionAmplitude] using hh

/-- The original small-data scattering amplitude also fails the paper's fifth-order estimate. -/
theorem reflectionAmplitude_globalSmallGaussian_not_isBigO_fifth (a : ℝ) :
    ¬ ((fun κ : ℝ => reflectionAmplitude (globalSmallScatteringPotential (compatibilityGaussian a)) κ)
      =O[atBot] fun κ => (Real.exp κ : ℂ)^(5 : ℕ)) := by
  intro h
  have hc : Tendsto (fun κ : ℝ => (Real.exp κ : ℂ)) atBot (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_atBot
  have hp := (isLittleO_pow_pow (𝕜 := ℂ) (by omega : 3 < 5)).comp_tendsto hc
  have hz := tendsto_nhds_unique
    (reflectionAmplitude_cubic_quotient_tendsto (globalSmallScatteringPotential (compatibilityGaussian a)))
    (h.trans_isLittleO hp).tendsto_div_nhds_zero
  exact compatibilityMoment_globalSmallGaussian_ne_zero a
    ((mul_eq_zero.mp hz).resolve_left (by norm_num))

end
end GaloisForLFunctions.HTGeometry.FokasLenells
