import GaloisForLFunctions.HTGeometry.FokasLenellsRawFifthScaling
import GaloisForLFunctions.HTGeometry.FokasLenellsScatteringContinuity

/-!
# The actual weighted reflection profile at the spectral origin

On z>0 this is z^-2 lambda^-1 b(lambda), lambda=sqrt(z), from Proposition
3.9 of arXiv:2607.19649. The actual fifth-order expansion splits it into
one explicit reciprocal pole and a remainder with a proved finite limit.
The displayed formula totalizes the profile to zero on z<=0.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def originWeightedReflection (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℂ :=
  reflectionAmplitude q (Real.log (Real.sqrt z))/(Real.sqrt z : ℂ)^5

theorem originWeightedReflection_measurable (q : SchwartzMap ℝ ℂ) : Measurable (originWeightedReflection q) := by
  have hS := continuous_scatteringMatrix q
  have hB : Continuous (reflectionAmplitude q) := by
    unfold reflectionAmplitude
    fun_prop
  have hN := hB.measurable.comp (Real.measurable_log.comp Real.continuous_sqrt.measurable)
  have hD := (Complex.continuous_ofReal.measurable.comp Real.continuous_sqrt.measurable).pow_const 5
  exact hN.div hD

private theorem originWeightedReflection_raw (q : SchwartzMap ℝ ℂ) (z : ℝ) (hz : 0 < z) :
    originWeightedReflection q z = rawScatteringMatrix q (Real.sqrt z) 1 0/(Real.sqrt z : ℂ)^5 := by
  have hh := rawScatteringMatrix_exp_eq q (Real.log (Real.sqrt z))
  rw [Real.exp_log (Real.sqrt_pos.mpr hz)] at hh
  rw [hh]
  rfl

/-- On the positive ray this is exactly the paper's weighted original scattering amplitude. -/
theorem originWeightedReflection_exp (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    originWeightedReflection q ((Real.exp κ)^2) = reflectionAmplitude q κ/(Real.exp κ : ℂ)^5 := by
  simp only [originWeightedReflection,Real.sqrt_sq_eq_abs,abs_of_pos (Real.exp_pos κ),Real.log_exp]

private theorem originWeightedReflection_decomposition (q : SchwartzMap ℝ ℂ) (z : ℝ) (hz : 0 < z) :
    originWeightedReflection q z = 2*compatibilityMoment q/(z : ℂ)+
      rawScatteringFifthRemainder q (Real.sqrt z) 1 0 := by
  have hsqrt : (Real.sqrt z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hz))
  have hs : (Real.sqrt z : ℂ)^2 = (z : ℂ) := by exact_mod_cast Real.sq_sqrt hz.le
  rw [originWeightedReflection_raw q z hz,rawReflection_fifth_factor,← hs]
  field_simp

private theorem origin_fifth_remainder_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => rawScatteringFifthRemainder q (Real.sqrt z) 1 0)
      (𝓝[>] 0) (𝓝 (rawScatteringFifthCoefficient q 1 0)) := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) := by fun_prop
  have hh := (hc.tendsto (rawScatteringFifthCoefficient q)).comp
    ((rawScatteringFifthRemainder_tendsto_zero q).comp hs)
  exact hh

/-- Subtracting the explicit compatibility pole leaves a finite actual fifth-coefficient limit. -/
theorem originWeightedReflection_sub_pole_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => originWeightedReflection q z-2*compatibilityMoment q/(z : ℂ))
      (𝓝[>] 0) (𝓝 (rawScatteringFifthCoefficient q 1 0)) := by
  apply (origin_fifth_remainder_tendsto q).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [originWeightedReflection_decomposition q z hz,add_sub_cancel_left]

/-- The weighted profile has exactly the reciprocal-pole residue predicted by the cubic scattering coefficient. -/
theorem originWeightedReflection_mul_coordinate_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => (z : ℂ)*originWeightedReflection q z)
      (𝓝[>] 0) (𝓝 (2*compatibilityMoment q)) := by
  have hz : Tendsto (fun z : ℝ => (z : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun _ : ℝ => 2*compatibilityMoment q) (𝓝[>] 0) (𝓝 (2*compatibilityMoment q)) := tendsto_const_nhds
  have hh := hc.add (hz.mul (origin_fifth_remainder_tendsto q))
  simp only [zero_mul,add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [originWeightedReflection_decomposition q z hz]
  field_simp

/-- The weighted profile has a finite right limit exactly on the compatibility locus. -/
theorem originWeightedReflection_finite_limit_iff (q : SchwartzMap ℝ ℂ) :
    (∃ c : ℂ, Tendsto (originWeightedReflection q) (𝓝[>] 0) (𝓝 c)) ↔ compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨c,hc⟩
    have hz : Tendsto (fun z : ℝ => (z : ℂ)) (𝓝[>] 0) (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hh := hz.mul hc
    simp only [zero_mul] at hh
    have he := tendsto_nhds_unique (originWeightedReflection_mul_coordinate_tendsto q) hh
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  · intro hm
    refine ⟨rawScatteringFifthCoefficient q 1 0,?_⟩
    simpa only [hm,mul_zero,zero_div,sub_zero] using originWeightedReflection_sub_pole_tendsto q

end
end GaloisForLFunctions.HTGeometry.FokasLenells
