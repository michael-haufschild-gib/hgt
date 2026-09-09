import GaloisForLFunctions.HTGeometry.FokasLenellsRawFourthDiagonal
import GaloisForLFunctions.HTGeometry.FokasLenellsParityMoment

/-!
# Fifth-order reflection is equivalent to the compatibility moment

This is the sharp spatial replacement for Proposition 3.8 of arXiv:2607.19649
on Schwartz data. Subtracting the explicit cubic moment always leaves a
controlled fifth-order remainder. Thus both reflection channels have
fifth-order decay exactly on the compatibility locus, with no PDE premise.
-/

open Complex Matrix MeasureTheory Filter Topology Asymptotics
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem fifth_denominator_nonzero :
    ∀ᶠ k : ℝ in 𝓝[≠] 0, (k : ℂ)^5 ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hk)

private theorem fifth_power_littleo_cubic :
    (fun k : ℝ => (k : ℂ)^5) =o[𝓝[≠] 0] fun k => (k : ℂ)^3 := by
  have hc : Tendsto (fun k : ℝ => (k : ℂ)) (𝓝[≠] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  exact (isLittleO_pow_pow (𝕜 := ℂ) (by omega : 3 < 5)).comp_tendsto hc

/-- Removing the exact cubic obstruction gives a convergent genuine fifth quotient. -/
theorem rawReflection_sub_cubic_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℝ => (rawScatteringMatrix q k 1 0-(k : ℂ)^3*(2*compatibilityMoment q))/(k : ℂ)^5)
      (𝓝[≠] 0) (𝓝 (rawScatteringFifthCoefficient q 1 0)) := by
  have hc : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) := by fun_prop
  have hr : Tendsto (rawScatteringFifthRemainder q) (𝓝[≠] (0 : ℝ)) (𝓝 (rawScatteringFifthCoefficient q)) :=
    (rawScatteringFifthRemainder_tendsto_zero q).mono_left nhdsWithin_le_nhds
  have hh := (hc.tendsto (rawScatteringFifthCoefficient q)).comp hr
  change Tendsto (fun k : ℝ => rawScatteringFifthRemainder q k 1 0)
    (𝓝[≠] 0) (𝓝 (rawScatteringFifthCoefficient q 1 0)) at hh
  apply hh.congr'
  filter_upwards [fifth_denominator_nonzero] with k hk
  rw [rawReflection_fifth_factor,add_sub_cancel_left,mul_div_cancel_left₀ _ hk]

/-- The cubic-subtracted reflection always has fifth-order spatial decay. -/
theorem rawReflection_sub_cubic_isBigO_fifth (q : SchwartzMap ℝ ℂ) :
    (fun k : ℝ => rawScatteringMatrix q k 1 0-(k : ℂ)^3*(2*compatibilityMoment q))
      =O[𝓝[≠] 0] fun k => (k : ℂ)^5 := by
  refine isBigO_of_div_tendsto_nhds ?_ _ (rawReflection_sub_cubic_quotient_tendsto q)
  filter_upwards [fifth_denominator_nonzero] with k hk
  exact fun h => (hk h).elim

/-- The fifth-order claim is exactly equivalent to the additional compatibility condition. -/
theorem rawReflection_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix q k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ↔
      compatibilityMoment q = 0 := by
  constructor
  · intro h
    exact (rawReflection_isLittleO_cubic_iff q).mp (h.trans_isLittleO fifth_power_littleo_cubic)
  · intro h
    simpa only [h,mul_zero,sub_zero] using rawReflection_sub_cubic_isBigO_fifth q

/-- Removing the exact cubic obstruction gives a convergent genuine fifth quotient. -/
theorem rawReverseReflection_sub_cubic_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℝ => (rawScatteringMatrix q k 0 1-(k : ℂ)^3*(-2*compatibilityMoment q))/(k : ℂ)^5)
      (𝓝[≠] 0) (𝓝 (rawScatteringFifthCoefficient q 0 1)) := by
  have hc : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) := by fun_prop
  have hr : Tendsto (rawScatteringFifthRemainder q) (𝓝[≠] (0 : ℝ)) (𝓝 (rawScatteringFifthCoefficient q)) :=
    (rawScatteringFifthRemainder_tendsto_zero q).mono_left nhdsWithin_le_nhds
  have hh := (hc.tendsto (rawScatteringFifthCoefficient q)).comp hr
  change Tendsto (fun k : ℝ => rawScatteringFifthRemainder q k 0 1)
    (𝓝[≠] 0) (𝓝 (rawScatteringFifthCoefficient q 0 1)) at hh
  apply hh.congr'
  filter_upwards [fifth_denominator_nonzero] with k hk
  rw [rawReverseReflection_fifth_factor,add_sub_cancel_left,mul_div_cancel_left₀ _ hk]

/-- The cubic-subtracted reflection always has fifth-order spatial decay. -/
theorem rawReverseReflection_sub_cubic_isBigO_fifth (q : SchwartzMap ℝ ℂ) :
    (fun k : ℝ => rawScatteringMatrix q k 0 1-(k : ℂ)^3*(-2*compatibilityMoment q))
      =O[𝓝[≠] 0] fun k => (k : ℂ)^5 := by
  refine isBigO_of_div_tendsto_nhds ?_ _ (rawReverseReflection_sub_cubic_quotient_tendsto q)
  filter_upwards [fifth_denominator_nonzero] with k hk
  exact fun h => (hk h).elim

/-- The fifth-order claim is exactly equivalent to the additional compatibility condition. -/
theorem rawReverseReflection_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix q k 0 1) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ↔
      compatibilityMoment q = 0 := by
  constructor
  · intro h
    exact (rawReverseReflection_isLittleO_cubic_iff q).mp (h.trans_isLittleO fifth_power_littleo_cubic)
  · intro h
    simpa only [h,mul_zero,sub_zero] using rawReverseReflection_sub_cubic_isBigO_fifth q

/-- Odd projected initial data satisfy both fifth-order reflection estimates unconditionally. -/
theorem rawReflections_oddInitialPart_isBigO_fifth (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix (oddInitialPart q) k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ∧
    ((fun k : ℝ => rawScatteringMatrix (oddInitialPart q) k 0 1) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) :=
  ⟨(rawReflection_isBigO_fifth_iff _).mpr (compatibilityMoment_oddInitialPart q),
   (rawReverseReflection_isBigO_fifth_iff _).mpr (compatibilityMoment_oddInitialPart q)⟩

/-- For even projected data, the sharp condition is precisely zero total mass. -/
theorem rawReflection_evenInitialPart_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix (evenInitialPart q) k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ↔
      (∫ x : ℝ, q x) = 0 := by
  rw [rawReflection_isBigO_fifth_iff,compatibilityMoment_evenInitialPart]

/-- An explicit full family of even compatible potentials comes from the existing Schwartz derivative operator. -/
theorem rawReflections_evenDerivative_isBigO_fifth (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix (evenInitialPart (SchwartzMap.derivCLM ℂ ℂ q)) k 1 0)
      =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ∧
    ((fun k : ℝ => rawScatteringMatrix (evenInitialPart (SchwartzMap.derivCLM ℂ ℂ q)) k 0 1)
      =O[𝓝[≠] 0] fun k => (k : ℂ)^5) := by
  have hm : compatibilityMoment (evenInitialPart (SchwartzMap.derivCLM ℂ ℂ q)) = 0 := by
    rw [compatibilityMoment_evenInitialPart]
    simpa only [SchwartzMap.derivCLM_apply] using RHTower.integral_deriv_schwartz_eq_zero q
  exact ⟨(rawReflection_isBigO_fifth_iff _).mpr hm,(rawReverseReflection_isBigO_fifth_iff _).mpr hm⟩

/-- General data balance their mass against the previously formalized even/odd interaction. -/
theorem rawReflection_isBigO_fifth_iff_parity_balance (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix q k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ↔
      (∫ x : ℝ, q x) = I*parityCoupling q := by
  rw [rawReflection_isBigO_fifth_iff,compatibilityMoment_zero_iff_parity_balance]

private theorem exp_tendsto_punctured_zero : Tendsto Real.exp atBot (𝓝[≠] (0 : ℝ)) := by
  have hp : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx)
  exact Real.tendsto_exp_atBot_nhdsGT.mono_right hp

/-- The exact same characterization holds for the original logarithmic-frequency scattering amplitude. -/
theorem reflectionAmplitude_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun κ : ℝ => reflectionAmplitude q κ) =O[atBot] fun κ => (Real.exp κ : ℂ)^5) ↔
      compatibilityMoment q = 0 := by
  constructor
  · intro h
    have hc : Tendsto (fun κ : ℝ => (Real.exp κ : ℂ)) atBot (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_atBot
    have hp := (isLittleO_pow_pow (𝕜 := ℂ) (by omega : 3 < 5)).comp_tendsto hc
    have hz := tendsto_nhds_unique (reflectionAmplitude_cubic_quotient_tendsto q)
      (h.trans_isLittleO hp).tendsto_div_nhds_zero
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h
    have hh := ((rawReflection_isBigO_fifth_iff q).mpr h).comp_tendsto exp_tendsto_punctured_zero
    simpa only [Function.comp_def,rawScatteringMatrix_exp_eq,reflectionAmplitude] using hh

/-- The exact same characterization holds for the original logarithmic-frequency scattering amplitude. -/
theorem reverseReflectionAmplitude_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun κ : ℝ => reverseReflectionAmplitude q κ) =O[atBot] fun κ => (Real.exp κ : ℂ)^5) ↔
      compatibilityMoment q = 0 := by
  constructor
  · intro h
    have hc : Tendsto (fun κ : ℝ => (Real.exp κ : ℂ)) atBot (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_atBot
    have hp := (isLittleO_pow_pow (𝕜 := ℂ) (by omega : 3 < 5)).comp_tendsto hc
    have hz := tendsto_nhds_unique (reverseReflectionAmplitude_cubic_quotient_tendsto q)
      (h.trans_isLittleO hp).tendsto_div_nhds_zero
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h
    have hh := ((rawReverseReflection_isBigO_fifth_iff q).mpr h).comp_tendsto exp_tendsto_punctured_zero
    simpa only [Function.comp_def,rawScatteringMatrix_exp_eq,reverseReflectionAmplitude] using hh

end
end GaloisForLFunctions.HTGeometry.FokasLenells
