import GaloisForLFunctions.HTGeometry.FokasLenellsRawReflectionFifth

/-!
# Scaling and reflection classification of fifth-order scattering data

The exact fifth-order criterion turns the previously proved linear-cubic
moment law into a classification of admissible amplitudes. Stability under
every amplitude scaling is equivalent to separate vanishing of mass and
parity coupling. The same stronger condition governs simultaneous validity
before and after the corpus's explicit global smallness normalization.
-/

open Complex Matrix MeasureTheory Filter Topology Asymptotics
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The admissible amplitude scales obey an exact quadratic balance, apart from the zero profile. -/
theorem rawReflection_scaling_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    ((fun k : ℝ => rawScatteringMatrix (c • q) k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ↔
      c = 0 ∨ (∫ x : ℝ, q x) = I*c^2*parityCoupling q := by
  rw [rawReflection_isBigO_fifth_iff,compatibilityMoment_smul]
  have he : c*(∫ x : ℝ, q x)-I*c^3*parityCoupling q =
      c*((∫ x : ℝ, q x)-I*c^2*parityCoupling q) := by ring
  rw [he,mul_eq_zero,sub_eq_zero]

/-- Testing the original amplitude and its double already detects complete scaling stability. -/
theorem rawReflection_twice_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    (((fun k : ℝ => rawScatteringMatrix q k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ∧
      ((fun k : ℝ => rawScatteringMatrix ((2 : ℂ) • q) k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5)) ↔
      ((∫ x : ℝ, q x) = 0 ∧ parityCoupling q = 0) := by
  rw [rawReflection_isBigO_fifth_iff,rawReflection_isBigO_fifth_iff,
    compatibilityMoment_smul,compatibilityMoment_parity_decomposition]
  constructor
  · rintro ⟨h1,h2⟩
    have hz : (6*I)*parityCoupling q = 0 := by linear_combination 2*h1-h2
    have hp : parityCoupling q = 0 :=
      (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) I_ne_zero)
    exact ⟨by simpa only [hp,mul_zero,sub_zero] using h1,hp⟩
  · rintro ⟨hm,hp⟩
    simp [hm,hp]

/-- Fifth-order reflection survives every complex amplitude scaling exactly on two separate moment kernels. -/
theorem rawReflection_all_scalings_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    (∀ c : ℂ, (fun k : ℝ => rawScatteringMatrix (c • q) k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ↔
      ((∫ x : ℝ, q x) = 0 ∧ parityCoupling q = 0) := by
  constructor
  · intro h
    exact (rawReflection_twice_isBigO_fifth_iff q).mp ⟨by simpa only [one_smul] using h 1,h 2⟩
  · rintro ⟨hm,hp⟩ c
    rw [rawReflection_scaling_isBigO_fifth_iff]
    exact Or.inr (by simp [hm,hp])

/-- Scaling stability is equivalent to compatibility for both the initial profile and its spatial reflection. -/
theorem rawReflection_all_scalings_iff_reflected_profile (q : SchwartzMap ℝ ℂ) :
    (∀ c : ℂ, (fun k : ℝ => rawScatteringMatrix (c • q) k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ↔
      (((fun k : ℝ => rawScatteringMatrix q k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ∧
       ((fun k : ℝ => rawScatteringMatrix (RHTower.negSchwartz' q) k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5)) := by
  rw [rawReflection_all_scalings_isBigO_fifth_iff,rawReflection_isBigO_fifth_iff,
    rawReflection_isBigO_fifth_iff,compatibilityMoment_both_zero_iff]

theorem globalScatteringScale_lt_one (q : SchwartzMap ℝ ℂ) : globalScatteringScale q < 1 := by
  let m := effectiveControlMass (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))
  have hm : 0 ≤ m := effectiveControlMass_nonneg _ _ _
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by positivity)
  change (64*(1+m)*Real.exp 1)⁻¹ < 1
  apply inv_lt_one_of_one_lt₀
  have hh : 64*(1+m) ≤ 64*(1+m)*Real.exp 1 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (show 0 ≤ 64*(1+m) by positivity)
  nlinarith

/-- Global smallness normalization changes the exact compatibility balance by the square of its scale. -/
theorem rawReflection_globalSmall_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    ((fun k : ℝ => rawScatteringMatrix (globalSmallScatteringPotential q) k 1 0)
      =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ↔
      (∫ x : ℝ, q x) = I*(globalScatteringScale q : ℂ)^2*parityCoupling q := by
  rw [globalSmallScatteringPotential,rawReflection_scaling_isBigO_fifth_iff]
  have hc : (globalScatteringScale q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (globalScatteringScale_pos q))
  simp only [hc,false_or]

/-- Compatibility before and after strict smallness normalization requires separate mass and coupling cancellation. -/
theorem rawReflection_and_globalSmall_isBigO_fifth_iff (q : SchwartzMap ℝ ℂ) :
    (((fun k : ℝ => rawScatteringMatrix q k 1 0) =O[𝓝[≠] 0] fun k => (k : ℂ)^5) ∧
      ((fun k : ℝ => rawScatteringMatrix (globalSmallScatteringPotential q) k 1 0)
        =O[𝓝[≠] 0] fun k => (k : ℂ)^5)) ↔
      ((∫ x : ℝ, q x) = 0 ∧ parityCoupling q = 0) := by
  rw [rawReflection_isBigO_fifth_iff_parity_balance,rawReflection_globalSmall_isBigO_fifth_iff]
  constructor
  · rintro ⟨h1,h2⟩
    have hs : (globalScatteringScale q)^2 < 1 := by
      have hh := mul_lt_mul_of_pos_right (globalScatteringScale_lt_one q) (globalScatteringScale_pos q)
      exact (show (globalScatteringScale q)^2 < globalScatteringScale q by
        simpa only [pow_two,one_mul] using hh).trans (globalScatteringScale_lt_one q)
    have hc : (globalScatteringScale q : ℂ)^2 ≠ 1 := by exact_mod_cast ne_of_lt hs
    have hz : (I*(1-(globalScatteringScale q : ℂ)^2))*parityCoupling q = 0 := by
      linear_combination h2-h1
    have hp : parityCoupling q = 0 := (mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero I_ne_zero (sub_ne_zero.mpr (Ne.symm hc)))
    exact ⟨by simpa only [hp,mul_zero] using h1,hp⟩
  · rintro ⟨hm,hp⟩
    simp [hm,hp]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
