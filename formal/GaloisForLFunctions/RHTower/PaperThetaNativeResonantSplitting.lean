import GaloisForLFunctions.RHTower.PaperThetaNativeScalarReduction

/-! # Exact resonant solving on the whole original uniform domain

The constructed global inverse supplies every resonant solution, its unique
zero-trace representative, and the literal one-dimensional source defect.
-/

noncomputable section
open Complex Set
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint

abbrev NativeResonantParameter := {z : ℂ // z = 0 ∨ XiC z = 0}

def nativeResonantParticular (z : ℂ) (g : NativeContinuousSpace) : NativeContinuousSpace :=
  (nativeGrushinInverse z (g,0)).1

def nativeResonantVector (z : ℂ) : NativeContinuousSpace := nativeGrushinTraceResponse z 1

theorem nativeResonantVector_trace (z : ℂ) :
    boundedResolventTrace nativeCompactParameter (nativeResonantVector z) = 1 :=
  congrArg Prod.snd (nativeGrushinInverse_right z (0,1))

theorem nativeResonantVector_ne_zero (z : ℂ) : nativeResonantVector z ≠ 0 := by
  intro h
  have ht := nativeResonantVector_trace z
  rw [h, map_zero] at ht
  exact zero_ne_one ht

theorem nativeResonantParticular_trace (z : ℂ) (g : NativeContinuousSpace) :
    boundedResolventTrace nativeCompactParameter (nativeResonantParticular z g) = 0 :=
  congrArg Prod.snd (nativeGrushinInverse_right z (g,0))

theorem nativeResonantParticular_equation (z : ℂ) (g : NativeContinuousSpace) :
    nativePencil z (nativeResonantParticular z g) =
      g-(boundedThetaMomentCLM z g/(nativeCounterMass : ℂ)) • nativeCounterSource z := by
  have h := congrArg Prod.fst (nativeGrushinInverse_right z (g,0))
  change nativePencil z (nativeResonantParticular z g)+
    (nativeGrushinInverse z (g,0)).2 • nativeCounterSource z = g at h
  rw [nativeGrushinInverse_scalar] at h
  simpa only [nativeBoundaryCorrection, mul_zero, zero_mul, add_zero] using eq_sub_of_add_eq h

theorem nativeResonantVector_equation (z : NativeResonantParameter) :
    nativePencil z (nativeResonantVector z) = 0 := by
  have h := congrArg Prod.fst (nativeGrushinInverse_right z (0,1))
  change nativePencil z (nativeResonantVector z)+
    (nativeGrushinInverse z (0,1)).2 • nativeCounterSource z = 0 at h
  rw [nativeGrushinInverse_scalar_zero,
    (nativeEffectiveScalar_zero_iff z).mpr z.property, zero_mul, zero_smul, add_zero] at h
  exact h

/-- Actual range obstruction together with every solution, not only an existence criterion. -/
theorem nativeResonant_full_solution (z : NativeResonantParameter)
    (g v : NativeContinuousSpace) :
    nativePencil z v = g ↔
      boundedThetaMomentCLM z g = 0 ∧
      v = nativeResonantParticular z g+
        boundedResolventTrace nativeCompactParameter v • nativeResonantVector z := by
  constructor
  · intro he
    have hb : nativeGrushinBlock z (v,0) =
        (g,boundedResolventTrace nativeCompactParameter v) := by
      rw [nativeGrushinBlock_apply,he,zero_smul,add_zero]
    have hi := nativeGrushinInverse_left z (v,0)
    rw [hb] at hi
    have hs := congrArg Prod.snd hi
    rw [nativeGrushinInverse_scalar] at hs
    have hc : boundedThetaMomentCLM z g = 0 := by
      have hz : (z : ℂ)*flatConnection z = 0 := by
        have h := (nativeEffectiveScalar_zero_iff z).mpr z.property
        exact (div_eq_zero_iff.mp h).resolve_right
          (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne')
      have hzt : (z : ℂ)*boundedResolventTrace nativeCompactParameter v*flatConnection z = 0 := by
        linear_combination boundedResolventTrace nativeCompactParameter v*hz
      change (boundedThetaMomentCLM z g+
        (z : ℂ)*boundedResolventTrace nativeCompactParameter v*flatConnection z)/
          (nativeCounterMass : ℂ) = 0 at hs
      rw [hzt, add_zero] at hs
      exact (div_eq_zero_iff.mp hs).resolve_right
        (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne')
    refine ⟨hc, ?_⟩
    have hp : (g,boundedResolventTrace nativeCompactParameter v) =
        (g,0)+boundedResolventTrace nativeCompactParameter v • ((0,1) : NativeGrushinSpace) := by
      simp
    rw [hp, map_add, map_smul] at hi
    exact (congrArg Prod.fst hi).symm
  · rintro ⟨hm,hv⟩
    rw [hv, map_add, map_smul, nativeResonantVector_equation, smul_zero, add_zero,
      nativeResonantParticular_equation, hm, zero_div, zero_smul, sub_zero]

/-- Every compatible resonant forcing has a specified zero-trace solution. -/
theorem nativeResonant_range (z : NativeResonantParameter) :
    LinearMap.range (nativePencil z).toLinearMap = LinearMap.ker (boundedThetaMomentCLM z).toLinearMap := by
  ext g
  constructor
  · rintro ⟨v,hv⟩
    exact (nativeResonant_full_solution z g v).mp hv |>.1
  · intro hg
    refine ⟨nativeResonantParticular z g, ?_⟩
    change nativePencil z (nativeResonantParticular z g) = g
    rw [nativeResonantParticular_equation, show boundedThetaMomentCLM z g = 0 from hg,
      zero_div, zero_smul, sub_zero]

/-- There are no unobserved eigenfunctions on the whole original uniform space. -/
theorem nativeResonant_kernel (z : NativeResonantParameter) :
    LinearMap.ker (nativePencil z).toLinearMap = ℂ ∙ nativeResonantVector z := by
  apply le_antisymm
  · intro v hv
    have h := ((nativeResonant_full_solution z 0 v).mp hv).2
    have hzero : nativeResonantParticular z 0 = 0 := by
      change (nativeGrushinInverse z (0 : NativeGrushinSpace)).1 = 0
      rw [map_zero]
      rfl
    rw [hzero, zero_add] at h
    exact Submodule.mem_span_singleton.mpr ⟨boundedResolventTrace nativeCompactParameter v,h.symm⟩
  · apply Submodule.span_le.mpr
    exact Set.singleton_subset_iff.mpr (nativeResonantVector_equation z)

end RHTower.PaperThetaEndpoint
