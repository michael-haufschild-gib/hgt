import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearPullback
import GaloisForLFunctions.RHTower.Deninger.DeningerSchwartzNuclear
import GaloisForLFunctions.RHTower.Deninger.DeningerSecondaryCollarDefect

/-!
# The weighted oscillator family of the Meyer source is nuclear

Multiplication by `e^{ct}` is an automorphism of the source, with inverse multiplication by
`e^{-ct}`.  The oscillator seminorms of the Schwartz space restrict to a nuclear family on the
source, and precomposing with those automorphisms keeps it nuclear, because nuclearity pulls back
along a surjection.

* `deningerExpMulLM` : multiplication by `e^{ct}` as a linear automorphism of `H_-`.
* `deningerMeyerOscFamily` : `R(k,m)(h) = Q_m(e^{kt}h)`.
* `deningerMeyerOsc_isNuclearSpaceC` : **the weighted oscillator family is nuclear.**
-/

namespace RHTower

open SchwartzMap Function GaloisForLFunctions

noncomputable section

/-- Multiplication by `e^{ct}` as a linear map of the source. -/
def deningerExpMulLM (c : ℝ) : DeningerExpSchwartz →ₗ[ℂ] DeningerExpSchwartz where
  toFun := deningerExpMul c
  map_add' h g := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    rw [deningerExpMul_apply]
    show ((Real.exp (c * t) : ℝ) : ℂ)
        * (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t + ((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t)
      = ((deningerExpMul c h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
        + ((deningerExpMul c g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
    rw [deningerExpMul_apply, deningerExpMul_apply]
    ring
  map_smul' a h := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    rw [deningerExpMul_apply]
    show ((Real.exp (c * t) : ℝ) : ℂ) * (a * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t)
      = a * ((deningerExpMul c h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
    rw [deningerExpMul_apply]
    ring

@[simp]
theorem deningerExpMulLM_apply (c : ℝ) (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerExpMulLM c h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((Real.exp (c * t) : ℝ) : ℂ) * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t :=
  deningerExpMul_apply c h t

/-- **Multiplication by `e^{ct}` is surjective on the source**, with inverse multiplication by
`e^{-ct}`. -/
theorem deningerExpMulLM_surjective (c : ℝ) : Surjective (deningerExpMulLM c) := by
  intro h
  refine ⟨deningerExpMulLM (-c) h, ?_⟩
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerExpMulLM_apply, deningerExpMulLM_apply, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add]
  have hzero : c * t + -c * t = 0 := by ring
  rw [hzero, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- The oscillator seminorms restricted to the source. -/
def deningerSourceOscSeminorm (m : ℕ) : Seminorm ℂ DeningerExpSchwartz :=
  deningerRestrictSeminorm DeningerExpSchwartz (shiftedSeminorm m)

/-- **The restricted oscillator family of the source is nuclear.** -/
theorem deningerSourceOsc_isNuclearSpaceC :
    DeningerIsNuclearSpaceC deningerSourceOscSeminorm :=
  deningerIsNuclearSpaceC_subspace (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ)
    DeningerExpSchwartz deningerIsNuclearSpace_shiftedSeminormFamily

/-- The weighted oscillator family `R(k,m)(h) = Q_m(e^{kt}h)`. -/
def deningerMeyerOscFamily : SeminormFamily ℂ DeningerExpSchwartz (ℤ × ℕ) :=
  fun km => (deningerSourceOscSeminorm km.2).comp (deningerExpMulLM (km.1 : ℝ))

theorem deningerMeyerOscFamily_apply (k : ℤ) (m : ℕ) (h : DeningerExpSchwartz) :
    deningerMeyerOscFamily (k, m) h
      = deningerSourceOscSeminorm m (deningerExpMulLM (k : ℝ) h) := rfl

/-- **The weighted oscillator family of the source is nuclear.**  For each weight the family is the
pullback of the restricted oscillator family along an automorphism, and nuclearity pulls back along
a surjection. -/
theorem deningerMeyerOsc_isNuclearSpaceC :
    DeningerIsNuclearSpaceC deningerMeyerOscFamily := by
  rintro ⟨k, m⟩
  obtain ⟨m', C, hle, hnuc⟩ :=
    deningerIsNuclearSpaceC_comp_surjective deningerSourceOscSeminorm
      (deningerExpMulLM (k : ℝ)) (deningerExpMulLM_surjective (k : ℝ))
      deningerSourceOsc_isNuclearSpaceC m
  exact ⟨(k, m'), C, hle, hnuc⟩

end

end RHTower
