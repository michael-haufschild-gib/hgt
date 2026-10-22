import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteBruhatProfiniteHaarTransport
import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteAdeleNonarchimedean
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Uniform profinite stabilizers of finite-adelic Bruhat functions

Compact support and additive local constancy imply more than pointwise
continuity in the profinite-unit parameter.  A support denominator confines the
function to one compact fractional-integral set, invariant under all profinite
units.  The tube lemma then turns one additive translation stabilizer into an
open multiplicative neighborhood of `1` that fixes the function globally.

This proves that right translation of a finite Bruhat function is genuinely
locally constant as a function of the profinite unit, which is the missing
uniformity needed by the full CCM strong class-space target.
-/

noncomputable section

open Filter Set Topology IsDedekindDomain
open scoped RestrictedProduct algebraMap

namespace GaloisForLFunctions
namespace RHTower

/-- Every finite Bruhat function is fixed globally by an open neighborhood of
the identity in the profinite-unit group. -/
theorem ccmRationalFiniteBruhat_exists_open_profiniteUnit_stabilizer
    (phi : CCMRationalFiniteBruhatSchwartz) :
    ∃ U : Set CCMRationalProfiniteUnit,
      IsOpen U ∧ 1 ∈ U ∧
        ∀ (u : CCMRationalProfiniteUnit), u ∈ U →
          ∀ x : CCMRationalFiniteAdele,
            phi.1 (x * (u.1 : CCMRationalFiniteAdele)) = phi.1 x := by
  obtain ⟨D, hD, hsupport⟩ :=
    ccmRationalFiniteBruhatMulRight_exists_positiveNatSupportDenominator
      phi (1 : CCMRationalFiniteAdeleˣ)
  obtain ⟨V, hV⟩ :=
    ccmRationalFiniteBruhat_exists_openAddSubgroup_stabilizer phi
  let qD := ccmRationalNatUnit D (Nat.ne_of_gt hD)
  let E := ccmRationalFiniteAdeleScalingEquiv qD
  let K : Set CCMRationalFiniteAdele :=
    E ⁻¹' ccmRationalIntegralFiniteAdeles
  have hKcompact : IsCompact K := by
    exact E.toHomeomorph.isCompact_preimage.mpr
      ccmRationalIntegralFiniteAdeles_isCompact
  have hsupportK : Function.support (phi.1 : CCMRationalFiniteAdele → ℂ) ⊆ K := by
    intro x hx
    have hxint := hsupport x (by simpa using hx)
    change E x ∈ ccmRationalIntegralFiniteAdeles
    change algebraMap ℚ CCMRationalFiniteAdele (D : ℚ) * x ∈
      ccmRationalIntegralFiniteAdeles
    rw [show algebraMap ℚ CCMRationalFiniteAdele (D : ℚ) =
        algebraMap ℕ CCMRationalFiniteAdele D by simp]
    exact hxint
  have hKmul (u : CCMRationalProfiniteUnit)
      (x : CCMRationalFiniteAdele) :
      x * (u.1 : CCMRationalFiniteAdele) ∈ K ↔ x ∈ K := by
    have hpre := Set.ext_iff.mp
      (ccmRationalFiniteAdeleProfiniteMulRightEquiv_preimage_integral u)
      (E x)
    change E (x * (u.1 : CCMRationalFiniteAdele)) ∈
        ccmRationalIntegralFiniteAdeles ↔
      E x ∈ ccmRationalIntegralFiniteAdeles
    rw [show E (x * (u.1 : CCMRationalFiniteAdele)) =
        E x * (u.1 : CCMRationalFiniteAdele) by
      simp [E, qD, ccmRationalFiniteAdeleScalingEquiv_apply, mul_assoc]]
    simpa [ccmRationalFiniteAdeleProfiniteMulRightEquiv] using hpre
  let N : Set (CCMRationalFiniteAdele × CCMRationalProfiniteUnit) :=
    {p | p.1 * (p.2.1 : CCMRationalFiniteAdele) - p.1 ∈ V}
  have hNopen : IsOpen N := by
    apply V.isOpen.preimage
    fun_prop
  have hKN : K ×ˢ ({1} : Set CCMRationalProfiniteUnit) ⊆ N := by
    rintro ⟨x, u⟩ ⟨hxK, hu⟩
    have hu1 : u = 1 := Set.mem_singleton_iff.mp hu
    subst u
    change x * (1 : CCMRationalFiniteAdele) - x ∈ V
    simp
  obtain ⟨OX, U, hOXopen, hUopen, hKOX, h1U, hprod⟩ :=
    generalized_tube_lemma hKcompact isCompact_singleton hNopen hKN
  refine ⟨U, hUopen, h1U (Set.mem_singleton 1), fun u hu x => ?_⟩
  by_cases hxK : x ∈ K
  · have hpN := hprod
      (show (x, u) ∈ OX ×ˢ U from ⟨hKOX hxK, hu⟩)
    have hdisp : x * (u.1 : CCMRationalFiniteAdele) - x ∈ V := by
      exact hpN
    have heq := hV x
      ⟨x * (u.1 : CCMRationalFiniteAdele) - x, hdisp⟩
    have hadd : x + (x * (u.1 : CCMRationalFiniteAdele) - x) =
        x * (u.1 : CCMRationalFiniteAdele) := by
      abel
    rwa [hadd] at heq
  · have hx0 : phi.1 x = 0 := by
      by_contra hxne
      exact hxK (hsupportK hxne)
    have hxuK : x * (u.1 : CCMRationalFiniteAdele) ∉ K := by
      simpa only [hKmul u x] using hxK
    have hxu0 : phi.1 (x * (u.1 : CCMRationalFiniteAdele)) = 0 := by
      by_contra hxne
      exact hxuK (hsupportK hxne)
    rw [hxu0, hx0]

/-- Right translation of a finite Bruhat function is locally constant in the
literal profinite-unit coordinate, as an equality of functions on all finite
adeles. -/
theorem ccmRationalFiniteBruhatMulRight_apply_isLocallyConstant
    (phi : CCMRationalFiniteBruhatSchwartz) :
    IsLocallyConstant (fun b : CCMRationalProfiniteUnit =>
      fun x : CCMRationalFiniteAdele =>
        phi.1 (x * (b.1 : CCMRationalFiniteAdele))) := by
  obtain ⟨U, hUopen, h1U, hstab⟩ :=
    ccmRationalFiniteBruhat_exists_open_profiniteUnit_stabilizer phi
  rw [IsLocallyConstant.iff_eventually_eq]
  intro b
  have htend : Tendsto (fun b' : CCMRationalProfiniteUnit => b⁻¹ * b')
      (𝓝 b) (𝓝 1) := by
    have h := (continuousAt_const.mul continuousAt_id :
      ContinuousAt (fun b' : CCMRationalProfiniteUnit => b⁻¹ * b') b)
    change Tendsto (fun b' : CCMRationalProfiniteUnit => b⁻¹ * b')
      (𝓝 b) (𝓝 (b⁻¹ * b)) at h
    rw [inv_mul_cancel b] at h
    exact h
  have hev : ∀ᶠ b' in 𝓝 b, b⁻¹ * b' ∈ U :=
    htend (hUopen.mem_nhds h1U)
  filter_upwards [hev] with b' hb'
  funext x
  have heq := hstab (b⁻¹ * b') hb'
    (x * (b.1 : CCMRationalFiniteAdele))
  simpa [mul_assoc] using heq

end RHTower
end GaloisForLFunctions
