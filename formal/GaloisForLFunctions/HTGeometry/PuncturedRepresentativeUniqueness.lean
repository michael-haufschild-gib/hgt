import GaloisForLFunctions.HTGeometry.MeromorphicPuncturedRepresentation

/-!
# A punctured-local representative determines the field element

Two elements of the global meromorphic field represented by the same function on a punctured
neighbourhood of every point are equal.  Cross-multiplying the two entire presentations gives an
entire function vanishing on one punctured neighbourhood — the two denominators are nonzero there,
because a nonzero entire function has isolated zeros — hence vanishing identically by the identity
theorem on the connected plane.  Equality of the cross products is equality of the fractions.

This is what turns an identity of meromorphic functions proved off the poles into an identity in the
field.
-/

open Filter Set Topology Function Complex

namespace GaloisForLFunctions

open Bottcher

noncomputable section

attribute [local instance] puncturedRepDomain puncturedRepComplexAlgebraAnalytic
  puncturedRepComplexAlgebraMero

/-- An entire germ whose function vanishes identically is the zero germ. -/
theorem analyticSubring_eq_zero_of_forall_eq_zero {a : analyticSubring (Set.univ : Set ℂ)}
    {f : ℂ → ℂ} (hfa : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) f = (a : Germ _ ℂ))
    (hf : ∀ z, f z = 0) : a = 0 := by
  refine Subtype.ext ?_
  rw [← hfa]
  have hfun : f = 0 := funext hf
  rw [hfun]
  exact map_zero _

/-- **A punctured-local representative determines the element.** -/
theorem eq_of_hasPuncturedMeromorphicRep {x y : meroField (Set.univ : Set ℂ)} {φ : ℂ → ℂ}
    (hx : HasPuncturedMeromorphicRep x φ) (hy : HasPuncturedMeromorphicRep y φ) : x = y := by
  obtain ⟨a, b, f, g, hb, hf, hg, hfa, hgb, hxeq, hxev⟩ := hx
  obtain ⟨c, d, h, k, hd, hh, hk, hhc, hkd, hyeq, hyev⟩ := hy
  -- a point where the first denominator does not vanish
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, g z₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (analyticSubring_eq_zero_of_forall_eq_zero hgb hcon)
  -- both denominators are nonzero on a punctured neighbourhood of that point
  have hgev : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 :=
    nhdsWithin_le_nhds (((hg z₀ (mem_univ z₀)).continuousAt).eventually_ne hz₀)
  have hkev : ∀ᶠ z in 𝓝[≠] z₀, k z ≠ 0 := by
    rcases (hk z₀ (mem_univ z₀)).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact absurd (analyticSubring_eq_zero_of_forall_eq_zero hkd fun z =>
        hk.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z₀)
          hzero (mem_univ z)) hd
    · exact hne
  -- the cross product vanishes on that punctured neighbourhood
  set F : ℂ → ℂ := fun z => f z * k z - h z * g z with hF
  have hFanalytic : AnalyticOnNhd ℂ F Set.univ := (hf.mul hk).sub (hh.mul hg)
  have hFev : ∀ᶠ z in 𝓝[≠] z₀, F z = 0 := by
    filter_upwards [hxev z₀, hyev z₀, hgev, hkev] with z h1 h2 h3 h4
    have h12 : f z / g z = h z / k z := by rw [h1, h2]
    rw [hF]
    field_simp at h12
    linear_combination h12
  -- hence identically, by the identity theorem
  have hFnhds : F =ᶠ[𝓝 z₀] 0 := by
    rcases (hFanalytic z₀ (mem_univ z₀)).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact hzero
    · obtain ⟨z, hz1, hz2⟩ := (hFev.and hne).exists
      exact absurd hz1 hz2
  have hFzero : ∀ z, f z * k z = h z * g z := by
    intro z
    have := hFanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ z₀) hFnhds (mem_univ z)
    rw [hF] at this
    exact sub_eq_zero.mp this
  -- equality of the cross products is equality of the fractions
  have hgerm : a * d = c * b := by
    refine Subtype.ext ?_
    rw [Subring.coe_mul, Subring.coe_mul, ← hfa, ← hkd, ← hhc, ← hgb, ← map_mul, ← map_mul]
    exact congrArg _ (funext hFzero)
  have hbne : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb
  have hdne : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hd
  rw [hxeq, hyeq, div_eq_div_iff hbne hdne, ← map_mul, ← map_mul, hgerm]

end

end GaloisForLFunctions
