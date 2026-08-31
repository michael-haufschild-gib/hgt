import GaloisForLFunctions.HTGeometry.MayerVietorisQuotient

/-!
# The Mayer–Vietoris sequence as a short exact complex

The three lemmas of `MayerVietorisQuotient.lean` are exactly the content of short exactness, so the
sequence assembles into a `ShortComplex (ModuleCat R)` that is `ShortExact`:

```text
mvDiff_comp_mvPair         the composite vanishes
mvShortComplex I J         0 → R ⧸ (I ⊓ J) → (R ⧸ I) × (R ⧸ J) → R ⧸ (I ⊔ J) → 0
mvShortComplex_shortExact  ** it is short exact **
```

`ModuleCat.mono_iff_injective`, `ModuleCat.epi_iff_surjective` and
`ShortComplex.moduleCat_exact_iff` translate the three conditions into the injectivity, exactness
and surjectivity already proved.

This is step 1 of the route to the non-cone Cohen–Macaulay induction: with a `ShortExact` complex in
hand, `covariantSequence_exact` of
`Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean` supplies the long exact `Ext`
sequence whose tail is the depth lemma `depth A ≥ min (depth B, depth C + 1)`.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u
variable {R : Type u} [CommRing R]

theorem mvDiff_comp_mvPair (I J : Ideal R) :
    (mvDiff I J).comp (mvPair I J) = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [mvPair_apply, mvDiff_apply, sub_self]

/-- The Mayer–Vietoris short complex of two ideals, in the category of modules. -/
noncomputable def mvShortComplex (I J : Ideal R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (mvPair I J))
    (ModuleCat.ofHom (mvDiff I J))
    (by
      apply ModuleCat.hom_ext
      simpa using mvDiff_comp_mvPair I J)

/-- **The Mayer–Vietoris sequence of two ideals is short exact.** -/
theorem mvShortComplex_shortExact (I J : Ideal R) : (mvShortComplex I J).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro w hw
    have hker : w ∈ LinearMap.ker (mvDiff I J) := hw
    rw [← mv_exact] at hker
    obtain ⟨z, hz⟩ := hker
    exact ⟨z, hz⟩
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    exact mvPair_injective I J
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    exact mvDiff_surjective I J

end GaloisForLFunctions.HTGeometry
