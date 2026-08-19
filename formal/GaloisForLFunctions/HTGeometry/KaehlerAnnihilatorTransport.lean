import Mathlib.RingTheory.Kaehler.Basic

/-!
# The annihilator of the differentials is an isomorphism invariant

Neither mathlib nor this corpus carried the transport of Kähler differentials along an algebra
isomorphism.  Only the push-forward along a *surjection* is needed, and twice — once in each
direction of the isomorphism — so no injectivity and no inverse map has to be built:

```text
annihilator_kaehler_map_of_surjective
    b annihilates Ω[B⁄A]  ⟹  algebraMap B C b annihilates Ω[C⁄A],
    whenever algebraMap B C is surjective
annihilator_kaehler_algEquiv
    ** b annihilates Ω[B⁄A]  ↔  e b annihilates Ω[C⁄A]  for an algebra isomorphism e **
```

The proof of the first is three lines from `KaehlerDifferential.map_surjective_of_surjective`:
every differential of `C` is the image of one of `B`, and the map is semilinear over
`algebraMap B C`.

This is what carries `ConstraintRelativity.MonogenicKaehler.annihilator_kaehler`, stated for
`AdjoinRoot (minpoly A x)`, across `minpoly.equivAdjoin` to a monogenic extension `B = A[x]`, where
it meets `DifferentIdealMonogenic.differentIdeal_eq_span_aeval_derivative` — both sides being
`span {p'(x)}`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- **The annihilator of the differentials pushes forward along a surjection.** -/
theorem annihilator_kaehler_map_of_surjective
    (h : Function.Surjective (algebraMap B C)) {b : B}
    (hb : b ∈ Module.annihilator B (Ω[B⁄A])) :
    algebraMap B C b ∈ Module.annihilator C (Ω[C⁄A]) := by
  refine Module.mem_annihilator.mpr fun ω => ?_
  obtain ⟨ν, rfl⟩ := KaehlerDifferential.map_surjective_of_surjective A A B C h ω
  have hsm : algebraMap B C b • KaehlerDifferential.map A A B C ν
      = KaehlerDifferential.map A A B C (b • ν) := by
    rw [map_smul, IsScalarTower.algebraMap_smul]
  rw [hsm, Module.mem_annihilator.mp hb ν, map_zero]

section Equiv

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- **The annihilator of the differentials is transported by an algebra isomorphism.** -/
theorem annihilator_kaehler_algEquiv (e : B ≃ₐ[A] C) (b : B) :
    b ∈ Module.annihilator B (Ω[B⁄A]) ↔ e b ∈ Module.annihilator C (Ω[C⁄A]) := by
  constructor
  · intro hb
    letI : Algebra B C := (e : B →ₐ[A] C).toRingHom.toAlgebra
    haveI : IsScalarTower A B C :=
      IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
    have hsurj : Function.Surjective (algebraMap B C) := e.surjective
    have h := annihilator_kaehler_map_of_surjective (A := A) hsurj hb
    exact h
  · intro hb
    letI : Algebra C B := (e.symm : C →ₐ[A] B).toRingHom.toAlgebra
    haveI : IsScalarTower A C B :=
      IsScalarTower.of_algebraMap_eq fun a => (e.symm.commutes a).symm
    have hsurj : Function.Surjective (algebraMap C B) := e.symm.surjective
    have h := annihilator_kaehler_map_of_surjective (A := A) hsurj hb
    have hb' : algebraMap C B (e b) = b := e.symm_apply_apply b
    rwa [hb'] at h

end Equiv

end GaloisForLFunctions.HTGeometry
