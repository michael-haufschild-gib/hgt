import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysRationalWittPresheaf

/-!
# Faithfulness of the rational Witt functor

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 2.4
(`t27xn`).

Two morphisms of schemes `α, β : Y → X` with `W_rat (α) = W_rat (β)` have the same underlying map
of topological spaces, and the induced maps on stalks satisfy
`W_rat (α^♯_y) = W_rat (β^♯_y)`.  Since the Teichmüller map is a natural, injective multiplicative
section of the construction, this forces `α^♯_y = β^♯_y`.

The algebraic content is precisely that the rational Witt functor is faithful: a ring
homomorphism is determined by the induced map on rational Witt rings.  That is proved here for the
ring functor and for the functor `W_rat : CommRingCat ⥤ CommRingCat` of Proposition 2.1.
-/

namespace RHTower

open CategoryTheory

/-- The Teichmüller map into the rational Witt ring is injective. -/
theorem deningerCanonicalRationalWittTeichmuller_injective {A : Type*} [CommRing A] :
    Function.Injective (deningerCanonicalRationalWittTeichmuller (A := A)) := by
  intro a b h
  have h' := congrArg (deningerCanonicalRationalWittEmbedding (A := A)) h
  rw [deningerCanonicalRationalWittEmbedding_teichmuller,
    deningerCanonicalRationalWittEmbedding_teichmuller] at h'
  exact deningerBigWittRingTeichmuller_injective h'

/-- **Deninger, Proposition 2.4 (`t27xn`), algebraic content.**  A ring homomorphism is determined
by the induced homomorphism of rational Witt rings. -/
theorem deningerCanonicalRationalWittMap_faithful {A B : Type*} [CommRing A] [CommRing B]
    {f g : A →+* B}
    (h : deningerCanonicalRationalWittMap f = deningerCanonicalRationalWittMap g) : f = g := by
  ext a
  refine deningerCanonicalRationalWittTeichmuller_injective ?_
  have h1 := congrArg (fun F => F (deningerCanonicalRationalWittTeichmuller a)) h
  rwa [deningerCanonicalRationalWittMap_teichmuller,
    deningerCanonicalRationalWittMap_teichmuller] at h1

/-- **Deninger, Proposition 2.4 (`t27xn`).**  The rational Witt functor on commutative rings is
faithful. -/
instance deningerRationalWittFunctor_faithful : deningerRationalWittFunctor.Faithful where
  map_injective {A B f g} h := by
    have h' : deningerCanonicalRationalWittMap f.hom = deningerCanonicalRationalWittMap g.hom := by
      have := congrArg CommRingCat.Hom.hom h
      exact this
    exact CommRingCat.hom_ext (deningerCanonicalRationalWittMap_faithful h')

end RHTower
