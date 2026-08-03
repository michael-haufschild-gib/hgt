import GaloisForLFunctions.RHTower.DeningerTreeAcyclic

/-!
# The tree of cosets as a short exact sequence of representations

The augmented chain complex of the tree of cosets of a pushout of groups with injective structure
maps is a short exact sequence of representations.  This is the input to the long exact sequence in
group homology from which Mayer-Vietoris is read off.

* `deningerTreeShortComplex` : the short complex `k[E] → k[V] → k`.
* `deningerTreeShortComplex_shortExact` : it is short exact.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory

universe u

variable {ι : Type u} {G : ι → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} (k : Type u) [CommRing k]

/-- The augmented chain complex of the tree of cosets, as a short complex of representations. -/
noncomputable def deningerTreeShortComplex : ShortComplex (Rep k (PushoutI φ)) :=
  ShortComplex.mk (deningerTreeBoundaryHom (φ := φ) k) (deningerTreeAugHom k) (by
    ext x
    have hz := DFunLike.congr_fun (deningerTreeAug_comp_boundary (φ := φ) k)
      (MonoidAlgebra.single x (1 : k))
    show (deningerTreeAug k) ((deningerTreeBoundary k) (MonoidAlgebra.single x (1 : k))) = 0
    simpa using hz)

/-- **The tree sequence is short exact.**  Injectivity is acyclicity of the tree, exactness in the
middle is its connectivity, and surjectivity of the augmentation is immediate. -/
theorem deningerTreeShortComplex_shortExact (hφ : ∀ i, Function.Injective (φ i)) :
    (deningerTreeShortComplex (φ := φ) k).ShortExact where
  exact := (forget₂ (Rep k (PushoutI φ)) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => deningerTree_connected k x hx
  mono_f := (Rep.mono_iff_injective _).2 (deningerTreeBoundary_injective k hφ)
  epi_g := (Rep.epi_iff_surjective _).2 (deningerTreeAug_surjective k)

end RHTower
