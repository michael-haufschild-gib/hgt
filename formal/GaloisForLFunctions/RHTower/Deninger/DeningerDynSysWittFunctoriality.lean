/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §1.

Functoriality of the rational Witt ring: `W_rat (id) = id` and `W_rat (g ∘ f) = W_rat g ∘ W_rat f`.
Both follow from the corresponding laws for the big Witt ring together with the injectivity and
naturality of the canonical embedding `W_rat (A) ↪ W (A)`.
-/
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittCanonicalMultiplication

namespace RHTower

variable {A B : Type*} [CommRing A] [CommRing B]

@[simp] theorem deningerCanonicalRationalWittMap_id (w : DeningerCanonicalRationalWittRing A) :
    deningerCanonicalRationalWittMap (RingHom.id A) w = w := by
  apply deningerCanonicalRationalWittEmbedding_injective
  show deningerCanonicalRationalWittEmbedding
      (deningerCanonicalRationalWittMapFun (RingHom.id A) w) = _
  rw [deningerCanonicalRationalWittEmbedding_mapFun, deningerBigWittRingMap_id]

@[simp] theorem deningerCanonicalRationalWittMap_comp {D : Type*} [CommRing D]
    (g : B →+* D) (f : A →+* B) (w : DeningerCanonicalRationalWittRing A) :
    deningerCanonicalRationalWittMap (g.comp f) w
      = deningerCanonicalRationalWittMap g (deningerCanonicalRationalWittMap f w) := by
  apply deningerCanonicalRationalWittEmbedding_injective
  show deningerCanonicalRationalWittEmbedding
      (deningerCanonicalRationalWittMapFun (g.comp f) w) = _
  rw [deningerCanonicalRationalWittEmbedding_mapFun, deningerBigWittRingMap_comp]
  show _ = deningerCanonicalRationalWittEmbedding
      (deningerCanonicalRationalWittMapFun g (deningerCanonicalRationalWittMapFun f w))
  rw [deningerCanonicalRationalWittEmbedding_mapFun,
    deningerCanonicalRationalWittEmbedding_mapFun]

/-- **The rational Witt ring functor respects monomorphisms.**  `W_rat (f)` is injective whenever
`f` is; in particular `W_rat (κ₀) ↪ W_rat (κ)` for a field extension. -/
theorem deningerCanonicalRationalWittMap_injective (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (deningerCanonicalRationalWittMap f) := by
  intro x y hxy
  apply DeningerCanonicalRationalWittRing.ext
  apply Additive.toMul.injective
  refine deningerRationalWittAdditiveMap_injective f hf ?_
  have h : deningerCanonicalRationalWittMapFun f x = deningerCanonicalRationalWittMapFun f y := hxy
  have h2 := congrArg DeningerCanonicalRationalWittRing.additiveVal h
  exact congrArg Additive.toMul h2

end RHTower
