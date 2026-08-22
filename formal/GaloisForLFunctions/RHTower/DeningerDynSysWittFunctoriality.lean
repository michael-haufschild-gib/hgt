/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §1.

Functoriality of the rational Witt ring: `W_rat (id) = id` and `W_rat (g ∘ f) = W_rat g ∘ W_rat f`.
Both follow from the corresponding laws for the big Witt ring together with the injectivity and
naturality of the canonical embedding `W_rat (A) ↪ W (A)`.
-/
import GaloisForLFunctions.RHTower.DeningerRationalWittCanonicalMultiplication

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

end RHTower
