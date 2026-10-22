import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittFatouIntersection
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittLocalSections

/-!
# The Fatou intersection theorem on the wrapped Witt-ring carriers

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.10(2),
transported from the literal additive carriers `1 + TA[[T]]` to the ring carriers
`W (A)` and `W_rat (A)` that carry the presheaf structures of §2.

For an extension of domains `A ⊆ B` with `A` Fatou, a rational Witt vector over `B` descends to
`A` exactly when its power series has coefficients in `A`, i.e. exactly when it lies in the image
of `W (A) → W (B)`.
-/

namespace RHTower

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B]

theorem deningerCanonicalRationalWittMap_additiveVal (f : A →+* B)
    (v : DeningerCanonicalRationalWittRing A) :
    (deningerCanonicalRationalWittMap f v).additiveVal
      = Additive.ofMul (deningerRationalWittAdditiveMap f (Additive.toMul v.additiveVal)) := rfl

theorem deningerCanonicalRationalWittEmbedding_additiveVal
    (v : DeningerCanonicalRationalWittRing A) :
    (deningerCanonicalRationalWittEmbedding v).additiveVal
      = Additive.ofMul (deningerRationalWittToBigWittAdditive A
        (Additive.toMul v.additiveVal)) := rfl

/-- **Deninger, Corollary 1.10(2), on the ring carriers.**  For an extension of domains `A ⊆ B`
with `A` Fatou, a rational Witt vector over `B` descends to `A` exactly when it lies in the image
of the big Witt ring of `A`. -/
theorem deningerRationalWittFatouIntersection_ring
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] (hA : DeningerFatouDomain A)
    (v : DeningerCanonicalRationalWittRing B) :
    (∃ v₀ : DeningerCanonicalRationalWittRing A,
        deningerCanonicalRationalWittMap (algebraMap A B) v₀ = v)
      ↔ ∃ w₀ : DeningerBigWittRing A,
          deningerBigWittRingMap (algebraMap A B) w₀
            = deningerCanonicalRationalWittEmbedding v := by
  constructor
  · rintro ⟨v₀, rfl⟩
    exact ⟨deningerCanonicalRationalWittEmbedding v₀,
      (deningerCanonicalRationalWittEmbedding_mapFun _ _).symm⟩
  · rintro ⟨w₀, hw₀⟩
    have hadd : deningerBigWittAdditiveMap (algebraMap A B)
        (Additive.toMul w₀.additiveVal)
      = deningerRationalWittToBigWittAdditive B (Additive.toMul v.additiveVal) := by
      exact congrArg (fun z : DeningerBigWittRing B => Additive.toMul z.additiveVal) hw₀
    obtain ⟨v₀, hv₀⟩ := (deningerRationalWittFatouIntersection_iff A B hA
      (Additive.toMul v.additiveVal)).2 ⟨Additive.toMul w₀.additiveVal, hadd⟩
    refine ⟨⟨Additive.ofMul v₀⟩, ?_⟩
    apply DeningerCanonicalRationalWittRing.ext
    apply Additive.toMul.injective
    exact hv₀

end

end RHTower
