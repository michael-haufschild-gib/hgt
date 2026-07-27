import GaloisForLFunctions.HTGeometry.DifferentialMatroidRank
import GaloisForLFunctions.HTGeometry.OrbitHeightFreeTranslates

/-!
# All-order uniform-face gluing for genuine differential independence

The order-three six-face gluing theorem is already specialized to the genuine differential matroid.
This file does the same for the *all-order* nested-star engine: a uniform family of faces whose
packets are individually differentially independent, whose star directions act by coefficient-fixing
differential automorphisms with an integer orbit height, and whose off-star translated packets are
differentially algebraic over the packet they came from, has a jointly differentially independent
total star.

The abstract hypotheses of `Rank.uniformFace_nestedStar_indep` are discharged here as follows:
rank-automorphism from `HTGeometry.DifferentialAlgEquiv.mem_differentialRank_rankAutSubgroup`, free
translates from the integer height (`Rank.hasFreeTranslates_of_intHeight`, or from an orbit
parametrization via `hasFreeTranslates_orbitUnion`), and cross-neutrality from
`differentialRank_crossNeutral_of_image_differentialAlgebraic`.

* **`differentialRank_uniformFace_nestedStar_diffIndepOn`** — the all-order statement, with only
  analytic inputs left: atomicity of each face packet, star stability and height of each direction,
  and off-star differential algebraicity;
* **`differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit`** — the same with the height
  hypothesis replaced by an injectively exponentiated orbit parametrization of each star.
-/

open scoped Classical Differential

namespace GaloisForLFunctions

open Set
open MatroidGluing MatroidGluing.Rank

noncomputable section

universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
  {V : Type*} [DecidableEq V]

/-- **All-order uniform-face nested-star gluing, for genuine differential independence.** -/
theorem differentialRank_uniformFace_nestedStar_diffIndepOn
    (faces : Finset (Finset V)) (O : Finset V → Set E)
    (σ : V → HTGeometry.DifferentialAlgEquiv F E) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hAtomic : ∀ J ∈ faces, DiffIndepOn F (O J))
    (height : V → E → ℤ)
    (hStarStable : ∀ (A : Finset V) (q : V), A.card < s → q ∉ A →
      ∀ x ∈ faceStar faces O (insert q A), ∀ n : ℤ,
        ((σ q).toAlgEquiv.toEquiv ^ n) x ∈ faceStar faces O (insert q A))
    (hStarHeight : ∀ (A : Finset V) (q : V), A.card < s → q ∉ A →
      ∀ x ∈ faceStar faces O (insert q A), ∀ n : ℤ,
        height q (((σ q).toAlgEquiv.toEquiv ^ n) x) = height q x + n)
    (hOffDA : ∀ (A : Finset V) (q : V), A.card < s → q ∉ A →
      ∀ t : Finset E, (↑t : Set E) ⊆
          (⋃ J ∈ (faces.filter (fun J => A ⊆ J)).filter (fun J => q ∉ J), O J) →
        ∀ n : ℤ, ∀ z, z ∈ (↑(t.image ⇑((σ q).toAlgEquiv.toEquiv ^ n)) : Set E) →
          DifferentialAlgebraicOver (differentialAdjoin F (↑t : Set E)) z) :
    DiffIndepOn F (faceStar faces O ∅) := by
  rw [← differentialRank_indepSet_iff]
  refine Rank.uniformFace_nestedStar_indep (differentialRank F E) faces O
    (fun q => (σ q).toAlgEquiv.toEquiv) s huniform
    (fun J hJ => (differentialRank_indepSet_iff).mpr (hAtomic J hJ))
    (fun q => (σ q).mem_differentialRank_rankAutSubgroup) ?_ ?_
  · intro A q hA hq
    exact Rank.hasFreeTranslates_of_intHeight _ _ (height q)
      (hStarStable A q hA hq) (hStarHeight A q hA hq)
  · intro A q hA hq
    exact differentialRank_crossNeutral_of_image_differentialAlgebraic _ _
      (hOffDA A q hA hq)

/-- **All-order uniform-face gluing from an orbit parametrization.**  Instead of an explicit
height, each star is presented as the union of full orbits of a base set on which distinct
exponents give distinct elements. -/
theorem differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit
    (faces : Finset (Finset V)) (O : Finset V → Set E)
    (σ : V → HTGeometry.DifferentialAlgEquiv F E) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hAtomic : ∀ J ∈ faces, DiffIndepOn F (O J))
    (base : Finset V → V → Set E)
    (hStarOrbit : ∀ (A : Finset V) (q : V), A.card < s → q ∉ A →
      faceStar faces O (insert q A) =
        orbitUnion ((σ q).toAlgEquiv.toEquiv) (base A q))
    (hStarInj : ∀ (A : Finset V) (q : V), A.card < s → q ∉ A →
      ∀ (m n : ℤ) (y z : E), y ∈ base A q → z ∈ base A q →
        ((σ q).toAlgEquiv.toEquiv ^ m) y = ((σ q).toAlgEquiv.toEquiv ^ n) z → m = n)
    (hOffDA : ∀ (A : Finset V) (q : V), A.card < s → q ∉ A →
      ∀ t : Finset E, (↑t : Set E) ⊆
          (⋃ J ∈ (faces.filter (fun J => A ⊆ J)).filter (fun J => q ∉ J), O J) →
        ∀ n : ℤ, ∀ z, z ∈ (↑(t.image ⇑((σ q).toAlgEquiv.toEquiv ^ n)) : Set E) →
          DifferentialAlgebraicOver (differentialAdjoin F (↑t : Set E)) z) :
    DiffIndepOn F (faceStar faces O ∅) := by
  rw [← differentialRank_indepSet_iff]
  refine Rank.uniformFace_nestedStar_indep (differentialRank F E) faces O
    (fun q => (σ q).toAlgEquiv.toEquiv) s huniform
    (fun J hJ => (differentialRank_indepSet_iff).mpr (hAtomic J hJ))
    (fun q => (σ q).mem_differentialRank_rankAutSubgroup) ?_ ?_
  · intro A q hA hq
    rw [hStarOrbit A q hA hq]
    exact hasFreeTranslates_orbitUnion _ _ (hStarInj A q hA hq)
  · intro A q hA hq
    exact differentialRank_crossNeutral_of_image_differentialAlgebraic _ _
      (hOffDA A q hA hq)

end

end GaloisForLFunctions
