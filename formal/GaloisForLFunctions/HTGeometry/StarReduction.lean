import GaloisForLFunctions.HTGeometry.ConeRegularSequence

/-!
# The star reduction, and the recursion step with only two hypotheses

The star of a vertex is a cone with that apex, and deleting the apex from the star gives the link.
So a regular sequence on the link extends by the vertex to one on the star, and the star hypothesis
of the shedding step is redundant:

```text
faceDeletion_faceStar        del (st(v)) v = lk(v)
exists_isRegular_star        a sequence of length n on the link gives one of length n+1 on the star
exists_isRegular_shedding
    ** the recursion step needs only the deletion (length n₀+1) and the link (length n₀) **
```

This is the form the recursion over a simplicial complex actually runs in: at each vertex one
descends to the deletion and the link, and the star takes care of itself.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

omit [Fintype σ] in
/-- **The deletion of a vertex from its star is the link.** -/
theorem faceDeletion_faceStar (F : Finset (Finset σ)) (v : σ) :
    faceDeletion (faceStar F v) v = faceLink F v := by
  classical
  ext S
  rw [mem_faceDeletion, mem_faceStar, mem_faceLink]
  constructor
  · rintro ⟨⟨hS, hins⟩, hv⟩
    exact ⟨hS, hv, hins⟩
  · rintro ⟨hS, hv, hins⟩
    exact ⟨⟨hS, hins⟩, hv⟩

/-- **The star reduction.**  A regular sequence on the link extends by the vertex to one on the
star, because the star is a cone with that apex and its deletion is the link.

This removes one of the three hypotheses of the shedding step: only the deletion and the link need
to be known. -/
theorem exists_isRegular_star (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) (v : σ) (𝔪 : Ideal (MvPolynomial σ K))
    (hv𝔪 : (X v : MvPolynomial σ K) ∈ 𝔪) {n : ℕ}
    (hlk : ∃ rs : List (MvPolynomial σ K), rs.length = n ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceLink F v)) rs) :
    ∃ rs : List (MvPolynomial σ K), rs.length = n + 1 ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceStar F v)) rs := by
  refine exists_isRegular_cone K (isFaceFamily_faceStar hF v) (isConePoint_faceStar v) 𝔪 hv𝔪 ?_
  rw [faceDeletion_faceStar F v]
  exact hlk

/-- **The recursion step with the star eliminated.**  Only the deletion and the link are needed. -/
theorem exists_isRegular_shedding (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) (v : σ) (𝔪 : Ideal (MvPolynomial σ K))
    (hv𝔪 : (X v : MvPolynomial σ K) ∈ 𝔪) {n₀ : ℕ}
    (hltI : 𝔪 • (⊤ : Submodule (MvPolynomial σ K)
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v)))) < ⊤)
    (hltJ : 𝔪 • (⊤ : Submodule (MvPolynomial σ K)
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceStar F v)))) < ⊤)
    (hltS : 𝔪 • (⊤ : Submodule (MvPolynomial σ K)
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceLink F v)))) < ⊤)
    (hltT : 𝔪 • (⊤ : Submodule (MvPolynomial σ K)
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ faceFamilyIdeal K F))) < ⊤)
    (hdel : ∃ rs : List (MvPolynomial σ K), rs.length = n₀ + 1 ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v)) rs)
    (hlk : ∃ rs : List (MvPolynomial σ K), rs.length = n₀ ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceLink F v)) rs) :
    ∃ rs : List (MvPolynomial σ K), rs.length = n₀ + 1 ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (MvPolynomial σ K ⧸ faceFamilyIdeal K F) rs :=
  exists_isRegular_faceFamily hF v 𝔪 rfl hltI hltJ hltS hltT hdel
    (exists_isRegular_star K hF v 𝔪 hv𝔪 hlk) hlk

end GaloisForLFunctions.HTGeometry
