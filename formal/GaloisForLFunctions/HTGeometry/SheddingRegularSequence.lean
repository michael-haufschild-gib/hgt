import GaloisForLFunctions.HTGeometry.SheddingStep
import GaloisForLFunctions.HTGeometry.ReesDepth

/-!
# The shedding step in regular-sequence form

Rees converts the depth hypotheses into `Ext`-vanishing, the shedding step transfers that across the
Mayer–Vietoris sequence, and Rees converts back:

```text
exists_isRegular_mv
    ** regular sequences of length n₁ on R ⧸ I and R ⧸ J inside 𝔪, one of length n₀ on
       R ⧸ (I ⊔ J)  ⟹  one of length n₁ on R ⧸ (I ⊓ J) **
exists_isRegular_faceFamily
    ** the same for a face family: deletion and star of length n₁, link of length n₀
       ⟹ the complex of length n₁ **
```

This closes the chain the Hankel card needs.  Everything is now a regular-sequence statement, in the
vocabulary the Cohen–Macaulay definition uses, and the remaining work on the card is to run the
recursion at `Δ_r` with the shedding vertex `0`, where the base case `N ≤ 2r` and the cone case are
already proved.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory CategoryTheory.Abelian

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- **The shedding step in regular-sequence form.**  Rees converts the depth hypotheses into
`Ext`-vanishing, the shedding step transfers it across the Mayer–Vietoris sequence, and Rees
converts back. -/
theorem exists_isRegular_mv (𝔪 I J : Ideal R) {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    (hltI : 𝔪 • (⊤ : Submodule R (ModuleCat.of R (R ⧸ I))) < ⊤)
    (hltJ : 𝔪 • (⊤ : Submodule R (ModuleCat.of R (R ⧸ J))) < ⊤)
    (hltS : 𝔪 • (⊤ : Submodule R (ModuleCat.of R (R ⧸ (I ⊔ J)))) < ⊤)
    (hltT : 𝔪 • (⊤ : Submodule R (ModuleCat.of R (R ⧸ (I ⊓ J)))) < ⊤)
    (hI : ∃ rs : List R, rs.length = n₁ ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular (ModuleCat.of R (R ⧸ I)) rs)
    (hJ : ∃ rs : List R, rs.length = n₁ ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular (ModuleCat.of R (R ⧸ J)) rs)
    (hS : ∃ rs : List R, rs.length = n₀ ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular (ModuleCat.of R (R ⧸ (I ⊔ J))) rs) :
    ∃ rs : List R, rs.length = n₁ ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular (ModuleCat.of R (R ⧸ (I ⊓ J))) rs := by
  refine exists_isRegular_of_ext 𝔪 n₁ (ModuleCat.of R (R ⧸ (I ⊓ J))) hltT ?_
  refine subsingleton_ext_mv_lt I J _ hn ?_ ?_ ?_
  · exact ext_subsingleton_of_isRegular 𝔪 n₁ _ hltI hI
  · exact ext_subsingleton_of_isRegular 𝔪 n₁ _ hltJ hJ
  · exact ext_subsingleton_of_isRegular 𝔪 n₀ _ hltS hS

section FaceFamily

open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

/-- **The shedding step for a Stanley–Reisner ring, in regular-sequence form.**  If the deletion and
the star of a vertex carry regular sequences of length `n₁` inside `𝔪` and the link one of length
`n₀`, then so does the complex. -/
theorem exists_isRegular_faceFamily {F : Finset (Finset σ)} (hF : IsFaceFamily F) (v : σ)
    (𝔪 : Ideal (MvPolynomial σ K)) {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    (hltI : 𝔪 • (⊤ : Submodule (MvPolynomial σ K)
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v)))) < ⊤)
    (hltJ : 𝔪 • (⊤ : Submodule (MvPolynomial σ K)
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceStar F v)))) < ⊤)
    (hltS : 𝔪 • (⊤ : Submodule (MvPolynomial σ K)
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceLink F v)))) < ⊤)
    (hltT : 𝔪 • (⊤ : Submodule (MvPolynomial σ K)
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K ⧸ faceFamilyIdeal K F))) < ⊤)
    (hI : ∃ rs : List (MvPolynomial σ K), rs.length = n₁ ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v))) rs)
    (hJ : ∃ rs : List (MvPolynomial σ K), rs.length = n₁ ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceStar F v))) rs)
    (hS : ∃ rs : List (MvPolynomial σ K), rs.length = n₀ ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceLink F v))) rs) :
    ∃ rs : List (MvPolynomial σ K), rs.length = n₁ ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K ⧸ faceFamilyIdeal K F)) rs := by
  have hsup := faceFamilyIdeal_link_eq_sup K hF v
  have hinf := faceFamilyIdeal_deletion_inf_star K hF v
  rw [hinf] at hltT ⊢
  rw [hsup] at hltS hS
  exact exists_isRegular_mv 𝔪 _ _ hn hltI hltJ hltS hltT hI hJ hS

end FaceFamily


end GaloisForLFunctions.HTGeometry
