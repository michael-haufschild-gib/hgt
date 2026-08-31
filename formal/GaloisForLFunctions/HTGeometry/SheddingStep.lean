import GaloisForLFunctions.HTGeometry.ExtMiddleProduct
import GaloisForLFunctions.HTGeometry.StanleyReisnerMayerVietoris

/-!
# The shedding step

The Cohen–Macaulay induction at a non-cone vertex, assembled from the Mayer–Vietoris sequence, the
depth lemma and the product case:

```text
subsingleton_ext_mv_lt
    ** R ⧸ I and R ⧸ J deep to n₁, R ⧸ (I ⊔ J) deep to n₀  ⟹  R ⧸ (I ⊓ J) deep to n₁ **
subsingleton_ext_faceFamily
    ** the same for a face family: deletion and star deep to n₁, link deep to n₀
       ⟹ the complex deep to n₁ **
```

The second is the first instantiated at `I = I_{del(v)}`, `J = I_{st(v)}`, where
`faceFamilyIdeal_deletion_inf_star` identifies `I ⊓ J` with `I_Δ` and `faceFamilyIdeal_link_eq_sup`
identifies `I ⊔ J` with `I_{lk(v)}`.

Since the star is a cone over the link (`isConePoint_faceStar`), its Stanley–Reisner ring is deep
whenever the link's is; so in practice the two hypotheses are "the deletion and the link are
Cohen–Macaulay of dimensions `d` and `d-1`", and the conclusion is depth `d` for the complex.  Read
through `ReesDepth.lean` this is the regular-sequence statement the Hankel card consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [CategoryTheory.HasExt.{w} (ModuleCat.{u} R)]

/-- **The shedding step, in `Ext` form.**  For two ideals `I`, `J`, if `R ⧸ I` and `R ⧸ J` have
vanishing `Ext` below `n₁` and `R ⧸ (I ⊔ J)` below `n₀` with `n₀ + 1 = n₁`, then so does
`R ⧸ (I ⊓ J)`.

With `I = I_{del(v)}` and `J = I_{st(v)}` this says: if the deletion and the star are deep to `n₁`
and the link is deep to `n₀`, then the whole complex is deep to `n₁` — the Cohen–Macaulay induction
step at a non-cone vertex. -/
theorem subsingleton_ext_mv_lt (I J : Ideal R) (X : ModuleCat.{u} R) {n₀ n₁ : ℕ}
    (hn : n₀ + 1 = n₁)
    (hI : ∀ i < n₁, Subsingleton (Ext.{w} X (ModuleCat.of R (R ⧸ I)) i))
    (hJ : ∀ i < n₁, Subsingleton (Ext.{w} X (ModuleCat.of R (R ⧸ J)) i))
    (hsup : ∀ i < n₀, Subsingleton (Ext.{w} X (ModuleCat.of R (R ⧸ (I ⊔ J))) i)) :
    ∀ i < n₁, Subsingleton (Ext.{w} X (ModuleCat.of R (R ⧸ (I ⊓ J))) i) := by
  refine subsingleton_ext_lt_of_shortExact X (mvShortComplex_shortExact I J) hn ?_ hsup
  intro i hi
  exact subsingleton_ext_prod X (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J))
    (hI i hi) (hJ i hi)

section StanleyReisner

open MvPolynomial

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]
variable [CategoryTheory.HasExt.{w} (ModuleCat.{u} (MvPolynomial σ K))]

/-- **The shedding step for a Stanley–Reisner ring.**  If the deletion and the star of a vertex are
deep to `n₁` and the link is deep to `n₀`, with `n₀ + 1 = n₁`, then the whole complex is deep to
`n₁`.

This is the Cohen–Macaulay induction step at a non-cone vertex, stated on the ideals produced by
`faceFamilyIdeal_deletion_inf_star` and `faceFamilyIdeal_link_eq_sup`. -/
theorem subsingleton_ext_faceFamily {F : Finset (Finset σ)} (hF : IsFaceFamily F) (v : σ)
    (X : ModuleCat.{u} (MvPolynomial σ K)) {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    (hdel : ∀ i < n₁, Subsingleton (Ext.{w} X
      (ModuleCat.of _ (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v))) i))
    (hst : ∀ i < n₁, Subsingleton (Ext.{w} X
      (ModuleCat.of _ (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceStar F v))) i))
    (hlk : ∀ i < n₀, Subsingleton (Ext.{w} X
      (ModuleCat.of _ (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceLink F v))) i)) :
    ∀ i < n₁, Subsingleton (Ext.{w} X
      (ModuleCat.of _ (MvPolynomial σ K ⧸ faceFamilyIdeal K F)) i) := by
  rw [faceFamilyIdeal_deletion_inf_star K hF v]
  refine subsingleton_ext_mv_lt _ _ X hn hdel hst ?_
  rw [← faceFamilyIdeal_link_eq_sup K hF v]
  exact hlk

end StanleyReisner


end GaloisForLFunctions.HTGeometry
