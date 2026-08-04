import GaloisForLFunctions.HTGeometry.IsogenyComplement

/-!
# Isogeny-regular groups and the isogeny relation

A commutative group is **isogeny-regular** when multiplication by every positive integer is an
isogeny, that is, has finite kernel and finite cokernel.  Finite groups, finitely generated
groups, lattices, algebraic tori and the point groups of abelian varieties over an algebraically
closed field are all of this kind, and it is exactly the condition under which "being isogenous"
becomes an equivalence relation rather than a mere preorder.

Two facts organise the theory.  First, isogeny-regularity is transported along isogenies, so the
condition is a property of an isogeny class and not of a representative.  Second, on isogeny-
regular groups the complementary map of an isogeny is again an isogeny, which supplies symmetry.

The resulting invariant is the degree of multiplication by `n`: it is constant on isogeny classes.
For abelian varieties this degree is `n ^ (2 dim)`, so isogenous abelian varieties have equal
dimension; for lattices it is `n ^ (-rank)`, so isogenous lattices have equal rank.  The single
statement `isogenyDegree_pow_eq_of_isogeny` covers both.
-/

open Subgroup

variable {G H K : Type*} [CommGroup G] [CommGroup H] [CommGroup K]

/-- An additive commutative group is **isogeny-regular** when multiplication by every positive
integer is an isogeny. -/
class IsAddIsogenyRegular (G : Type*) [AddCommGroup G] : Prop where
  /-- Multiplication by every positive integer has finite kernel and finite cokernel. -/
  isogeny_nsmul : ∀ n : ℕ, 0 < n → IsAddIsogeny (nsmulAddMonoidHom n : G →+ G)

/-- A commutative group is **isogeny-regular** when every positive power map is an isogeny. -/
@[to_additive IsAddIsogenyRegular]
class IsIsogenyRegular (G : Type*) [CommGroup G] : Prop where
  /-- Every positive power map has finite kernel and finite cokernel. -/
  isogeny_pow : ∀ n : ℕ, 0 < n → IsIsogeny (powMonoidHom n : G →* G)

/-- Finite commutative groups are isogeny-regular. -/
@[to_additive /-- Finite additive commutative groups are isogeny-regular. -/]
instance (priority := 100) IsIsogenyRegular.of_finite (G : Type*) [CommGroup G] [Finite G] :
    IsIsogenyRegular G where
  isogeny_pow _ _ := ⟨inferInstance, inferInstance⟩

namespace IsIsogeny

/-- The `n`-th power map commutes with every homomorphism. -/
@[to_additive /-- Multiplication by `n` commutes with every additive homomorphism. -/]
theorem powMonoidHom_comp (f : G →* H) (n : ℕ) :
    (powMonoidHom n : H →* H).comp f = f.comp (powMonoidHom n : G →* G) := by
  ext x
  simp

/-- Isogeny-regularity is transported along an isogeny. -/
@[to_additive isAddIsogenyRegular_target /-- Isogeny-regularity is transported along an additive
isogeny. -/]
theorem isIsogenyRegular_target [IsIsogenyRegular G] {f : G →* H} (hf : IsIsogeny f) :
    IsIsogenyRegular H := by
  refine ⟨fun n hn => ?_⟩
  have hGn : IsIsogeny (powMonoidHom n : G →* G) := IsIsogenyRegular.isogeny_pow n hn
  have hcomp : IsIsogeny ((powMonoidHom n : H →* H).comp f) := by
    rw [powMonoidHom_comp f n]
    exact hf.comp hGn
  haveI := hcomp.finite_ker
  haveI := hf.finite_coker
  constructor
  · -- The kernel of `[n]` on `H` meets `im f` in a finite group, with finite relative index.
    have hcard : Nat.card ((powMonoidHom n : H →* H).comp f).ker
        = Nat.card f.ker
          * Nat.card (f.range ⊓ (powMonoidHom n : H →* H).ker : Subgroup H) :=
      MonoidHom.card_ker_comp f _
    have hne : Nat.card (f.range ⊓ (powMonoidHom n : H →* H).ker : Subgroup H) ≠ 0 := by
      intro hzero
      rw [hzero, Nat.mul_zero] at hcard
      exact Nat.card_pos.ne' hcard
    haveI : Finite (f.range ⊓ (powMonoidHom n : H →* H).ker : Subgroup H) :=
      Nat.finite_of_card_ne_zero hne
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.card_mul_relIndex
      (P := (f.range ⊓ (powMonoidHom n : H →* H).ker))
      (Q := (powMonoidHom n : H →* H).ker) inf_le_right]
    refine Nat.mul_ne_zero (Nat.card_pos.ne') ?_
    rw [Subgroup.inf_relIndex_right]
    intro hzero
    exact Subgroup.index_ne_zero_of_finite (H := f.range)
      (Nat.eq_zero_of_zero_dvd (hzero ▸ Subgroup.relIndex_dvd_index_of_normal f.range
        (powMonoidHom n : H →* H).ker))
  · -- The image of `[n]` on `H` contains the image of the composite, of finite index.
    haveI := hcomp.finite_coker
    have hle : ((powMonoidHom n : H →* H).comp f).range ≤ (powMonoidHom n : H →* H).range := by
      rw [MonoidHom.range_comp]
      exact Subgroup.map_le_range _ f.range
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.index_eq_card]
    intro hzero
    exact Subgroup.index_ne_zero_of_finite (H := ((powMonoidHom n : H →* H).comp f).range)
      (Nat.eq_zero_of_zero_dvd (hzero ▸ Subgroup.index_dvd_of_le hle))

/-- Isogeny-regularity is reflected by an isogeny: if the target is isogeny-regular so is the
source. -/
@[to_additive isAddIsogenyRegular_source /-- Isogeny-regularity is reflected by an additive
isogeny. -/]
theorem isIsogenyRegular_source [IsIsogenyRegular H] {f : G →* H} (hf : IsIsogeny f) :
    IsIsogenyRegular G := by
  refine ⟨fun n hn => ?_⟩
  have hHn : IsIsogeny (powMonoidHom n : H →* H) := IsIsogenyRegular.isogeny_pow n hn
  have hcomp : IsIsogeny (f.comp (powMonoidHom n : G →* G)) := by
    rw [← powMonoidHom_comp f n]
    exact hHn.comp hf
  haveI := hcomp.finite_ker
  haveI := hcomp.finite_coker
  haveI := hf.finite_ker
  constructor
  · -- The kernel of `[n]` on `G` is a factor of the kernel of the composite.
    have hcard : Nat.card (f.comp (powMonoidHom n : G →* G)).ker
        = Nat.card (powMonoidHom n : G →* G).ker
          * Nat.card ((powMonoidHom n : G →* G).range ⊓ f.ker : Subgroup G) :=
      MonoidHom.card_ker_comp _ f
    refine Nat.finite_of_card_ne_zero ?_
    intro hzero
    rw [hzero, Nat.zero_mul] at hcard
    exact Nat.card_pos.ne' hcard
  · -- The image of `[n]` on `G` sits inside the sup with `ker f` with both indices finite.
    have hidx : ((f.comp (powMonoidHom n : G →* G)).range).index
        = ((powMonoidHom n : G →* G).range ⊔ f.ker).index * (f.range).index :=
      MonoidHom.index_range_comp_eq _ f
    have h1 : ((powMonoidHom n : G →* G).range ⊔ f.ker).index ≠ 0 := by
      intro hz
      rw [hz, Nat.zero_mul] at hidx
      exact Subgroup.index_ne_zero_of_finite
        (H := (f.comp (powMonoidHom n : G →* G)).range) hidx
    have h2 : ((powMonoidHom n : G →* G).range).relIndex
        ((powMonoidHom n : G →* G).range ⊔ f.ker) ≠ 0 := by
      rw [sup_comm, Subgroup.relIndex_sup_right]
      intro hz
      have hdvd : ((powMonoidHom n : G →* G).range).relIndex f.ker ∣ Nat.card f.ker :=
        Subgroup.relIndex_dvd_card _ _
      rw [hz] at hdvd
      exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.index_eq_card,
      ← Subgroup.relIndex_mul_index (H := (powMonoidHom n : G →* G).range)
        (K := (powMonoidHom n : G →* G).range ⊔ f.ker) le_sup_left]
    exact Nat.mul_ne_zero h2 h1

end IsIsogeny

/-- Two commutative groups are **isogenous** when there is an isogeny between them. -/
@[to_additive IsAddIsogenous /-- Two additive commutative groups are **isogenous** when there is
an isogeny between them. -/]
def IsIsogenous (G H : Type*) [CommGroup G] [CommGroup H] : Prop := ∃ f : G →* H, IsIsogeny f

namespace IsIsogenous

@[to_additive]
theorem refl (G : Type*) [CommGroup G] : IsIsogenous G G :=
  ⟨MonoidHom.id G, IsIsogeny.of_bijective Function.bijective_id⟩

@[to_additive]
theorem trans (h₁ : IsIsogenous G H) (h₂ : IsIsogenous H K) : IsIsogenous G K := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨g.comp f, hg.comp hf⟩

/-- On isogeny-regular groups the isogeny relation is symmetric: the complementary map of an
isogeny is again an isogeny. -/
@[to_additive /-- On isogeny-regular additive groups the isogeny relation is symmetric. -/]
theorem symm [IsIsogenyRegular G] (h : IsIsogenous G H) : IsIsogenous H G := by
  obtain ⟨f, hf⟩ := h
  haveI := hf.isIsogenyRegular_target
  have hpos : 0 < f.kerCard * f.cokerCard := Nat.mul_pos hf.kerCard_pos hf.cokerCard_pos
  obtain ⟨-, f', hf', -, -⟩ := MonoidHom.exists_complement_isIsogeny
    (f := f) (IsIsogenyRegular.isogeny_pow _ hpos) (IsIsogenyRegular.isogeny_pow _ hpos)
  exact ⟨f', hf'⟩

end IsIsogenous

namespace MonoidHom

/-- **The degree of multiplication by `n` is an isogeny invariant.**  If `G` is isogeny-regular
and `f : G →* H` is an isogeny, then the `n`-th power maps on `G` and on `H` have the same
degree. -/
@[to_additive /-- **The degree of multiplication by `n` is an isogeny invariant.** -/]
theorem isogenyDegree_pow_eq_of_isogeny [IsIsogenyRegular G] {f : G →* H} (hf : IsIsogeny f)
    (n : ℕ) (hn : 0 < n) :
    (powMonoidHom n : H →* H).isogenyDegree = (powMonoidHom n : G →* G).isogenyDegree := by
  haveI := hf.isIsogenyRegular_target
  have hGn : IsIsogeny (powMonoidHom n : G →* G) := IsIsogenyRegular.isogeny_pow n hn
  have hHn : IsIsogeny (powMonoidHom n : H →* H) := IsIsogenyRegular.isogeny_pow n hn
  have h1 : ((powMonoidHom n : H →* H).comp f).isogenyDegree
      = (powMonoidHom n : H →* H).isogenyDegree * f.isogenyDegree :=
    MonoidHom.isogenyDegree_comp hf hHn
  have h2 : (f.comp (powMonoidHom n : G →* G)).isogenyDegree
      = f.isogenyDegree * (powMonoidHom n : G →* G).isogenyDegree :=
    MonoidHom.isogenyDegree_comp hGn hf
  rw [IsIsogeny.powMonoidHom_comp f n, h2] at h1
  have hfne : f.isogenyDegree ≠ 0 := (MonoidHom.isogenyDegree_pos hf).ne'
  rw [mul_comm f.isogenyDegree (powMonoidHom n : G →* G).isogenyDegree] at h1
  exact (mul_right_cancel₀ hfne h1).symm

end MonoidHom
