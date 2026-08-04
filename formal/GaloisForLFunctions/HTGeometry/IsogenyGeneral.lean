import GaloisForLFunctions.HTGeometry.IsogenyIndexArithmetic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# General isogenies of commutative groups

An **isogeny** is a homomorphism of commutative groups whose kernel and cokernel are both finite.
The definition is the common generalisation of the two classical special cases:

* a surjective homomorphism with finite kernel — the shape of an isogeny of abelian varieties or
  of algebraic tori over an algebraically closed field;
* an injective homomorphism with finite cokernel — the shape of a finite-index inclusion of
  lattices, i.e. of an isogeny in its contravariant lattice presentation.

The **degree** of an isogeny is the positive rational `|ker f| / |coker f|`.  It is `|ker f|` in
the first case and `1 / [H : im f]` in the second, so the two classical degree conventions are
reconciled exactly by the contravariance of the lattice picture.  The degree is multiplicative on
composites; that is `MonoidHom.isogenyDegree_comp`, and it is what makes the class of isogenies a
graded calculus rather than merely a class of maps.
-/

open Subgroup

variable {G H K : Type*} [CommGroup G] [CommGroup H] [CommGroup K]

namespace MonoidHom

/-- Cardinality of the kernel of a homomorphism; `0` when the kernel is infinite. -/
@[to_additive /-- Cardinality of the kernel of an additive homomorphism; `0` when infinite. -/]
noncomputable def kerCard (f : G →* H) : ℕ := Nat.card f.ker

/-- Cardinality of the cokernel of a homomorphism, read as the index of its range; `0` when the
cokernel is infinite. -/
@[to_additive /-- Cardinality of the cokernel of an additive homomorphism, read as the index of
its range; `0` when infinite. -/]
noncomputable def cokerCard (f : G →* H) : ℕ := (f.range).index

@[to_additive]
theorem kerCard_eq_card (f : G →* H) : f.kerCard = Nat.card f.ker := rfl

@[to_additive]
theorem cokerCard_eq_card_quotient (f : G →* H) : f.cokerCard = Nat.card (H ⧸ f.range) :=
  Subgroup.index_eq_card _

end MonoidHom

/-- A homomorphism of commutative groups is an **isogeny** when both its kernel and its cokernel
are finite.  Surjective maps with finite kernel and injective maps with finite cokernel are the
two extreme cases. -/
@[to_additive IsAddIsogeny /-- A homomorphism of additive commutative groups is an **isogeny**
when both its kernel and its cokernel are finite. -/]
def IsIsogeny (f : G →* H) : Prop := Finite f.ker ∧ Finite (H ⧸ f.range)

namespace IsIsogeny

variable {f : G →* H} {g : H →* K}

@[to_additive]
theorem finite_ker (hf : IsIsogeny f) : Finite f.ker := hf.1

@[to_additive]
theorem finite_coker (hf : IsIsogeny f) : Finite (H ⧸ f.range) := hf.2

@[to_additive]
theorem kerCard_ne_zero (hf : IsIsogeny f) : f.kerCard ≠ 0 := by
  haveI := hf.finite_ker
  exact Nat.card_pos.ne'

@[to_additive]
theorem cokerCard_ne_zero (hf : IsIsogeny f) : f.cokerCard ≠ 0 := by
  haveI := hf.finite_coker
  exact Subgroup.index_ne_zero_of_finite

@[to_additive]
theorem kerCard_pos (hf : IsIsogeny f) : 0 < f.kerCard :=
  Nat.pos_of_ne_zero hf.kerCard_ne_zero

@[to_additive]
theorem cokerCard_pos (hf : IsIsogeny f) : 0 < f.cokerCard :=
  Nat.pos_of_ne_zero hf.cokerCard_ne_zero

/-- A surjective homomorphism with finite kernel is an isogeny. -/
@[to_additive /-- A surjective additive homomorphism with finite kernel is an isogeny. -/]
theorem of_surjective (hs : Function.Surjective f) (hk : Finite f.ker) : IsIsogeny f :=
  ⟨hk, by rw [MonoidHom.range_eq_top_of_surjective f hs]; infer_instance⟩

/-- An injective homomorphism with finite cokernel is an isogeny. -/
@[to_additive /-- An injective additive homomorphism with finite cokernel is an isogeny. -/]
theorem of_injective (hi : Function.Injective f) (hc : Finite (H ⧸ f.range)) : IsIsogeny f :=
  ⟨by rw [(MonoidHom.ker_eq_bot_iff f).2 hi]; infer_instance, hc⟩

/-- A bijective homomorphism is an isogeny. -/
@[to_additive /-- A bijective additive homomorphism is an isogeny. -/]
theorem of_bijective (hb : Function.Bijective f) : IsIsogeny f :=
  of_surjective hb.2 (by rw [(MonoidHom.ker_eq_bot_iff f).2 hb.1]; infer_instance)

/-- The identity is an isogeny. -/
@[to_additive /-- The identity is an isogeny. -/]
theorem id_isogeny : IsIsogeny (MonoidHom.id G) :=
  of_bijective Function.bijective_id

/-- The part of the outer kernel reached by the inner map is finite. -/
@[to_additive]
theorem finite_range_inf_ker (hg : IsIsogeny g) (f : G →* H) :
    Finite (f.range ⊓ g.ker : Subgroup H) := by
  haveI := hg.finite_ker
  exact Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)

/-- Isogenies are closed under composition. -/
@[to_additive /-- Isogenies of additive groups are closed under composition. -/]
theorem comp (hg : IsIsogeny g) (hf : IsIsogeny f) : IsIsogeny (g.comp f) := by
  haveI := hf.finite_ker
  haveI := hg.finite_ker
  haveI := hg.finite_coker
  haveI := hg.finite_range_inf_ker f
  refine ⟨Nat.finite_of_card_ne_zero ?_, Nat.finite_of_card_ne_zero ?_⟩
  · rw [MonoidHom.card_ker_comp f g]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  · rw [← Subgroup.index_eq_card, MonoidHom.index_range_comp_eq f g]
    refine Nat.mul_ne_zero ?_ hg.cokerCard_ne_zero
    intro hzero
    exact hf.cokerCard_ne_zero
      (Nat.eq_zero_of_zero_dvd (hzero ▸ Subgroup.index_dvd_of_le (le_sup_left (b := g.ker))))

end IsIsogeny

namespace MonoidHom

/-- The **degree** of an isogeny: the positive rational `|ker f| / |coker f|`. -/
@[to_additive /-- The **degree** of an additive isogeny: the rational `|ker f| / |coker f|`. -/]
noncomputable def isogenyDegree (f : G →* H) : ℚ := (f.kerCard : ℚ) / (f.cokerCard : ℚ)

@[to_additive]
theorem isogenyDegree_pos {f : G →* H} (hf : IsIsogeny f) : 0 < f.isogenyDegree :=
  div_pos (by exact_mod_cast hf.kerCard_pos) (by exact_mod_cast hf.cokerCard_pos)

/-- For a surjective isogeny the degree is the cardinality of the kernel: the classical degree of
an isogeny of abelian varieties or tori. -/
@[to_additive /-- For a surjective additive isogeny the degree is the kernel cardinality. -/]
theorem isogenyDegree_of_surjective {f : G →* H} (hs : Function.Surjective f) :
    f.isogenyDegree = (f.kerCard : ℚ) := by
  have hc : f.cokerCard = 1 := by
    rw [cokerCard, MonoidHom.range_eq_top_of_surjective f hs, Subgroup.index_top]
  rw [isogenyDegree, hc]
  norm_num

/-- For an injective isogeny the degree is the reciprocal of the index of the image: the lattice
convention, dual to the surjective one. -/
@[to_additive /-- For an injective additive isogeny the degree is the reciprocal index. -/]
theorem isogenyDegree_of_injective {f : G →* H} (hi : Function.Injective f) :
    f.isogenyDegree = 1 / (f.cokerCard : ℚ) := by
  have hk : f.kerCard = 1 := by
    rw [kerCard, (MonoidHom.ker_eq_bot_iff f).2 hi]
    simp
  rw [isogenyDegree, hk]
  norm_num

/-- **Multiplicativity of the isogeny degree.**  The degree is a homomorphism from composition of
isogenies to multiplication of positive rationals. -/
@[to_additive /-- **Multiplicativity of the additive isogeny degree.** -/]
theorem isogenyDegree_comp {f : G →* H} {g : H →* K} (hf : IsIsogeny f) (hg : IsIsogeny g) :
    (g.comp f).isogenyDegree = g.isogenyDegree * f.isogenyDegree := by
  have hidQ : ((g.comp f).kerCard : ℚ) * ((f.cokerCard : ℚ) * (g.cokerCard : ℚ))
      = (f.kerCard : ℚ) * (g.kerCard : ℚ) * ((g.comp f).cokerCard : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ))
      (MonoidHom.card_ker_mul_index_range_comp f g)
  have hcf : ((f.cokerCard : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hf.cokerCard_ne_zero
  have hcg : ((g.cokerCard : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hg.cokerCard_ne_zero
  have hcgf : (((g.comp f).cokerCard : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (hg.comp hf).cokerCard_ne_zero
  rw [isogenyDegree, isogenyDegree, isogenyDegree]
  field_simp
  linear_combination hidQ

@[to_additive]
theorem isogenyDegree_id : (MonoidHom.id G).isogenyDegree = 1 := by
  rw [isogenyDegree_of_surjective Function.surjective_id, kerCard, MonoidHom.ker_id]
  simp

end MonoidHom
