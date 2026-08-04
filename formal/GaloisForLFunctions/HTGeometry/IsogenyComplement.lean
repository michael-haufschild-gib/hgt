import GaloisForLFunctions.HTGeometry.IsogenyGeneral
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# The complementary isogeny

Every isogeny `f : G →* H` of commutative groups admits a complementary homomorphism
`f' : H →* G` with

`f' ∘ f = [n]` on `G` and `f ∘ f' = [n]` on `H`, where `n = |ker f| · |coker f|`.

No divisibility, torsion-freeness or finiteness hypothesis on `G` or `H` is needed: the
construction only uses that a finite group is killed by its own order.  The map is built from the
canonical factorisation `f = ι ∘ π` through `G ⧸ ker f`, complementing the surjection `π` by
Lagrange on `ker f` and the injection `ι` by Lagrange on `coker f`.

For abelian varieties this is the statement that the dual isogeny satisfies `f̂ ∘ f = [deg f]`;
for lattices it is the adjugate identity `adj(M) · M = det(M) · I`.  Both are shadows of the same
elementary group-theoretic fact.
-/

open Subgroup QuotientGroup

variable {G H : Type*} [CommGroup G] [CommGroup H]

namespace MonoidHom

/-- A finite kernel is killed by its own cardinality. -/
@[to_additive /-- A finite kernel is killed by its own cardinality. -/]
theorem ker_le_ker_powMonoidHom_kerCard (f : G →* H) :
    f.ker ≤ (powMonoidHom f.kerCard : G →* G).ker := by
  intro x hx
  have h : (⟨x, hx⟩ : f.ker) ^ Nat.card f.ker = 1 := pow_card_eq_one'
  have hx' : x ^ Nat.card f.ker = 1 := by
    have := congrArg (Subgroup.subtype f.ker) h
    simpa using this
  simpa [MonoidHom.mem_ker, kerCard] using hx'

/-- A finite cokernel forces the corresponding power of every element into the image. -/
@[to_additive /-- A finite cokernel forces the corresponding multiple of every element into the
image. -/]
theorem pow_cokerCard_mem_range (f : G →* H) (y : H) : y ^ f.cokerCard ∈ f.range := by
  have h : ((y : H) : H ⧸ f.range) ^ Nat.card (H ⧸ f.range) = 1 := pow_card_eq_one'
  rw [← QuotientGroup.mk_pow] at h
  have hmem := (QuotientGroup.eq_one_iff _).1 h
  rwa [cokerCard_eq_card_quotient]

end MonoidHom

namespace MonoidHom

/-- **Complementary map.**  For every homomorphism `f` of commutative groups there is a
homomorphism `f'` in the opposite direction with `f' ∘ f` and `f ∘ f'` both equal to the power map
of exponent `|ker f| · |coker f|`.  No finiteness is assumed; when a kernel or cokernel is
infinite the exponent is `0` and the statement degenerates to the trivial homomorphism. -/
@[to_additive /-- **Complementary map** for additive commutative groups. -/]
theorem exists_complement (f : G →* H) :
    ∃ f' : H →* G,
      f'.comp f = powMonoidHom (f.kerCard * f.cokerCard) ∧
      f.comp f' = powMonoidHom (f.kerCard * f.cokerCard) := by
  -- The canonical factorisation of `f` through `G ⧸ ker f`.
  let ι : G ⧸ f.ker →* H := QuotientGroup.kerLift f
  have hιinj : Function.Injective ι := QuotientGroup.kerLift_injective f
  have hfac : ∀ x : G, ι (x : G ⧸ f.ker) = f x := fun x => QuotientGroup.kerLift_mk f x
  -- Complement of the surjection: Lagrange on `ker f`.
  let π' : G ⧸ f.ker →* G :=
    QuotientGroup.lift f.ker (powMonoidHom f.kerCard) (MonoidHom.ker_le_ker_powMonoidHom_kerCard f)
  have hπ' : ∀ x : G, π' (x : G ⧸ f.ker) = x ^ f.kerCard := fun x =>
    QuotientGroup.lift_mk' _ _ x
  have hπ'' : ∀ q : G ⧸ f.ker, ((π' q : G) : G ⧸ f.ker) = q ^ f.kerCard := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => rw [hπ' x, QuotientGroup.mk_pow]
  -- Complement of the injection: Lagrange on `coker f`.
  have hmem : ∀ y : H, y ^ f.cokerCard ∈ ι.range := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.pow_cokerCard_mem_range f y
    exact ⟨(x : G ⧸ f.ker), by rw [hfac x, hx]⟩
  let ι' : H →* G ⧸ f.ker :=
    ((MonoidHom.ofInjective hιinj).symm : ι.range →* G ⧸ f.ker).comp
      (MonoidHom.codRestrict (powMonoidHom f.cokerCard) ι.range hmem)
  have hι' : ∀ y : H, ι (ι' y) = y ^ f.cokerCard := fun y =>
    MonoidHom.apply_ofInjective_symm hιinj ⟨y ^ f.cokerCard, hmem y⟩
  have hι'' : ∀ q : G ⧸ f.ker, ι' (ι q) = q ^ f.cokerCard := by
    intro q
    refine hιinj ?_
    rw [hι' (ι q), map_pow]
  -- The complementary map and the two identities.
  refine ⟨π'.comp ι', ?_, ?_⟩
  · ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
    rw [← hfac x, hι'' (x : G ⧸ f.ker), map_pow, hπ' x, ← pow_mul]
  · ext y
    simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
    rw [← hfac (π' (ι' y)), hπ'' (ι' y), map_pow, hι' y, ← pow_mul,
      mul_comm f.cokerCard f.kerCard]

end MonoidHom

namespace IsIsogeny

variable {f : G →* H}

/-- **Complementary isogeny.**  For an isogeny the exponent `|ker f| · |coker f|` of the
complementary identities is positive. -/
@[to_additive /-- **Complementary isogeny** for additive commutative groups, with positive
exponent. -/]
theorem exists_complement (hf : IsIsogeny f) :
    ∃ f' : H →* G, 0 < f.kerCard * f.cokerCard ∧
      f'.comp f = powMonoidHom (f.kerCard * f.cokerCard) ∧
      f.comp f' = powMonoidHom (f.kerCard * f.cokerCard) := by
  obtain ⟨f', h1, h2⟩ := MonoidHom.exists_complement f
  exact ⟨f', Nat.mul_pos hf.kerCard_pos hf.cokerCard_pos, h1, h2⟩

end IsIsogeny

namespace MonoidHom

/-- **Two-sided isogeny criterion.**  If the power map of exponent `|ker f| · |coker f|` is an
isogeny on both source and target, then `f` and its complementary map are both isogenies. -/
@[to_additive /-- **Two-sided isogeny criterion** for additive commutative groups. -/]
theorem exists_complement_isIsogeny {f : G →* H}
    (hG : IsIsogeny (powMonoidHom (f.kerCard * f.cokerCard) : G →* G))
    (hH : IsIsogeny (powMonoidHom (f.kerCard * f.cokerCard) : H →* H)) :
    IsIsogeny f ∧ ∃ f' : H →* G, IsIsogeny f' ∧
      f'.comp f = powMonoidHom (f.kerCard * f.cokerCard) ∧
      f.comp f' = powMonoidHom (f.kerCard * f.cokerCard) := by
  obtain ⟨f', h1, h2⟩ := MonoidHom.exists_complement f
  haveI hkerG : Finite (f'.comp f).ker := by rw [h1]; exact hG.finite_ker
  haveI hkerH : Finite (f.comp f').ker := by rw [h2]; exact hH.finite_ker
  haveI hcokG : Finite (G ⧸ (f'.comp f).range) := by rw [h1]; exact hG.finite_coker
  haveI hcokH : Finite (H ⧸ (f.comp f').range) := by rw [h2]; exact hH.finite_coker
  have hkf : Finite f.ker := by
    have hle : f.ker ≤ (f'.comp f).ker := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      simp [hx]
    exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
  have hkf' : Finite f'.ker := by
    have hle : f'.ker ≤ (f.comp f').ker := by
      intro y hy
      rw [MonoidHom.mem_ker] at hy ⊢
      simp [hy]
    exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
  have hcf : Finite (H ⧸ f.range) := by
    have hle : (f.comp f').range ≤ f.range := by
      rw [MonoidHom.range_comp]
      exact Subgroup.map_le_range f f'.range
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.index_eq_card]
    intro hzero
    exact Subgroup.index_ne_zero_of_finite (H := (f.comp f').range)
      (Nat.eq_zero_of_zero_dvd (hzero ▸ Subgroup.index_dvd_of_le hle))
  have hcf' : Finite (G ⧸ f'.range) := by
    have hle : (f'.comp f).range ≤ f'.range := by
      rw [MonoidHom.range_comp]
      exact Subgroup.map_le_range f' f.range
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.index_eq_card]
    intro hzero
    exact Subgroup.index_ne_zero_of_finite (H := (f'.comp f).range)
      (Nat.eq_zero_of_zero_dvd (hzero ▸ Subgroup.index_dvd_of_le hle))
  exact ⟨⟨hkf, hcf⟩, f', ⟨hkf', hcf'⟩, h1, h2⟩

end MonoidHom
