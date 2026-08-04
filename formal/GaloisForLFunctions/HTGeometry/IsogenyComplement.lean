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
  have := (QuotientGroup.eq_one_iff _).1 h
  rwa [cokerCard_eq_card_quotient]

end MonoidHom

namespace IsIsogeny

variable {f : G →* H}

/-- **Complementary isogeny.**  For any isogeny `f` of commutative groups there is a homomorphism
`f'` in the opposite direction with `f' ∘ f` and `f ∘ f'` both equal to the power map of exponent
`|ker f| · |coker f|`. -/
@[to_additive /-- **Complementary isogeny** for additive commutative groups. -/]
theorem exists_complement (hf : IsIsogeny f) :
    ∃ f' : H →* G,
      f'.comp f = powMonoidHom (f.kerCard * f.cokerCard) ∧
      f.comp f' = powMonoidHom (f.kerCard * f.cokerCard) := by
  haveI := hf.finite_ker
  haveI := hf.finite_coker
  -- The canonical factorisation `f = ι ∘ π` through `G ⧸ ker f`.
  let π : G →* G ⧸ f.ker := QuotientGroup.mk' f.ker
  let ι : G ⧸ f.ker →* H := QuotientGroup.kerLift f
  have hιinj : Function.Injective ι := QuotientGroup.kerLift_injective f
  have hfac : ∀ x : G, ι (π x) = f x := fun x => QuotientGroup.kerLift_mk f x
  -- Complement of the surjection: Lagrange on `ker f`.
  let π' : G ⧸ f.ker →* G :=
    QuotientGroup.lift f.ker (powMonoidHom f.kerCard) (MonoidHom.ker_le_ker_powMonoidHom_kerCard f)
  have hπ' : ∀ x : G, π' (π x) = x ^ f.kerCard := fun x =>
    QuotientGroup.lift_mk' _ _ x
  have hπ'' : ∀ q : G ⧸ f.ker, π (π' q) = q ^ f.kerCard := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => rw [hπ' x, ← map_pow]
  -- Complement of the injection: Lagrange on `coker f`.
  have hmem : ∀ y : H, (powMonoidHom f.cokerCard) y ∈ ι.range := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.pow_cokerCard_mem_range f y
    exact ⟨π x, by rw [hfac x, hx]⟩
  let ι' : H →* G ⧸ f.ker :=
    ((MonoidHom.ofInjective hιinj).symm : ι.range →* G ⧸ f.ker).comp
      (MonoidHom.codRestrict (powMonoidHom f.cokerCard) ι.range hmem)
  have hι' : ∀ y : H, ι (ι' y) = y ^ f.cokerCard := by
    intro y
    exact congrArg Subtype.val (MonoidHom.apply_ofInjective_symm hιinj
      ⟨(powMonoidHom f.cokerCard) y, hmem y⟩)
  have hι'' : ∀ q : G ⧸ f.ker, ι' (ι q) = q ^ f.cokerCard := by
    intro q
    refine hιinj ?_
    rw [hι' (ι q), ← map_pow]
  -- The complementary map and the two identities.
  refine ⟨π'.comp ι', ?_, ?_⟩
  · ext x
    have h1 : ι' (f x) = (π x) ^ f.cokerCard := by rw [← hfac x, hι'' (π x)]
    simp only [MonoidHom.coe_comp, Function.comp_apply, h1, map_pow, hπ' x, powMonoidHom_apply]
    rw [← pow_mul]
  · ext y
    have h1 : π (π' (ι' y)) = (ι' y) ^ f.kerCard := hπ'' (ι' y)
    have h2 : ι ((ι' y) ^ f.kerCard) = (y ^ f.cokerCard) ^ f.kerCard := by
      rw [map_pow, hι' y]
    simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
    rw [← hfac (π' (ι' y)), h1, h2, ← pow_mul, mul_comm f.cokerCard f.kerCard]

/-- The complementary map of an isogeny is itself an isogeny as soon as the corresponding power
maps on source and target are isogenies. -/
@[to_additive /-- The complementary map of an additive isogeny is an isogeny once the
corresponding multiplication maps are. -/]
theorem exists_complement_isIsogeny (hf : IsIsogeny f)
    (hG : IsIsogeny (powMonoidHom (f.kerCard * f.cokerCard) : G →* G))
    (hH : IsIsogeny (powMonoidHom (f.kerCard * f.cokerCard) : H →* H)) :
    ∃ f' : H →* G, IsIsogeny f' ∧
      f'.comp f = powMonoidHom (f.kerCard * f.cokerCard) ∧
      f.comp f' = powMonoidHom (f.kerCard * f.cokerCard) := by
  obtain ⟨f', h1, h2⟩ := hf.exists_complement
  refine ⟨f', ⟨?_, ?_⟩, h1, h2⟩
  · haveI := hH.finite_ker
    have hle : f'.ker ≤ (powMonoidHom (f.kerCard * f.cokerCard) : H →* H).ker := by
      rw [← h2, ← MonoidHom.comap_ker]
      exact Subgroup.ker_le_comap f' f.ker |>.trans (Subgroup.comap_mono (by
        intro z hz
        simp only [MonoidHom.mem_ker] at hz ⊢
        rw [hz, map_one]))
    exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
  · haveI := hG.finite_coker
    have hle : (powMonoidHom (f.kerCard * f.cokerCard) : G →* G).range ≤ f'.range := by
      rw [← h1, MonoidHom.range_comp]
      exact Subgroup.map_le_range f' f.range
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.index_eq_card]
    intro hzero
    exact hG.cokerCard_ne_zero
      (Nat.eq_zero_of_zero_dvd (hzero ▸ Subgroup.index_dvd_of_le hle))

end IsIsogeny
