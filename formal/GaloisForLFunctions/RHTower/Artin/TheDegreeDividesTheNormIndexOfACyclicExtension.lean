import GaloisForLFunctions.RHTower.Artin.NormsArePositiveAtTheRamifiedRealPlaces

/-!
# The degree divides the norm index of a cyclic extension

Let `L/K` be a cyclic extension of number fields with group `G = ⟨σ⟩` of order `n`, and `S` a
finite `G`-stable set of primes of `L` outside of which invariant divisors descend. Inside `K^×`
put `𝒩 = N L^×`, `K_S` for the elements that are units outside `S`, `W = K^× ∩ W_k` for a
congruence subgroup at `S`, and `P` for the elements positive at the ramified places.

**The second inequality** (`card_dvd_index_norm_sup_congruence_sup_sUnits`):
`n` divides `[K^× : 𝒩 · (W ∩ P) · K_S]`.

With `V₀ = 𝒩 W`, `V₁ = 𝒩 (W ∩ P)`, `U = V₁ K_S`:
* `[K^× : V₀] = Π_S · h`, with `Π_S` the product of the orders of the stabilizers over the orbits
  on `S` and `h = [N⁻¹ W_k : (σ − 1) L^× · W_k]` (`index_comap_norm_sup_comap_congruence`);
* `[V₀ : V₁] = Π_∞`, the same product over the orbits on the infinite places;
* `[U : V₁] = [K_S : K_S ∩ V₁]` divides `[K_S : N L_S]`, and `n · [K_S : N L_S] = Π_∞ Π_S`
  (`card_mul_relIndex_comap_map_actionNorm_sUnits`).

Hence `[K^× : U] = n · h · [K_S ∩ V₁ : N L_S]` (`dvd_index_sup_of_relIndex`).
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GaloisForLFunctions

/-- Index bookkeeping: for subgroups `V₁ ≤ V₀`, `T` and `M ≤ V₁ ∩ T` with `[A : V₀] = b h`,
`[V₀ : V₁] = a` and `n [T : M] = a b ≠ 0`, one has `[A : V₁ + T] = n h [V₁ ∩ T : M]`. -/
theorem dvd_index_sup_of_relIndex {A : Type*} [AddCommGroup A] {V₀ V₁ T M : AddSubgroup A}
    {n a b h : ℕ} (h01 : V₁ ≤ V₀) (hM : M ≤ V₁ ⊓ T) (h0 : V₀.index = b * h)
    (h1 : V₁.relIndex V₀ = a) (hn : n * M.relIndex T = a * b) (hab : 0 < a * b) :
    n ∣ (V₁ ⊔ T).index := by
  have h2 := AddSubgroup.relIndex_mul_index h01
  have h3 := AddSubgroup.relIndex_mul_index (le_sup_left : V₁ ≤ V₁ ⊔ T)
  rw [AddSubgroup.relIndex_sup_left] at h3
  have h4 := AddSubgroup.relIndex_mul_relIndex M (V₁ ⊓ T) T hM inf_le_right
  rw [AddSubgroup.inf_relIndex_right] at h4
  refine ⟨h * M.relIndex (V₁ ⊓ T), Nat.eq_of_mul_eq_mul_left hab ?_⟩
  calc a * b * (V₁ ⊔ T).index
      = n * M.relIndex T * (V₁ ⊔ T).index := by rw [hn]
    _ = n * M.relIndex (V₁ ⊓ T) * (V₁.relIndex T * (V₁ ⊔ T).index) := by rw [← h4]; ring
    _ = n * M.relIndex (V₁ ⊓ T) * (a * (b * h)) := by rw [h3, ← h2, h1, h0]
    _ = a * b * (n * (h * M.relIndex (V₁ ⊓ T))) := by ring

universe u

variable {K L G : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction infinitePlaceMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))}

omit [NumberField K] [NumberField L] [Fintype G] in
/-- For a generator `σ` of `G`, the kernel of `σ − 1` on `L^×` is `K^×`. -/
theorem ker_actionDiff_fieldUnitsRep {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    (actionDiff (fieldUnitsRep L G) σ).ker = (baseIncl K L).range := by
  refine le_antisymm (fun x hx => mem_range_baseIncl_of_forall_eq (K := K)
    (rep_apply_eq_of_actionDiff_eq_zero hσ (AddMonoidHom.mem_ker.mp hx))) ?_
  rintro _ ⟨c, rfl⟩
  rw [AddMonoidHom.mem_ker, actionDiff_apply, fieldUnitsRep_baseIncl, sub_self]

variable [Fintype S]

omit [NumberField K] in
/-- `[K^× : N L^× · (K^× ∩ W_k)] = Π_ω |G_ω| · [N⁻¹ W_k : (σ − 1) L^× · W_k]`, as an index in
`K^×`; the product is over the orbits of `G` on `S`. -/
theorem index_comap_norm_sup_comap_congruence {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ)
    (k : ℕ) :
    ((actionNorm (fieldUnitsRep L G)).range.comap (baseIncl K L) ⊔
        (congruenceSubgroup K S k).comap (baseIncl K L)).index =
      (∏ ω : MulAction.orbitRel.Quotient G S, Nat.card (MulAction.stabilizer G ω.out)) *
        herbrandQuotIndex (actionNorm (fieldUnitsRep L G)) (actionDiff (fieldUnitsRep L G) σ)
          (congruenceSubgroup K S k) := by
  have e : ((baseIncl K L).range ⊓ congruenceSubgroup K S k).comap (baseIncl K L) =
      (congruenceSubgroup K S k).comap (baseIncl K L) := by
    ext x
    exact ⟨fun h => h.2, fun h => ⟨⟨x, rfl⟩, h⟩⟩
  rw [← e, AddSubgroup.comap_sup_eq_of_le_range (baseIncl K L)
    range_actionNorm_le_range_baseIncl inf_le_left, AddSubgroup.index_comap]
  exact relIndex_range_actionNorm_sup_range_baseIncl hσ k

omit [NumberField K] in
/-- **The norm index of the `S`-units** in `K^×`: `n · [K_S : N L_S] = Π_ω |G_ω|`, the product
over the orbits of `G` on the infinite places of `L` and on `S`. -/
theorem card_mul_relIndex_comap_map_actionNorm_sUnits (hS : InvariantDivisorsDescend L G S)
    {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    Fintype.card G *
        (((sUnits L G S).map (actionNorm (fieldUnitsRep L G))).comap (baseIncl K L)).relIndex
          ((sUnits L G S).comap (baseIncl K L)) =
      (∏ ω : MulAction.orbitRel.Quotient G (InfinitePlace L),
          Nat.card (MulAction.stabilizer G ω.out)) *
        ∏ ω : MulAction.orbitRel.Quotient G S, Nat.card (MulAction.stabilizer G ω.out) := by
  haveI : FaithfulSMul G L := IsGaloisGroup.faithful K
  rw [← card_mul_herbrandSubIndex_sUnits_eq hS hσ, herbrandSubIndex,
    ker_actionDiff_fieldUnitsRep (K := K) hσ, AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq]

/-- **The second inequality for a cyclic extension**: the degree `n = |G|` divides
`[K^× : N L^× · (K^× ∩ W_k ∩ P) · K_S]`, with `W_k` a congruence subgroup at `S`, `P` the
elements positive at the ramified places and `K_S` the elements that are units outside `S`. -/
theorem card_dvd_index_norm_sup_congruence_sup_sUnits (hS : InvariantDivisorsDescend L G S)
    {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (k : ℕ) :
    Fintype.card G ∣
      ((actionNorm (fieldUnitsRep L G)).range.comap (baseIncl K L) ⊔
        (congruenceSubgroup K S k).comap (baseIncl K L) ⊓ positiveAtRamified K L ⊔
          (sUnits L G S).comap (baseIncl K L)).index := by
  -- norms of `S`-units are `S`-units
  have hNS : (sUnits L G S).map (actionNorm (fieldUnitsRep L G)) ≤ sUnits L G S := by
    rintro _ ⟨a, ha, rfl⟩
    exact actionNorm_mem (fun τ x hx => fieldUnitsRep_mem_sUnits L G S τ x hx) ha
  exact dvd_index_sup_of_relIndex
    (M := ((sUnits L G S).map (actionNorm (fieldUnitsRep L G))).comap (baseIncl K L))
    (sup_le_sup_left inf_le_left _)
    (le_inf (le_sup_of_le_left (AddSubgroup.comap_mono (AddSubgroup.map_le_range _ _)))
      (AddSubgroup.comap_mono hNS))
    (index_comap_norm_sup_comap_congruence hσ k) (relIndex_norm_sup_congruence_inf_positive k)
    (card_mul_relIndex_comap_map_actionNorm_sUnits hS hσ)
    (Nat.mul_pos (Finset.prod_pos fun _ _ => Nat.card_pos)
      (Finset.prod_pos fun _ _ => Nat.card_pos))

end GaloisForLFunctions
