import GaloisForLFunctions.RHTower.Artin.UnitsPermutedByTheGaloisGroupHaveFiniteIndex

/-!
# The Herbrand quotient of the unit group

Let a finite cyclic group `G = ⟨σ⟩` act on a number field `L`, `E` the group of units of `L`
and `X` the set of infinite places of `L`. With `f = σ − 1` and `g` the norm,

`|G| · [E^G : N E] · h¹(ℤ^X) = [(ℤ^X)^G : N ℤ^X] · h¹(E)`,

where `h¹ = [ker g : im f]` (`card_mul_herbrandIndex_units`). So the Herbrand quotient of `E` is
that of the permutation module `ℤ^X` divided by `|G|`, and

`|G| · [E^G : N E] ≤ Π_ω |G_ω| · h¹(E)`,

the product over the orbits `ω` of `G` on `X` of the orders of the stabilizers
(`card_mul_herbrandIndex_units_le`). For `K = L^G` this is
`[L : K] · [E_K : N E_L] ≤ 2^ρ · |H¹(G, E_L)|`, `ρ` the number of real places of `K` that
become complex in `L`.

Proof. Let `B ⊂ ℤ^X` be the vectors of coordinate sum zero. The sum `ℤ^X → ℤ` is equivariant
for the trivial action on `ℤ`, whose Herbrand indices are `|G|` and `1`; so the Herbrand
quotient of `B` is that of `ℤ^X` divided by `|G|`. The map `y ↦ Π_w η_w^{y_w}` embeds `B`
equivariantly into `E` with finite cokernel, so `B` and `E` have the same Herbrand quotient.
-/

open scoped Classical NumberField
open NumberField

noncomputable section

namespace GaloisForLFunctions

attribute [local instance] infinitePlaceMulAction

section Permutation

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]

/-- The sum of the coordinates is invariant under the permutation action. -/
theorem coordSum_permRep (τ : G) (y : X → ℤ) :
    coordSum X (permRep G X τ y) = (1 : G →* AddMonoid.End ℤ) τ (coordSum X y) :=
  Fintype.sum_bijective (τ⁻¹ • ·) (MulAction.bijective τ⁻¹) _ _ fun _ => rfl

end Permutation

section Units

variable (L : Type*) [Field L] [NumberField L] (G : Type*) [Group G] [Fintype G]
  [MulSemiringAction G L]

/-- **The Herbrand quotient of the unit group**:
`|G| · [E^G : N E] · h¹(ℤ^X) = [(ℤ^X)^G : N ℤ^X] · h¹(E)` for the units `E` and the infinite
places `X` of `L`. -/
theorem card_mul_herbrandIndex_units {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    Fintype.card G *
          herbrandIndex (actionDiff (unitsRep L G) σ) (actionNorm (unitsRep L G)) *
        herbrandIndex (actionNorm (permRep G (InfinitePlace L)))
          (actionDiff (permRep G (InfinitePlace L)) σ) =
      herbrandIndex (actionDiff (permRep G (InfinitePlace L)) σ)
          (actionNorm (permRep G (InfinitePlace L))) *
        herbrandIndex (actionNorm (unitsRep L G)) (actionDiff (unitsRep L G) σ) := by
  set ρY := permRep G (InfinitePlace L)
  set ρE := unitsRep L G
  set ρZ : G →* AddMonoid.End ℤ := 1
  set s := coordSum (InfinitePlace L)
  set φ := artinUnitHom L G
  have hs : ∀ (τ : G) (y : InfinitePlace L → ℤ), s (ρY τ y) = ρZ τ (s y) := coordSum_permRep
  have hsf := map_actionDiff s hs σ
  have hsg := map_actionNorm s hs
  have hφf := map_actionDiff φ (artinUnitHom_permRep L G) σ
  have hφg := map_actionNorm φ (artinUnitHom_permRep L G)
  have fgY := actionDiff_actionNorm ρY σ
  have gfY := actionNorm_actionDiff ρY σ
  have fgE := actionDiff_actionNorm ρE σ
  have gfE := actionNorm_actionDiff ρE σ
  -- the vectors of sum zero form a stable subgroup
  have hBf : ∀ y ∈ s.ker, actionDiff ρY σ y ∈ s.ker := fun y hy => by
    rw [AddMonoidHom.mem_ker] at hy ⊢
    rw [hsf, hy, map_zero]
  have hBg : ∀ y ∈ s.ker, actionNorm ρY y ∈ s.ker := fun y hy => by
    rw [AddMonoidHom.mem_ker] at hy ⊢
    rw [hsg, hy, map_zero]
  -- `0 → B → ℤ^X → ℤ → 0`
  have hsurj : s.range = ⊤ := AddMonoidHom.range_eq_top.mpr fun n => by
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace L))
    refine ⟨Pi.single w₀ n, ?_⟩
    show ∑ w, (Pi.single w₀ n : InfinitePlace L → ℤ) w = n
    rw [Finset.sum_pi_single' w₀ n Finset.univ, if_pos (Finset.mem_univ _)]
  have h1 := herbrandSubIndex_inf_ker_mul s hsf hsg fgY gfY (C := ⊤)
    (fun _ _ => AddSubgroup.mem_top _) fun _ _ => AddSubgroup.mem_top _
  rw [top_inf_eq, ← AddMonoidHom.range_eq_map, hsurj, herbrandSubIndex_top, herbrandSubIndex_top,
    herbrandSubIndex_top, herbrandSubIndex_top, (herbrandIndex_int_trivial ρZ (fun _ _ => rfl) σ).1,
    (herbrandIndex_int_trivial ρZ (fun _ _ => rfl) σ).2] at h1
  -- `B` embeds into the units
  have hbot : s.ker ⊓ φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := AddSubgroup.mem_inf.mp hy
    exact eq_zero_of_artinUnitHom_eq_zero L G (AddMonoidHom.mem_ker.mp hy1)
      (AddMonoidHom.mem_ker.mp hy2)
  have h2 := herbrandSubIndex_inf_ker_mul φ hφf hφg fgY gfY hBf hBg
  rw [hbot, herbrandSubIndex_bot, herbrandSubIndex_bot, one_mul, one_mul] at h2
  -- the image has finite index in the units
  have hIf : ∀ u ∈ s.ker.map φ, actionDiff ρE σ u ∈ s.ker.map φ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hBf y hy, hφf y⟩
  have hIg : ∀ u ∈ s.ker.map φ, actionNorm ρE u ∈ s.ker.map φ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hBg y hy, hφg y⟩
  have hI := index_map_artinUnitHom_ne_zero L G
  have h3 := herbrandSubIndex_mul_of_index_ne_zero fgE gfE hIf hIg hI
  have he' : herbrandIndex (actionNorm ρE) (actionDiff ρE σ) ≠ 0 :=
    herbrandIndex_actionNorm_ne_zero hσ
  have hi : herbrandSubIndex (actionDiff ρE σ) (actionNorm ρE) (s.ker.map φ) ≠ 0 :=
    (herbrandSubIndex_ne_zero_iff_of_index_ne_zero fgE gfE hIf hIg hI).mpr
      (herbrandIndex_actionDiff_ne_zero hσ)
  have hi' : herbrandSubIndex (actionNorm ρE) (actionDiff ρE σ) (s.ker.map φ) ≠ 0 :=
    (herbrandSubIndex_ne_zero_iff_of_index_ne_zero gfE fgE hIg hIf hI).mpr he'
  have ha : herbrandSubIndex (actionDiff ρY σ) (actionNorm ρY) s.ker ≠ 0 := by
    refine herbrandSubIndex_ne_zero_of_inf_ker φ hφf hφg fgY hBf hBg ?_ hi
    rw [hbot, herbrandSubIndex_bot]
    exact one_ne_zero
  -- eliminate the indices of `B` and of its image
  have key : ∀ a a' i i' e e' y y' n : ℕ, a * n * y' = a' * 1 * y → i * a' = i' * a →
      i * e' = i' * e → a ≠ 0 → i' ≠ 0 → n * e * y' = y * e' := by
    intro a a' i i' e e' y y' n k1 k2 k3 ka ki'
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero ka ki'))
    calc a * i' * (n * e * y') = a * n * y' * (i' * e) := by ring
      _ = a' * 1 * y * (i * e') := by rw [k1, k3]
      _ = i * a' * (y * e') := by ring
      _ = i' * a * (y * e') := by rw [k2]
      _ = a * i' * (y * e') := by ring
  exact key _ _ _ _ _ _ _ _ _ h1 h2 h3 ha hi'

/-- `|G| · [E^G : N E] ≤ Π_ω |G_ω| · h¹(E)`: the product over the orbits of `G` on the infinite
places of `L` of the orders of the stabilizers. -/
theorem card_mul_herbrandIndex_units_le {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    Fintype.card G *
        herbrandIndex (actionDiff (unitsRep L G) σ) (actionNorm (unitsRep L G)) ≤
      (∏ ω : MulAction.orbitRel.Quotient G (InfinitePlace L),
          Nat.card (MulAction.stabilizer G ω.out)) *
        herbrandIndex (actionNorm (unitsRep L G)) (actionDiff (unitsRep L G) σ) := by
  have h := card_mul_herbrandIndex_units L G hσ
  have hy' : 1 ≤ herbrandIndex (actionNorm (permRep G (InfinitePlace L)))
      (actionDiff (permRep G (InfinitePlace L)) σ) :=
    Nat.one_le_iff_ne_zero.mpr (herbrandIndex_actionNorm_ne_zero hσ)
  calc Fintype.card G *
        herbrandIndex (actionDiff (unitsRep L G) σ) (actionNorm (unitsRep L G))
      ≤ Fintype.card G *
          herbrandIndex (actionDiff (unitsRep L G) σ) (actionNorm (unitsRep L G)) *
        herbrandIndex (actionNorm (permRep G (InfinitePlace L)))
          (actionDiff (permRep G (InfinitePlace L)) σ) := Nat.le_mul_of_pos_right _ hy'
    _ = _ := h
    _ ≤ _ := Nat.mul_le_mul_right _ (herbrandIndex_permRep_le hσ)

end Units

end GaloisForLFunctions
