/-
# Proper discontinuity restricts to subgroups

A reusable topology lemma for the modular-curve covering lane (`#34/#35`): if a group `G` acts properly
discontinuously on `T`, then every subgroup `H ≤ G` does too. Proven directly from the definition
(`finite_disjoint_inter_image`): the finite set `{g : G | (g•K ∩ L).Nonempty}` contains the coercion-image
of `{h : H | (h•K ∩ L).Nonempty}`, so the latter is finite. This feeds the quotient-covering
`ℍ → ℍ/Γ(2)` (mathlib `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`) from the ambient
modular action — the route by which `λ : ℍ → ℂ∖{0,1}` becomes a covering, hence the three-value-Montel lift.
-/
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.GroupTheory.GroupAction.Basic

namespace Bottcher

/-- **Proper discontinuity transports along an injective equivariant map.** If `H` acts properly
discontinuously on `T`, `f : G → H` is injective, and the `G`-action factors through `f`
(`g • x = f g • x`), then `G` acts properly discontinuously. Generalises the subgroup case — the tool to
push mathlib's `SL(2,ℝ)`-discrete-subgroup proper discontinuity on `ℍ` down to `SL(2,ℤ)` and `Γ(2)`. -/
theorem properlyDiscontinuousSMul_of_injective {G H T : Type*} [TopologicalSpace T]
    [SMul G T] [SMul H T] [ProperlyDiscontinuousSMul H T] (f : G → H)
    (hf : Function.Injective f) (hcompat : ∀ (g : G) (x : T), g • x = f g • x) :
    ProperlyDiscontinuousSMul G T := by
  constructor
  intro K L hK hL
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := H) (T := T) hK hL
  apply Set.Finite.of_finite_image (f := f) _ hf.injOn
  apply hfin.subset
  rintro h ⟨g, hg, rfl⟩
  obtain ⟨w, ⟨v, hv, hvw⟩, hwL⟩ := hg
  exact ⟨w, ⟨v, hv, (hcompat g v).symm.trans hvw⟩, hwL⟩

/-- **Proper discontinuity restricts to subgroups.** If `G` acts properly discontinuously on `T`, any
subgroup `H ≤ G` does too. -/
theorem properlyDiscontinuousSMul_subgroup {G T : Type*} [Group G] [TopologicalSpace T]
    [MulAction G T] [ProperlyDiscontinuousSMul G T] (H : Subgroup G) :
    ProperlyDiscontinuousSMul H T := by
  exact properlyDiscontinuousSMul_of_injective (Subtype.val : H → G) Subtype.val_injective (by
    intro h x
    rfl)

/-- **Proper discontinuity transports along a surjective equivariant map.** If `G` acts properly
discontinuously on `T`, `f : G → H` is surjective, and the `H`-action is the pushforward of the
`G`-action (`f g • x = g • x`), then `H` acts properly discontinuously. The tool to push proper
discontinuity from a group down to a **quotient** group `H = G/N` (where `N` acts trivially): the
finite set `{g | (g•K ∩ L).Nonempty}` maps onto `{h | (h•K ∩ L).Nonempty}` under the surjection `f`,
and the image of a finite set is finite. -/
theorem properlyDiscontinuousSMul_of_surjective {G H T : Type*} [TopologicalSpace T]
    [SMul G T] [SMul H T] [ProperlyDiscontinuousSMul G T] (f : G → H)
    (hf : Function.Surjective f) (hcompat : ∀ (g : G) (x : T), f g • x = g • x) :
    ProperlyDiscontinuousSMul H T := by
  constructor
  intro K L hK hL
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) (T := T) hK hL
  apply Set.Finite.subset (hfin.image f)
  intro h hmem
  obtain ⟨g, rfl⟩ := hf h
  obtain ⟨w, ⟨v, hv, hvw⟩, hwL⟩ := hmem
  exact ⟨g, ⟨w, ⟨v, hv, (hcompat g v).symm.trans hvw⟩, hwL⟩, rfl⟩

end Bottcher
