import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring

/-!
# Kernel and cokernel arithmetic for composable homomorphisms

For a composable pair of homomorphisms of commutative groups the four basic invariants — the
cardinalities of the two kernels and the indices of the two ranges — are tied to those of the
composite by a single identity,

`|ker (g ∘ f)| · [H : im f] · [K : im g] = |ker f| · |ker g| · [K : im (g ∘ f)]`.

This is the counting shadow of the six-term exact sequence

`1 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 1`,

obtained here without any exactness machinery: only Lagrange's theorem in relative form, the
second isomorphism theorem in its index form, and the behaviour of indices under images and
preimages.  Every statement holds unconditionally, with the convention that `Nat.card` and
`Subgroup.index` return `0` on infinite objects.
-/

namespace Subgroup

variable {A : Type*} [Group A]

/-- Relative Lagrange theorem: the cardinality of a subgroup times its index inside a larger
subgroup recovers the cardinality of the larger subgroup. -/
@[to_additive /-- Relative Lagrange theorem for additive subgroups. -/]
theorem card_mul_relIndex {P Q : Subgroup A} (h : P ≤ Q) :
    Nat.card P * P.relIndex Q = Nat.card Q := by
  have h1 := Subgroup.card_mul_index (P.subgroupOf Q)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  exact h1

end Subgroup

namespace MonoidHom

variable {G H K : Type*} [CommGroup G] [CommGroup H] [CommGroup K]

/-- The kernel of a composite is an extension of the inner kernel by the part of the outer kernel
that is actually reached.  Counting the extension gives the product formula. -/
@[to_additive /-- The kernel of a composite of additive homomorphisms is an extension of the inner
kernel by the reached part of the outer kernel. -/]
theorem card_ker_comp (f : G →* H) (g : H →* K) :
    Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card (f.range ⊓ g.ker : Subgroup H) := by
  have h1 : Nat.card f.ker * f.ker.relIndex (g.ker.comap f) = Nat.card (g.ker.comap f) :=
    Subgroup.card_mul_relIndex (Subgroup.ker_le_comap f g.ker)
  have h3 : f.ker.relIndex (g.ker.comap f) = Nat.card ((g.ker.comap f).map f) :=
    Subgroup.relIndex_ker (K := g.ker.comap f) f
  have h4 : (g.ker.comap f).map f = f.range ⊓ g.ker := by rw [Subgroup.map_comap_eq]
  rw [← MonoidHom.comap_ker g f, ← h1, h3, h4]

/-- Inside the range of the outer map, the range of the composite has the index that the inner
range together with the outer kernel has upstairs. -/
@[to_additive /-- Inside the range of the outer additive map, the range of the composite has the
index that the inner range together with the outer kernel has upstairs. -/]
theorem relIndex_range_comp (f : G →* H) (g : H →* K) :
    ((g.comp f).range).relIndex g.range = (f.range ⊔ g.ker).index := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_map g, Subgroup.relIndex_map_map,
    top_sup_eq, Subgroup.relIndex_top_right]

/-- **Kernel–cokernel identity for a composite.**  For composable homomorphisms of commutative
groups the kernel cardinalities and range indices satisfy

`|ker (g ∘ f)| · ([H : im f] · [K : im g]) = |ker f| · |ker g| · [K : im (g ∘ f)]`.

No finiteness is assumed: both sides are read with the `0` conventions for infinite cardinalities
and indices. -/
@[to_additive /-- **Kernel–cokernel identity for a composite of additive homomorphisms.** -/]
theorem card_ker_mul_index_range_comp (f : G →* H) (g : H →* K) :
    Nat.card (g.comp f).ker * ((f.range).index * (g.range).index)
      = Nat.card f.ker * Nat.card g.ker * ((g.comp f).range).index := by
  have hstep : (f.range).relIndex (f.range ⊔ g.ker) = (f.range ⊓ g.ker).relIndex g.ker := by
    rw [Subgroup.inf_relIndex_right, sup_comm]
    exact Subgroup.relIndex_sup_right g.ker f.range
  have hR : (f.range ⊓ g.ker).relIndex g.ker * (f.range ⊔ g.ker).index = (f.range).index := by
    rw [← hstep]; exact Subgroup.relIndex_mul_index le_sup_left
  have hP : (f.range ⊔ g.ker).index * (g.range).index = ((g.comp f).range).index := by
    rw [← relIndex_range_comp f g]
    exact Subgroup.relIndex_mul_index (by
      rw [MonoidHom.range_comp]
      exact Subgroup.map_le_range g f.range)
  have hInf : Nat.card (f.range ⊓ g.ker : Subgroup H) * ((f.range ⊓ g.ker).relIndex g.ker)
      = Nat.card g.ker := Subgroup.card_mul_relIndex inf_le_right
  calc Nat.card (g.comp f).ker * ((f.range).index * (g.range).index)
      = (Nat.card f.ker * Nat.card (f.range ⊓ g.ker : Subgroup H))
          * (((f.range ⊓ g.ker).relIndex g.ker * (f.range ⊔ g.ker).index) * (g.range).index) := by
        rw [card_ker_comp f g, hR]
    _ = Nat.card f.ker
          * (Nat.card (f.range ⊓ g.ker : Subgroup H) * (f.range ⊓ g.ker).relIndex g.ker)
          * ((f.range ⊔ g.ker).index * (g.range).index) := by ring
    _ = Nat.card f.ker * Nat.card g.ker * ((g.comp f).range).index := by
        rw [hInf, hP]

/-- The range index of a composite is divisible in the outer range: the index of the composite
range factors through the index of the outer range. -/
@[to_additive /-- The range index of a composite of additive homomorphisms factors through the
index of the outer range. -/]
theorem index_range_comp_eq (f : G →* H) (g : H →* K) :
    ((g.comp f).range).index = (f.range ⊔ g.ker).index * (g.range).index := by
  rw [← relIndex_range_comp f g]
  exact (Subgroup.relIndex_mul_index (by
    rw [MonoidHom.range_comp]; exact Subgroup.map_le_range g f.range)).symm

end MonoidHom
