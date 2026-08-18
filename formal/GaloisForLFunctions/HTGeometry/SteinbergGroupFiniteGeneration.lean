import GaloisForLFunctions.HTGeometry.SteinbergElementaryGroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Defs

/-!
# The Steinberg group of a finitely generated ring is finitely generated

Although the Steinberg group has one generator `x_ij(a)` for *every* ring element `a`, the three
Steinberg relations already produce all of them from the generators attached to a set of ring
generators: additivity of the entry gives sums and negatives, and the chained commutator
`⁅x_ik(a), x_kj(b)⁆ = x_ij(ab)` gives products, provided a third index is available.

Hence the entries whose generators lie in a fixed subgroup form a **subring**, and if that subring
contains a set of ring generators it is everything.

* `steinbergEntrySubring` : the entries whose generators lie in a given subgroup form a subring.
* `steinbergGroup_fg` : **`St(R)` is finitely generated for a finitely generated ring `R`** and an
  index type with at least three elements.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [Ring R] {n : Type*}

/-- The Steinberg generators whose entry lies in `T`. -/
def steinbergGens (T : Set R) : Set (SteinbergGroup R n) :=
  (PresentedGroup.of : SteinbergGen R n → SteinbergGroup R n) '' {g | g.a ∈ T}

theorem steinbergX_mem_steinbergGens {T : Set R} {i j : n} (hij : i ≠ j) {a : R} (ha : a ∈ T) :
    steinbergX hij a ∈ (steinbergGens T : Set (SteinbergGroup R n)) :=
  ⟨⟨i, j, hij, a⟩, ha, rfl⟩

theorem steinbergGens_finite [Finite n] {T : Set R} (hT : T.Finite) :
    (steinbergGens (n := n) T).Finite := by
  have hinj : Function.Injective (fun g : SteinbergGen R n => (g.i, g.j, g.a)) := by
    rintro ⟨i, j, hij, a⟩ ⟨i', j', hij', a'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  refine Set.Finite.image _ ?_
  refine Set.Finite.of_finite_image (f := fun g : SteinbergGen R n => (g.i, g.j, g.a))
    ?_ hinj.injOn
  refine Set.Finite.subset
    (((Set.finite_univ (α := n)).prod ((Set.finite_univ (α := n)).prod hT))) ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨Set.mem_univ _, Set.mem_univ _, hg⟩

/-- The entries all of whose Steinberg generators lie in `H`. -/
def steinbergEntries (H : Subgroup (SteinbergGroup R n)) : Set R :=
  {a | ∀ (i j : n) (hij : i ≠ j), steinbergX hij a ∈ H}

/-- **The entries whose generators lie in a subgroup form a subring**, provided a third index is
always available and the generators of `1` are present. -/
def steinbergEntrySubring (H : Subgroup (SteinbergGroup R n))
    (hthird : ∀ i j : n, ∃ k : n, k ≠ i ∧ k ≠ j)
    (hone : (1 : R) ∈ steinbergEntries H) : Subring R where
  carrier := steinbergEntries H
  zero_mem' := by
    intro i j hij
    rw [steinbergX_zero]
    exact one_mem H
  one_mem' := hone
  add_mem' := by
    intro a b ha hb i j hij
    rw [← steinbergX_mul hij a b]
    exact mul_mem (ha i j hij) (hb i j hij)
  neg_mem' := by
    intro a ha i j hij
    have h : steinbergX hij a * steinbergX hij (-a) = 1 := by
      rw [steinbergX_mul hij a (-a), add_neg_cancel, steinbergX_zero]
    have : steinbergX hij (-a) = (steinbergX hij a)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem (ha i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k, hki, hkj⟩ := hthird i j
    have hik : i ≠ k := Ne.symm hki
    have hkj' : k ≠ j := hkj
    rw [← steinbergX_chain hik hkj' hij a b]
    exact mul_mem (mul_mem (mul_mem (ha i k hik) (hb k j hkj'))
      (inv_mem (ha i k hik))) (inv_mem (hb k j hkj'))

/-- **The Steinberg group of a finitely generated ring is finitely generated.**  The subgroup on
the generators attached to a finite set of ring generators, together with `1`, already contains the
generators of every ring element, because those entries form a subring. -/
theorem steinbergGroup_fg [Finite n] (T : Set R) (hTfin : T.Finite)
    (hT : Subring.closure T = ⊤) (hthird : ∀ i j : n, ∃ k : n, k ≠ i ∧ k ≠ j) :
    Group.FG (SteinbergGroup R n) := by
  classical
  set T' : Set R := insert (1 : R) T with hT'
  set H : Subgroup (SteinbergGroup R n) := Subgroup.closure (steinbergGens T') with hH
  have hgenmem : ∀ (i j : n) (hij : i ≠ j) (a : R), a ∈ T' → steinbergX hij a ∈ H := by
    intro i j hij a ha
    exact Subgroup.subset_closure (steinbergX_mem_steinbergGens hij ha)
  have hone : (1 : R) ∈ steinbergEntries H := fun i j hij =>
    hgenmem i j hij 1 (Set.mem_insert _ _)
  set A : Subring R := steinbergEntrySubring H hthird hone with hA
  have hTA : T ⊆ (A : Set R) := fun a ha i j hij =>
    hgenmem i j hij a (Set.mem_insert_of_mem _ ha)
  have hAtop : A = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← hT]
    exact Subring.closure_le.2 hTA
  have hgen : (⊤ : Subgroup (SteinbergGroup R n))
      = Subgroup.closure (Set.range (PresentedGroup.of : SteinbergGen R n → SteinbergGroup R n)) :=
    (PresentedGroup.closure_range_of (steinbergRels R n)).symm
  have hHtop : H = ⊤ := by
    refine top_le_iff.1 ?_
    rw [hgen]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, rfl⟩
    have : g.a ∈ A := by rw [hAtop]; trivial
    exact this g.i g.j g.hij
  exact Group.fg_iff.2 ⟨steinbergGens T', hHtop, steinbergGens_finite (hTfin.insert 1)⟩

/-- A set spanning a ring as a `ℤ`-module generates it as a ring. -/
theorem subring_closure_eq_top_of_span_eq_top {s : Set R} (hs : Submodule.span ℤ s = ⊤) :
    Subring.closure s = ⊤ := by
  have key : ∀ x ∈ Submodule.span ℤ s, x ∈ Subring.closure s := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Subring.subset_closure hy
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c a _ ha => exact zsmul_mem ha c
  exact top_le_iff.1 fun x _ => key x (by rw [hs]; trivial)

/-- **The Steinberg group of a ring that is finitely generated as an abelian group is finitely
generated.**  This covers the ring of integers of a number field and every ring of `S`-integers. -/
theorem steinbergGroup_fg_of_moduleFinite [Finite n] (hR : Module.Finite ℤ R)
    (hthird : ∀ i j : n, ∃ k : n, k ≠ i ∧ k ≠ j) : Group.FG (SteinbergGroup R n) := by
  obtain ⟨T, hT⟩ := hR.fg_top
  exact steinbergGroup_fg (T : Set R) T.finite_toSet
    (subring_closure_eq_top_of_span_eq_top hT) hthird

/-- With at least three indices a third index is always available. -/
theorem exists_third_index [Fintype n] [DecidableEq n] (hcard : 3 ≤ Fintype.card n) (i j : n) :
    ∃ k : n, k ≠ i ∧ k ≠ j := by
  classical
  have hcard2 : ({i, j} : Finset n).card ≤ 2 := by
    simpa using Finset.card_insert_le i ({j} : Finset n)
  have hlt : ({i, j} : Finset n).card < (Finset.univ : Finset n).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨k, ?_, ?_⟩ <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hk <;> tauto

section Elementary

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The elementary group of a ring that is finitely generated as an abelian group is finitely
generated**, being the image of the Steinberg group. -/
theorem elementaryGroup_fg (hR : Module.Finite ℤ R)
    (hthird : ∀ i j : n, ∃ k : n, k ≠ i ∧ k ≠ j) : Group.FG (elementaryGroup R n) := by
  haveI : Group.FG (SteinbergGroup R n) := steinbergGroup_fg_of_moduleFinite hR hthird
  exact Group.fg_range _

end Elementary

end GaloisForLFunctions.HTGeometry
