import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# The Steinberg group of a ring

`K_2` of a ring is the kernel of the map from the Steinberg group to the elementary group, so the
Steinberg group is the first object needed to connect the tame kernel of Milnor `K`-theory with
group homology.  It is the group presented by one generator `x_ij(a)` for every off-diagonal
position and every ring element, subject to Steinberg's three relations: additivity in the entry,
commutation at disjoint positions, and the chained commutator.

* `SteinbergGen`, `steinbergRels`, `SteinbergGroup` : **the presentation.**
* `steinbergX` : the generator at a position.
* `steinbergX_mul`, `steinbergX_zero`, `steinbergX_commute`, `steinbergX_chain` : **the three
  relations, as theorems about the generators.**
-/

namespace GaloisForLFunctions.HTGeometry

open FreeGroup

/-- A generator of the Steinberg group: an off-diagonal position and a ring entry. -/
structure SteinbergGen (R : Type*) (n : Type*) where
  /-- the row -/
  i : n
  /-- the column -/
  j : n
  /-- the two indices are distinct -/
  hij : i ≠ j
  /-- the entry -/
  a : R

variable (R : Type*) [Ring R] (n : Type*)

/-- The additivity relators `x_ij(a)·x_ij(b)·x_ij(a+b)⁻¹`. -/
def steinbergAddRel : Set (FreeGroup (SteinbergGen R n)) :=
  {w | ∃ (i j : n) (hij : i ≠ j) (a b : R),
    w = of (⟨i, j, hij, a⟩ : SteinbergGen R n) * of ⟨i, j, hij, b⟩ * (of ⟨i, j, hij, a + b⟩)⁻¹}

/-- The relators expressing that generators at disjoint positions commute. -/
def steinbergCommRel : Set (FreeGroup (SteinbergGen R n)) :=
  {w | ∃ (i j k l : n) (hij : i ≠ j) (hkl : k ≠ l) (a b : R), j ≠ k ∧ i ≠ l ∧
    w = of (⟨i, j, hij, a⟩ : SteinbergGen R n) * of ⟨k, l, hkl, b⟩
      * (of (⟨i, j, hij, a⟩ : SteinbergGen R n))⁻¹ * (of (⟨k, l, hkl, b⟩ : SteinbergGen R n))⁻¹}

/-- The relators expressing the chained commutator `[x_ij(a), x_jk(b)] = x_ik(ab)`. -/
def steinbergChainRel : Set (FreeGroup (SteinbergGen R n)) :=
  {w | ∃ (i j k : n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
    w = of (⟨i, j, hij, a⟩ : SteinbergGen R n) * of ⟨j, k, hjk, b⟩
      * (of (⟨i, j, hij, a⟩ : SteinbergGen R n))⁻¹ * (of (⟨j, k, hjk, b⟩ : SteinbergGen R n))⁻¹
      * (of (⟨i, k, hik, a * b⟩ : SteinbergGen R n))⁻¹}

/-- All the Steinberg relators. -/
def steinbergRels : Set (FreeGroup (SteinbergGen R n)) :=
  steinbergAddRel R n ∪ steinbergCommRel R n ∪ steinbergChainRel R n

/-- **The Steinberg group of a ring.** -/
def SteinbergGroup : Type _ := PresentedGroup (steinbergRels R n)

instance : Group (SteinbergGroup R n) := by
  unfold SteinbergGroup
  infer_instance

variable {R n}

/-- The Steinberg generator at an off-diagonal position. -/
def steinbergX {i j : n} (hij : i ≠ j) (a : R) : SteinbergGroup R n :=
  PresentedGroup.of ⟨i, j, hij, a⟩

/-- **Additivity of the Steinberg generators.** -/
theorem steinbergX_mul {i j : n} (hij : i ≠ j) (a b : R) :
    steinbergX hij a * steinbergX hij b = steinbergX hij (a + b) := by
  have hmem : (of (⟨i, j, hij, a⟩ : SteinbergGen R n) * of ⟨i, j, hij, b⟩
      * (of (⟨i, j, hij, a + b⟩ : SteinbergGen R n))⁻¹) ∈ steinbergRels R n :=
    Or.inl (Or.inl ⟨i, j, hij, a, b, rfl⟩)
  have h := (QuotientGroup.eq_one_iff _).2
    (Subgroup.subset_normalClosure hmem)
  show PresentedGroup.of _ * PresentedGroup.of _ = PresentedGroup.of _
  have hq : (QuotientGroup.mk (of (⟨i, j, hij, a⟩ : SteinbergGen R n) * of ⟨i, j, hij, b⟩
      * (of (⟨i, j, hij, a + b⟩ : SteinbergGen R n))⁻¹) :
      PresentedGroup (steinbergRels R n)) = 1 := h
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hq
  rw [mul_inv_eq_one] at hq
  exact hq

/-- **The Steinberg generator at zero is trivial.** -/
theorem steinbergX_zero {i j : n} (hij : i ≠ j) : steinbergX hij (0 : R) = 1 := by
  have h := steinbergX_mul hij (0 : R) 0
  rw [add_zero] at h
  have h1 : steinbergX hij (0 : R) * steinbergX hij (0 : R)
      = steinbergX hij (0 : R) * 1 := by rw [mul_one]; exact h
  exact mul_left_cancel h1

/-- **Generators at disjoint positions commute.** -/
theorem steinbergX_commute {i j k l : n} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l)
    (a b : R) :
    steinbergX hij a * steinbergX hkl b = steinbergX hkl b * steinbergX hij a := by
  have hmem : (of (⟨i, j, hij, a⟩ : SteinbergGen R n) * of ⟨k, l, hkl, b⟩
      * (of (⟨i, j, hij, a⟩ : SteinbergGen R n))⁻¹
      * (of (⟨k, l, hkl, b⟩ : SteinbergGen R n))⁻¹) ∈ steinbergRels R n :=
    Or.inl (Or.inr ⟨i, j, k, l, hij, hkl, a, b, hjk, hil, rfl⟩)
  have hq : (QuotientGroup.mk (of (⟨i, j, hij, a⟩ : SteinbergGen R n) * of ⟨k, l, hkl, b⟩
      * (of (⟨i, j, hij, a⟩ : SteinbergGen R n))⁻¹
      * (of (⟨k, l, hkl, b⟩ : SteinbergGen R n))⁻¹) : SteinbergGroup R n) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure hmem)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv] at hq
  have h3 : steinbergX hij a * steinbergX hkl b * (steinbergX hij a)⁻¹ = steinbergX hkl b :=
    mul_inv_eq_one.1 hq
  exact mul_inv_eq_iff_eq_mul.1 h3

/-- **The chained commutator relation.** -/
theorem steinbergX_chain {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    steinbergX hij a * steinbergX hjk b * (steinbergX hij a)⁻¹ * (steinbergX hjk b)⁻¹
      = steinbergX hik (a * b) := by
  have hmem : (of (⟨i, j, hij, a⟩ : SteinbergGen R n) * of ⟨j, k, hjk, b⟩
      * (of (⟨i, j, hij, a⟩ : SteinbergGen R n))⁻¹
      * (of (⟨j, k, hjk, b⟩ : SteinbergGen R n))⁻¹
      * (of (⟨i, k, hik, a * b⟩ : SteinbergGen R n))⁻¹) ∈ steinbergRels R n :=
    Or.inr ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩
  have hq : (QuotientGroup.mk (of (⟨i, j, hij, a⟩ : SteinbergGen R n) * of ⟨j, k, hjk, b⟩
      * (of (⟨i, j, hij, a⟩ : SteinbergGen R n))⁻¹
      * (of (⟨j, k, hjk, b⟩ : SteinbergGen R n))⁻¹
      * (of (⟨i, k, hik, a * b⟩ : SteinbergGen R n))⁻¹) : SteinbergGroup R n) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure hmem)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, QuotientGroup.mk_inv] at hq
  exact mul_inv_eq_one.1 hq


/-- **Generators with a common second index commute.**  These generate the abelian "column"
subgroups on which the map to matrices is injective, which is the mechanism behind the centrality
of `K_2` in the Steinberg group. -/
theorem steinbergX_commute_col {k l j : n} (hkj : k ≠ j) (hlj : l ≠ j) (a b : R) :
    steinbergX hkj a * steinbergX hlj b = steinbergX hlj b * steinbergX hkj a :=
  steinbergX_commute hkj hlj (Ne.symm hlj) hkj a b

/-- **Generators with a common first index commute.** -/
theorem steinbergX_commute_row {i k l : n} (hik : i ≠ k) (hil : i ≠ l) (a b : R) :
    steinbergX hik a * steinbergX hil b = steinbergX hil b * steinbergX hik a :=
  steinbergX_commute hik hil (Ne.symm hik) hil a b


/-- **Every generator is a commutator**, whenever a third index is available. -/
theorem steinbergX_eq_commutator {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : R) :
    steinbergX hik a
      = steinbergX hij a * steinbergX hjk (1 : R) * (steinbergX hij a)⁻¹
        * (steinbergX hjk (1 : R))⁻¹ := by
  rw [steinbergX_chain hij hjk hik a 1, mul_one]

/-- **The Steinberg group is perfect** as soon as every pair of distinct indices admits a third.
Every generator is a commutator, and the generators generate. -/
theorem steinbergGroup_perfect (h3 : ∀ i k : n, i ≠ k → ∃ j, i ≠ j ∧ j ≠ k) :
    commutator (SteinbergGroup R n) = ⊤ := by
  refine top_le_iff.1 ?_
  have hgen : (⊤ : Subgroup (SteinbergGroup R n))
      = Subgroup.closure (Set.range (PresentedGroup.of : SteinbergGen R n → SteinbergGroup R n)) :=
    (PresentedGroup.closure_range_of (steinbergRels R n)).symm
  rw [hgen]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨g, rfl⟩
  obtain ⟨m, him, hmj⟩ := h3 g.i g.j g.hij
  have hx : (PresentedGroup.of g : SteinbergGroup R n) = steinbergX g.hij g.a := rfl
  rw [hx, steinbergX_eq_commutator him hmj g.hij g.a]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)


end GaloisForLFunctions.HTGeometry
