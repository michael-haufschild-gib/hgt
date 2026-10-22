import GaloisForLFunctions.RHTower.Deninger.DeningerRootCyclicCentralizers
import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutCountable
import GaloisForLFunctions.RHTower.Deninger.DeningerRootUniqueRoots
import GaloisForLFunctions.RHTower.Deninger.DeningerCentralizerZpow

/-!
# Stages carrying unique roots and cyclic centralizers

A stage of the tower is a countable group with unique roots whose centralizers are all cyclic,
together with an enumeration of its elements and a distinguished nontrivial element.  The step roots
the generator of the centralizer of an enumerated element — every element being a power of that
generator, the element itself acquires the root — and the enumeration of the new stage keeps the old
indices, the images of the old elements, and devotes a fresh block of indices to a surjection onto
the new group.

* `DeningerCCStage`, `DeningerCCGood`, `deningerCCStep` : the tower data.
* `deningerCCStep_good` : the step preserves the invariant.
* `deningerCCStep_root` : the enumerated element acquires the scheduled root.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

open scoped Classical

/-- A surjection from the naturals onto a group, chosen once and for all. -/
noncomputable def deningerCCFresh (A : Type u) [Group A] : ℕ → A :=
  if h : ∃ f : ℕ → A, Function.Surjective f then Classical.choose h else fun _ => 1

/-- **The chosen surjection is onto** when the group is countable. -/
theorem deningerCCFresh_surjective (A : Type u) [Group A] [Countable A] :
    Function.Surjective (deningerCCFresh A) := by
  have h : ∃ f : ℕ → A, Function.Surjective f := exists_surjective_nat A
  rw [deningerCCFresh, dif_pos h]
  exact Classical.choose_spec h

/-- The generator of the centralizer of an element, chosen once and for all. -/
noncomputable def deningerCCGen (A : Type u) [Group A] (x : A) : A :=
  if h : ∃ y : A, (∀ n : ℤ, y ^ n = 1 → n = 0) ∧
      ∀ z : A, z * x * z⁻¹ = x ↔ z ∈ Subgroup.zpowers y then Classical.choose h else x

/-- **The chosen generator generates the centralizer** when the centralizers are cyclic. -/
theorem deningerCCGen_spec (A : Type u) [Group A] (hCC : DeningerCyclicCentralizers A)
    (x : A) (hx : x ≠ 1) :
    (∀ n : ℤ, (deningerCCGen A x) ^ n = 1 → n = 0) ∧
      ∀ z : A, z * x * z⁻¹ = x ↔ z ∈ Subgroup.zpowers (deningerCCGen A x) := by
  have h := hCC x hx
  rw [deningerCCGen, dif_pos h]
  exact Classical.choose_spec h

/-- A stage of the tower: a group with an enumeration and a distinguished element. -/
structure DeningerCCStage : Type (u + 1) where
  /-- The underlying group of the stage. -/
  carrier : Type u
  /-- Its group structure. -/
  [group : Group carrier]
  /-- An enumeration of its elements. -/
  hist : ℕ → carrier
  /-- A distinguished element, used when the enumeration hits the identity. -/
  witness : carrier

attribute [instance] DeningerCCStage.group

/-- The invariant carried along the tower. -/
structure DeningerCCGood (S : DeningerCCStage.{u}) : Prop where
  /-- The stage has unique roots. -/
  uniqueRoots : ∀ (x y : S.carrier) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y
  /-- Its centralizers are cyclic. -/
  cyclic : DeningerCyclicCentralizers S.carrier
  /-- The distinguished element is nontrivial. -/
  witness_ne : S.witness ≠ 1
  /-- The enumeration is onto. -/
  hist_surj : Function.Surjective S.hist
  /-- The stage is countable. -/
  countable : Countable S.carrier

/-- The element whose centralizer is rooted at an index: the enumerated element, or the
distinguished one if that is the identity. -/
noncomputable def deningerCCElt (S : DeningerCCStage.{u}) (p : ℕ) : S.carrier :=
  if S.hist p = 1 then S.witness else S.hist p

/-- **The rooted element is nontrivial.** -/
theorem deningerCCElt_ne_one (S : DeningerCCStage.{u}) (hS : DeningerCCGood S) (p : ℕ) :
    deningerCCElt S p ≠ 1 := by
  rw [deningerCCElt]
  split
  · exact hS.witness_ne
  · assumption

/-- The generator of the centralizer of the element rooted at an index. -/
noncomputable def deningerCCRoot (S : DeningerCCStage.{u}) (p : ℕ) : S.carrier :=
  deningerCCGen S.carrier (deningerCCElt S p)

/-- **The step of the tower**: adjoin an `N`-th root to the generator of the centralizer of the
`p`-th enumerated element, at stage `n`. -/
noncomputable def deningerCCStep (S : DeningerCCStage.{u}) (n p : ℕ) (N : ℤ) :
    DeningerCCStage.{u} where
  carrier := PushoutI (deningerRootMap S.carrier (deningerCCRoot S p) N)
  hist := fun q => if (Nat.unpair q).1 = n + 1
    then deningerCCFresh (PushoutI (deningerRootMap S.carrier (deningerCCRoot S p) N))
      (Nat.unpair q).2
    else PushoutI.of (φ := deningerRootMap S.carrier (deningerCCRoot S p) N) (ULift.up true)
      (S.hist q)
  witness := PushoutI.of (φ := deningerRootMap S.carrier (deningerCCRoot S p) N) (ULift.up true)
    S.witness

/-- The rooted generator has infinite order. -/
theorem deningerCCRoot_order (S : DeningerCCStage.{u}) (hS : DeningerCCGood S) (p : ℕ) :
    ∀ n : ℤ, (deningerCCRoot S p) ^ n = 1 → n = 0 :=
  (deningerCCGen_spec S.carrier hS.cyclic (deningerCCElt S p) (deningerCCElt_ne_one S hS p)).1

/-- The rooted generator is its own centralizer. -/
theorem deningerCCRoot_central (S : DeningerCCStage.{u}) (hS : DeningerCCGood S) (p : ℕ)
    (z : S.carrier) (hz : z * deningerCCRoot S p * z⁻¹ = deningerCCRoot S p) :
    z ∈ Subgroup.zpowers (deningerCCRoot S p) :=
  deningerCyclicCentralizers_central (deningerCCElt S p) (deningerCCRoot S p)
    (deningerCCGen_spec S.carrier hS.cyclic (deningerCCElt S p) (deningerCCElt_ne_one S hS p)).2
    (deningerCCElt_ne_one S hS p) z hz

/-- The rooted generator generates an isolated subgroup. -/
theorem deningerCCRoot_isolated (S : DeningerCCStage.{u}) (hS : DeningerCCGood S) (p : ℕ)
    (z : S.carrier) (k : ℕ) (hk : 0 < k) (hz : z ^ k ∈ Subgroup.zpowers (deningerCCRoot S p)) :
    z ∈ Subgroup.zpowers (deningerCCRoot S p) :=
  deningerCyclicCentralizers_isolated hS.uniqueRoots (deningerCCElt S p) (deningerCCRoot S p)
    (deningerCCGen_spec S.carrier hS.cyclic (deningerCCElt S p) (deningerCCElt_ne_one S hS p)).2
    (deningerCCElt_ne_one S hS p) z k hk hz

/-- The rooted element is a power of the rooted generator. -/
theorem deningerCCElt_mem (S : DeningerCCStage.{u}) (hS : DeningerCCGood S) (p : ℕ) :
    ∃ c : ℤ, (deningerCCRoot S p) ^ c = deningerCCElt S p := by
  obtain ⟨c, -, hc⟩ := deningerCyclicCentralizers_mem (deningerCCElt S p) (deningerCCRoot S p)
    (deningerCCGen_spec S.carrier hS.cyclic (deningerCCElt S p) (deningerCCElt_ne_one S hS p)).2
    (deningerCCElt_ne_one S hS p)
  exact ⟨c, hc⟩

/-- **The step preserves the invariant.** -/
theorem deningerCCStep_good (S : DeningerCCStage.{u}) (hS : DeningerCCGood S) (n p : ℕ) (N : ℤ)
    (hN : 2 ≤ N.natAbs) : DeningerCCGood (deningerCCStep S n p N) := by
  have hm : N ≠ 0 := by omega
  have ha := deningerCCRoot_order S hS p
  have hcentA : ∀ (x : S.carrier) (c : ℤ), c ≠ 0 →
      x * (deningerCCRoot S p) ^ c * x⁻¹ = (deningerCCRoot S p) ^ c →
      x ∈ Subgroup.zpowers (deningerCCRoot S p) :=
    deningerCentralizer_zpow_subset hS.uniqueRoots (deningerCCRoot S p)
      (deningerCCRoot_central S hS p)
  have htorA : ∀ (x : S.carrier) (k : ℕ), 0 < k → x ^ k = 1 → x = 1 :=
    deningerUniqueRoots_torsionFree hS.uniqueRoots
  have hcount : Countable (PushoutI (deningerRootMap S.carrier (deningerCCRoot S p) N)) := by
    have := hS.countable
    exact deningerRootAdjunction_countable S.carrier (deningerCCRoot S p) N hm ha
  have hφ := deningerRootMap_injective S.carrier (deningerCCRoot S p) N hm ha
  refine ⟨?_, ?_, ?_, ?_, hcount⟩
  · intro x y k hk h
    refine deningerRootAdjunction_uniqueRoots S.carrier (deningerCCRoot S p) N hm ha
      hS.uniqueRoots (deningerCCRoot_isolated S hS p) hcentA htorA x y (k - 1) ?_
    rw [show k - 1 + 1 = k by omega]
    exact h
  · exact deningerRootAdjunction_cyclicCentralizers S.carrier (deningerCCRoot S p) N hm hN ha
      hS.uniqueRoots (deningerCCRoot_isolated S hS p) hcentA htorA hS.cyclic
  · show PushoutI.of (φ := deningerRootMap S.carrier (deningerCCRoot S p) N) (ULift.up true)
      S.witness ≠ 1
    intro hc
    refine hS.witness_ne (PushoutI.of_injective hφ (ULift.up true) ?_)
    exact hc.trans (map_one _).symm
  · intro w
    obtain ⟨i, hi⟩ := deningerCCFresh_surjective
      (PushoutI (deningerRootMap S.carrier (deningerCCRoot S p) N)) w
    refine ⟨Nat.pair (n + 1) i, ?_⟩
    show (if (Nat.unpair (Nat.pair (n + 1) i)).1 = n + 1 then _ else _) = w
    rw [Nat.unpair_pair, if_pos rfl]
    exact hi

/-- **The enumerated element acquires the scheduled root.** -/
theorem deningerCCStep_root (S : DeningerCCStage.{u}) (hS : DeningerCCGood S) (_n p : ℕ) (N : ℤ) :
    ∃ y : PushoutI (deningerRootMap S.carrier (deningerCCRoot S p) N),
      y ^ N = PushoutI.of (φ := deningerRootMap S.carrier (deningerCCRoot S p) N)
        (ULift.up true) (S.hist p) := by
  by_cases h1 : S.hist p = 1
  · refine ⟨1, ?_⟩
    rw [one_zpow, h1]
    exact (map_one _).symm
  · obtain ⟨c, hc⟩ := deningerCCElt_mem S hS p
    have helt : deningerCCElt S p = S.hist p := by
      rw [deningerCCElt, if_neg h1]
    refine ⟨(deningerRootElt S.carrier (deningerCCRoot S p) N) ^ c, ?_⟩
    have h3 : deningerCCRoot S p ^ c = S.hist p := hc.trans helt
    calc ((deningerRootElt S.carrier (deningerCCRoot S p) N) ^ c) ^ N
        = (PushoutI.of (φ := deningerRootMap S.carrier (deningerCCRoot S p) N) (ULift.up true)
            (deningerCCRoot S p)) ^ c := by
          rw [← zpow_mul, mul_comm, zpow_mul, deningerRootElt_zpow]
      _ = PushoutI.of (φ := deningerRootMap S.carrier (deningerCCRoot S p) N) (ULift.up true)
            (deningerCCRoot S p ^ c) := (map_zpow _ _ _).symm
      _ = PushoutI.of (φ := deningerRootMap S.carrier (deningerCCRoot S p) N) (ULift.up true)
            (S.hist p) := congrArg _ h3

end RootAdjunction

end RHTower
