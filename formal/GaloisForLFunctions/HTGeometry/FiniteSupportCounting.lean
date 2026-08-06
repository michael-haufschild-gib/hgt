import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting finite configurations by the size of their support

For a finite site set `σ`, a finite local alphabet `α` and a distinguished
ground letter `z`, the number of configurations `σ → α` whose support
`{i : f i ≠ z}` has exactly `k` elements is `C(|σ|, k) · (|α| - 1)^k`, and the
number whose support has at most `q` elements is the corresponding partial sum.

The proof fibres the configuration space over the support and identifies each
fibre with the space of maps from the support to the non-ground letters.
-/

namespace GaloisForLFunctions.HTGeometry

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [Fintype α] [DecidableEq α]

/-- The non-ground letters are one fewer than all letters. -/
theorem card_ne_ground (z : α) : Fintype.card {a : α // a ≠ z} = Fintype.card α - 1 := by
  classical
  simp [Fintype.card_subtype_compl (p := fun a : α => a = z)]

/-- The support of a configuration relative to a ground letter. -/
def configSupport (z : α) (f : σ → α) : Finset σ :=
  Finset.univ.filter (fun i => f i ≠ z)

omit [DecidableEq σ] [Fintype α] in
theorem mem_configSupport {z : α} {f : σ → α} {i : σ} :
    i ∈ configSupport z f ↔ f i ≠ z := by
  simp [configSupport]

/-- Configurations with a prescribed support are exactly the maps from that
support to the non-ground letters. -/
def configSupportFiberEquiv (z : α) (S : Finset σ) :
    {f : σ → α // configSupport z f = S} ≃ (↥S → {a : α // a ≠ z}) where
  toFun f := fun i => ⟨f.1 i.1, by
    have : i.1 ∈ configSupport z f.1 := by rw [f.2]; exact i.2
    exact mem_configSupport.mp this⟩
  invFun g := ⟨fun i => if h : i ∈ S then (g ⟨i, h⟩).1 else z, by
    ext i
    rw [mem_configSupport]
    by_cases h : i ∈ S
    · simp only [dif_pos h]
      exact iff_of_true (g ⟨i, h⟩).2 h
    · simp only [dif_neg h]
      exact iff_of_false (fun hc => hc rfl) h⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases h : i ∈ S
    · simp [h]
    · simp only [dif_neg h]
      by_contra hc
      exact h (f.2 ▸ mem_configSupport.mpr (Ne.symm hc))
  right_inv g := by
    funext i
    apply Subtype.ext
    simp [i.2]

/-- The number of configurations with a prescribed support. -/
theorem card_configSupport_fiber (z : α) (S : Finset σ) :
    (Finset.univ.filter (fun f : σ → α => configSupport z f = S)).card
      = (Fintype.card α - 1) ^ S.card := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (configSupportFiberEquiv z S), Fintype.card_fun,
    Fintype.card_coe, card_ne_ground]

/-- **Support-size count.**  The configurations whose support has exactly `k`
sites are counted by choosing the support and then a non-ground letter at each
of its sites. -/
theorem card_configSupport_card_eq (z : α) (k : ℕ) :
    (Finset.univ.filter (fun f : σ → α => (configSupport z f).card = k)).card
      = (Fintype.card σ).choose k * (Fintype.card α - 1) ^ k := by
  classical
  have hsplit : Finset.univ.filter (fun f : σ → α => (configSupport z f).card = k)
      = (Finset.univ.powersetCard k).biUnion
          (fun S => Finset.univ.filter (fun f : σ → α => configSupport z f = S)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_powersetCard]
    constructor
    · intro h
      exact ⟨configSupport z f, ⟨Finset.subset_univ _, h⟩, rfl⟩
    · rintro ⟨S, ⟨-, hcard⟩, hS⟩
      rw [hS]
      exact hcard
  rw [hsplit, Finset.card_biUnion]
  · have hterm : ∀ S ∈ Finset.univ.powersetCard (α := σ) k,
        (Finset.univ.filter (fun f : σ → α => configSupport z f = S)).card
          = (Fintype.card α - 1) ^ k := by
      intro S hS
      rw [card_configSupport_fiber z S, (Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ]
    simp
  · intro S hS T hT hST
    refine Finset.disjoint_left.mpr fun f hf hf' => hST ?_
    rw [Finset.mem_filter] at hf hf'
    rw [← hf.2, ← hf'.2]

/-- **Bounded-support count.**  The configurations whose support is nonempty and
has at most `q` sites are counted by the partial sum. -/
theorem card_configSupport_pos_le (z : α) (q : ℕ) :
    (Finset.univ.filter
        (fun f : σ → α => 0 < (configSupport z f).card ∧ (configSupport z f).card ≤ q)).card
      = ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * (Fintype.card α - 1) ^ k := by
  classical
  have hsplit : Finset.univ.filter
      (fun f : σ → α => 0 < (configSupport z f).card ∧ (configSupport z f).card ≤ q)
      = (Finset.Icc 1 q).biUnion
          (fun k => Finset.univ.filter (fun f : σ → α => (configSupport z f).card = k)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(configSupport z f).card, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, hk⟩
      exact ⟨hk ▸ hk1, hk ▸ hk2⟩
  rw [hsplit, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun k _ => card_configSupport_card_eq z k
  · intro k hk l hl hkl
    refine Finset.disjoint_left.mpr fun f hf hf' => hkl ?_
    rw [Finset.mem_filter] at hf hf'
    rw [← hf.2, ← hf'.2]

end GaloisForLFunctions.HTGeometry
