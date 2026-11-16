import GaloisForLFunctions.RHTower.FermionicFockIsospectrality
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Quadratic energy cost of fermionic excitations

For the half-filled equally spaced spectrum, moving `q` particles across the
Fermi edge costs at least `q²` units of energy. Distinct occupied levels force
two triangular contributions. This is the combinatorial energy mechanism in
Slonim's exterior-power estimates.
-/

noncomputable section
open scoped BigOperators
open Finset
namespace RHTower.ParityForecast

private theorem sum_lower_edge (k : ℕ) (s : Finset ℕ) :
    (∀ j ∈ s, k ≤ j) →
      (s.card : ℝ) * (2 * k + s.card - 1) ≤ 2 * ∑ j ∈ s, (j : ℝ) := by
  induction s using Finset.induction_on_max with
  | empty => intro _; norm_num
  | insert a s hmax ih =>
    intro hk
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
    have hks : ∀ j ∈ s, k ≤ j := fun j hj => hk j (mem_insert_of_mem hj)
    have hka := hk a (mem_insert_self a s)
    have hsub : s ⊆ Ico k a := by
      intro j hj
      exact mem_Ico.mpr ⟨hks j hj, hmax j hj⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Ico] at hcard
    have hkn : k + s.card ≤ a := by omega
    have hkr : (k : ℝ) + s.card ≤ a := by exact_mod_cast hkn
    have hh := ih hks
    rw [card_insert_of_notMem ha, sum_insert ha, Nat.cast_add, Nat.cast_one]
    nlinarith only [hh, hkr]

private theorem sum_upper_edge (k : ℕ) (s : Finset ℕ) :
    (∀ j ∈ s, j < k) →
      2 * (∑ j ∈ s, (j : ℝ)) ≤ (s.card : ℝ) * (2 * k - s.card - 1) := by
  induction s using Finset.induction_on_min with
  | empty => intro _; norm_num
  | insert a s hmin ih =>
    intro hk
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmin a h)
    have hks : ∀ j ∈ s, j < k := fun j hj => hk j (mem_insert_of_mem hj)
    have hak := hk a (mem_insert_self a s)
    have hsub : s ⊆ Ioo a k := by
      intro j hj
      exact mem_Ioo.mpr ⟨hmin j hj, hks j hj⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Ioo] at hcard
    have hkn : a + s.card + 1 ≤ k := by omega
    have hkr : (a : ℝ) + s.card + 1 ≤ k := by exact_mod_cast hkn
    have hh := ih hks
    rw [card_insert_of_notMem ha, sum_insert ha, Nat.cast_add, Nat.cast_one]
    nlinarith only [hh, hkr]

/-- The natural-number occupied levels of a half-filled fermionic state. -/
def occupiedLevels {k : ℕ} (S : Set.powersetCard (Fin (2 * k)) k) : Finset ℕ :=
  S.val.map ⟨Fin.val, Fin.val_injective⟩

/-- Number of occupied levels below the half-filling edge. -/
def fermiExcitationNumber {k : ℕ} (S : Set.powersetCard (Fin (2 * k)) k) : ℕ :=
  (occupiedLevels S \ Ico k (2 * k)).card

/-- Energy lost relative to occupying precisely the upper half of the spectrum. -/
def fermiExcitationCost {k : ℕ} (S : Set.powersetCard (Fin (2 * k)) k) : ℝ :=
  (∑ j ∈ Ico k (2 * k), (j : ℝ)) - ∑ j ∈ occupiedLevels S, (j : ℝ)

/-- The excitation cost is the gap in the existing exterior-power Hamiltonian's eigenvalue. -/
theorem fermiExcitationCost_eq_subsetEnergy_gap {k : ℕ}
    (S : Set.powersetCard (Fin (2 * k)) k) :
    fermiExcitationCost S = (∑ j ∈ Ico k (2 * k), (j : ℝ)) -
      fermionicSubsetEnergy (fun j : Fin (2 * k) => (j.val : ℝ)) S := by
  simp only [fermiExcitationCost, occupiedLevels, sum_map, Function.Embedding.coeFn_mk,
    fermionicSubsetEnergy]

/-- Pauli exclusion makes the energy cost quadratic in the number of moved particles. -/
theorem fermiExcitationNumber_sq_le_cost {k : ℕ}
    (S : Set.powersetCard (Fin (2 * k)) k) :
    (fermiExcitationNumber S : ℝ) ^ 2 ≤ fermiExcitationCost S := by
  have hcard : (occupiedLevels S).card = k := by
    rw [occupiedLevels, card_map]
    exact S.property
  have htop : (Ico k (2 * k)).card = k := by rw [Nat.card_Ico]; omega
  have hbound (j : ℕ) (hj : j ∈ occupiedLevels S) : j < 2 * k := by
    obtain ⟨i, _, rfl⟩ := mem_map.mp hj
    exact i.isLt
  have hc : (Ico k (2 * k) \ occupiedLevels S).card =
      (occupiedLevels S \ Ico k (2 * k)).card := by
    apply card_sdiff_comm
    rw [htop, hcard]
  have hl := sum_lower_edge k (Ico k (2 * k) \ occupiedLevels S) (by
    intro j hj
    exact (mem_Ico.mp (mem_sdiff.mp hj).1).1)
  have hu := sum_upper_edge k (occupiedLevels S \ Ico k (2 * k)) (by
    intro j hj
    have hm := mem_sdiff.mp hj
    have hb := hbound j hm.1
    have hn := hm.2
    simp only [mem_Ico, not_and] at hn
    omega)
  rw [hc] at hl
  have ht := sum_inter_add_sum_sdiff (Ico k (2 * k)) (occupiedLevels S) (fun j => (j : ℝ))
  have hs := sum_inter_add_sum_sdiff (occupiedLevels S) (Ico k (2 * k)) (fun j => (j : ℝ))
  rw [inter_comm (Ico k (2 * k)) (occupiedLevels S)] at ht
  dsimp only [fermiExcitationNumber, fermiExcitationCost]
  nlinarith only [hl, hu, ht, hs]

/-- Zero excitation energy characterizes the filled upper half of the spectrum. -/
theorem fermiExcitationCost_eq_zero_iff {k : ℕ}
    (S : Set.powersetCard (Fin (2 * k)) k) :
    fermiExcitationCost S = 0 ↔ occupiedLevels S = Ico k (2 * k) := by
  constructor
  · intro hz
    have hq := fermiExcitationNumber_sq_le_cost S
    rw [hz] at hq
    have hq0 : fermiExcitationNumber S = 0 := by
      have hr : (fermiExcitationNumber S : ℝ) = 0 := by nlinarith only [hq]
      exact_mod_cast hr
    have hsub : occupiedLevels S ⊆ Ico k (2 * k) := by
      exact sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hq0)
    apply eq_of_subset_of_card_le hsub
    rw [Nat.card_Ico, occupiedLevels, card_map, S.property]
    omega
  · intro h
    simp only [fermiExcitationCost, h, sub_self]

/-- An energy window below `m²` permits fewer than `m` particle-hole excitations. -/
theorem fermiExcitationNumber_lt_of_cost_lt_sq {k : ℕ}
    (S : Set.powersetCard (Fin (2 * k)) k) (m : ℕ)
    (h : fermiExcitationCost S < (m : ℝ) ^ 2) :
    fermiExcitationNumber S < m := by
  have hq := lt_of_le_of_lt (fermiExcitationNumber_sq_le_cost S) h
  have hr : (fermiExcitationNumber S : ℝ) < m := by
    nlinarith only [hq, Nat.cast_nonneg (α := ℝ) (fermiExcitationNumber S), Nat.cast_nonneg (α := ℝ) m]
  exact_mod_cast hr

/-- Occupied levels after the nearest `q` particle-hole moves at half filling `q+r`. -/
def fermiEdgeLevels (q r : ℕ) : Finset ℕ :=
  Ico r (q + r) ∪ Ico (2 * q + r) (2 * (q + r))

private theorem edge_intervals_disjoint (q r : ℕ) :
    Disjoint (Ico r (q + r)) (Ico (2 * q + r) (2 * (q + r))) := by
  apply disjoint_left.mpr
  intro j hj hj'
  simp only [mem_Ico] at hj hj'
  omega

private theorem fermiEdgeLevels_card (q r : ℕ) : (fermiEdgeLevels q r).card = q + r := by
  rw [fermiEdgeLevels, card_union_of_disjoint (edge_intervals_disjoint q r),
    Nat.card_Ico, Nat.card_Ico]
  omega

private theorem fermiEdgeLevels_lt (q r j : ℕ) (hj : j ∈ fermiEdgeLevels q r) :
    j < 2 * (q + r) := by
  simp only [fermiEdgeLevels, mem_union, mem_Ico] at hj
  omega

private def fermiEdgeEmbedding (q r : ℕ) :
    (fermiEdgeLevels q r) ↪ Fin (2 * (q + r)) where
  toFun j := ⟨j.val, fermiEdgeLevels_lt q r j.val j.property⟩
  inj' := by
    intro i j h
    apply Subtype.ext
    exact congrArg Fin.val h

/-- The nearest-excitation configuration as an actual exterior-power basis index. -/
def fermiEdgeState (q r : ℕ) : Set.powersetCard (Fin (2 * (q + r))) (q + r) :=
  ⟨(fermiEdgeLevels q r).attach.map (fermiEdgeEmbedding q r), by
    change ((fermiEdgeLevels q r).attach.map (fermiEdgeEmbedding q r)).card = q + r
    rw [card_map, card_attach, fermiEdgeLevels_card]⟩

/-- The exterior configuration has exactly the advertised occupied levels. -/
theorem occupiedLevels_fermiEdgeState (q r : ℕ) :
    occupiedLevels (fermiEdgeState q r) = fermiEdgeLevels q r := by
  ext j
  simp only [occupiedLevels, fermiEdgeState, fermiEdgeEmbedding, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨i, ⟨k, _, rfl⟩, rfl⟩
    exact k.property
  · intro hj
    exact ⟨⟨j, fermiEdgeLevels_lt q r j hj⟩, ⟨⟨j, hj⟩, mem_attach _ _, rfl⟩, rfl⟩

/-- Precisely `q` particles cross the edge in the nearest-excitation configuration. -/
theorem fermiExcitationNumber_edge (q r : ℕ) :
    fermiExcitationNumber (fermiEdgeState q r) = q := by
  rw [fermiExcitationNumber, occupiedLevels_fermiEdgeState]
  have he : fermiEdgeLevels q r \ Ico (q + r) (2 * (q + r)) = Ico r (q + r) := by
    ext j
    simp only [fermiEdgeLevels, mem_sdiff, mem_union, mem_Ico]
    omega
  rw [he, Nat.card_Ico]
  omega

private theorem two_mul_sum_Ico (a n : ℕ) :
    2 * (∑ j ∈ Ico a (a + n), (j : ℝ)) = (n : ℝ) * (2 * a + n - 1) := by
  induction n with
  | zero => simp only [add_zero, Ico_self, sum_empty, mul_zero, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [Nat.add_succ, sum_Ico_succ_top (by omega)]
    push_cast
    nlinarith only [ih]

/-- The quadratic lower bound is attained at every excitation number and every larger half filling. -/
theorem fermiExcitationCost_edge (q r : ℕ) :
    fermiExcitationCost (fermiEdgeState q r) = (q : ℝ) ^ 2 := by
  rw [fermiExcitationCost, occupiedLevels_fermiEdgeState, fermiEdgeLevels,
    sum_union (edge_intervals_disjoint q r)]
  have htop := two_mul_sum_Ico (q + r) (q + r)
  have hlo := two_mul_sum_Ico r q
  have hhi := two_mul_sum_Ico (2 * q + r) r
  rw [show q + r + (q + r) = 2 * (q + r) by omega] at htop
  rw [show r + q = q + r by omega] at hlo
  rw [show 2 * q + r + r = 2 * (q + r) by omega] at hhi
  push_cast at htop hlo hhi
  linarith only [htop, hlo, hhi]

/-- Exact minimum excitation cost, realized by an explicit state in the existing fermionic basis. -/
theorem fermi_quadratic_cost_is_sharp (q r : ℕ) :
    ∃ S : Set.powersetCard (Fin (2 * (q + r))) (q + r),
      fermiExcitationNumber S = q ∧ fermiExcitationCost S = (q : ℝ) ^ 2 ∧
      ∀ T : Set.powersetCard (Fin (2 * (q + r))) (q + r),
        fermiExcitationNumber T = q → fermiExcitationCost S ≤ fermiExcitationCost T := by
  refine ⟨fermiEdgeState q r, fermiExcitationNumber_edge q r,
    fermiExcitationCost_edge q r, ?_⟩
  intro T hT
  rw [fermiExcitationCost_edge]
  simpa only [hT] using fermiExcitationNumber_sq_le_cost T

end RHTower.ParityForecast



