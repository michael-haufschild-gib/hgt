import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Pi

/-! # Occupation intervals in a sector of prescribed total degree -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount

open Finset

variable {I : Type*} [Fintype I]

def capacity (c : I → ℕ) := ∑ i, c i

/-- Occupations obey the coordinate caps and have exactly the prescribed particle number. -/
abbrev State (c : I → ℕ) (m : ℕ) :=
  {x : (i : I) → Fin (c i + 1) // ∑ i, (x i : ℕ) = m}

def count {c : I → ℕ} {m : ℕ} (x : State c m) (i : I) : ℕ := (x.val i).val

theorem count_cap {c : I → ℕ} {m : ℕ} (x : State c m) (i : I) : count x i ≤ c i :=
  Nat.le_of_lt_succ (x.val i).isLt

theorem count_sum {c : I → ℕ} {m : ℕ} (x : State c m) : (∑ i, count x i) = m := x.property

theorem state_ext {c : I → ℕ} {m : ℕ} {x y : State c m}
    (h : ∀ i, count x i = count y i) : x = y :=
  Subtype.ext (funext fun i => Fin.ext (h i))

private def pack {c : I → ℕ} {m : ℕ} (x : I → ℕ)
    (hc : ∀ i, x i ≤ c i) (hm : ∑ i, x i = m) : State c m :=
  ⟨fun i => ⟨x i, Nat.lt_succ_of_le (hc i)⟩, hm⟩

def lower (c : I → ℕ) (m : ℕ) (i : I) := m - (capacity c - c i)

def upper (c : I → ℕ) (m : ℕ) (i : I) := min m (c i)

def pairCount (c : I → ℕ) (m : ℕ) (i : I) := lower c m i + upper c m i

omit [Fintype I] in
private theorem update_cap [DecidableEq I] {c f : I → ℕ} (hf : ∀ j, f j ≤ c j)
    {i : I} {k : ℕ} (hk : k ≤ c i) (j : I) : Function.update f i k j ≤ c j := by
  by_cases h : j = i
  · subst j; simpa only [Function.update_self] using hk
  · simpa only [Function.update_of_ne h] using hf j

omit [Fintype I] in
/-- Successively fill each coordinate up to its cap or the remaining total. -/
private theorem fill (c : I → ℕ) (A : Finset I) {m : ℕ} (hm : m ≤ ∑ i ∈ A, c i) :
    ∃ f : I → ℕ, (∀ i, f i ≤ c i) ∧ ∑ i ∈ A, f i = m := by
  classical
  induction A using Finset.induction_on generalizing m with
  | empty =>
    refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_⟩
    rw [sum_empty] at hm ⊢
    omega
  | @insert i A hi ih =>
    rw [sum_insert hi] at hm
    have rem : m - min m (c i) ≤ ∑ j ∈ A, c j := by omega
    obtain ⟨f, hf, hsum⟩ := ih rem
    refine ⟨Function.update f i (min m (c i)), update_cap hf (min_le_right _ _), ?_⟩
    rw [sum_insert hi, Function.update_self, sum_update_of_notMem hi, hsum]
    omega

theorem feasible_iff (c : I → ℕ) (m : ℕ) : Nonempty (State c m) ↔ m ≤ capacity c := by
  constructor
  · rintro ⟨x⟩
    exact (count_sum x) ▸ sum_le_sum (fun i _ => count_cap x i)
  · intro hm
    obtain ⟨f, hf, hs⟩ := fill c univ hm
    exact ⟨pack f hf hs⟩

theorem count_interval {c : I → ℕ} {m : ℕ} (x : State c m) (i : I) :
    lower c m i ≤ count x i ∧ count x i ≤ upper c m i := by
  classical
  have hc := sum_erase_add univ c (mem_univ i)
  have hx := sum_erase_add univ (count x) (mem_univ i)
  have hrest := sum_le_sum (s := univ.erase i) (fun j _ => count_cap x j)
  rw [count_sum] at hx
  have hi := count_cap x i
  unfold lower upper capacity
  omega

/-- Every integer between the two stated bounds occurs at the specified coordinate. -/
theorem coordinate_values (c : I → ℕ) (m : ℕ) (i : I) (k : ℕ) :
    (∃ x : State c m, count x i = k) ↔ lower c m i ≤ k ∧ k ≤ upper c m i := by
  classical
  constructor
  · rintro ⟨x, rfl⟩; exact count_interval x i
  · rintro ⟨hl, hu⟩
    have hc := sum_erase_add univ c (mem_univ i)
    unfold lower capacity at hl
    unfold upper at hu
    have hr : m - k ≤ ∑ j ∈ univ.erase i, c j := by omega
    obtain ⟨f, hf, hs⟩ := fill c _ hr
    let g := Function.update f i k
    have hg : ∑ j, g j = m := by
      rw [← sum_erase_add univ g (mem_univ i)]
      change (∑ j ∈ univ.erase i, Function.update f i k j) + Function.update f i k i = m
      rw [sum_update_of_notMem (notMem_erase _ _), Function.update_self, hs]
      omega
    refine ⟨pack g (update_cap hf (by omega)) hg, ?_⟩
    exact Function.update_self i k f

/-- Even a self-map with constant paired occupations must use the coordinate endpoint sums. -/
theorem forced_pair_count {c : I → ℕ} {m : ℕ} (hx : Nonempty (State c m))
    (f : State c m → State c m) (a : I → ℕ)
    (h : ∀ x i, count x i + count (f x) i = a i) : a = pairCount c m := by
  obtain ⟨z⟩ := hx
  funext i
  have hle := (count_interval z i).1.trans (count_interval z i).2
  obtain ⟨v, hv⟩ := (coordinate_values c m i _).2 ⟨le_rfl, hle⟩
  obtain ⟨w, hw⟩ := (coordinate_values c m i _).2 ⟨hle, le_rfl⟩
  have hi := (count_interval (f v) i).2
  have lo := (count_interval (f w) i).1
  have ev := h v i
  have ew := h w i
  unfold pairCount
  omega

private theorem count_le_pair {c : I → ℕ} {m : ℕ} (x : State c m) (i : I) :
    count x i ≤ pairCount c m i := (count_interval x i).2.trans (Nat.le_add_left _ _)

/-- Coordinate reflection preserves the fixed particle number when the endpoint sums total 2m. -/
def partner {c : I → ℕ} {m : ℕ} (h : ∑ i, pairCount c m i = 2*m) (x : State c m) : State c m :=
  pack (fun i => pairCount c m i - count x i) (fun i => by
    have lo := (count_interval x i).1
    have up : upper c m i ≤ c i := min_le_right _ _
    unfold pairCount
    omega) (by
    rw [sum_tsub_distrib _ (fun i _ => count_le_pair x i), h, count_sum]
    omega)

theorem partner_pair {c : I → ℕ} {m : ℕ} (h : ∑ i, pairCount c m i = 2*m)
    (x : State c m) (i : I) : count x i + count (partner h x) i = pairCount c m i :=
  Nat.add_sub_of_le (count_le_pair x i)

/-- The canonical partner acts involutively on the actual bounded occupations. -/
def reversal {c : I → ℕ} {m : ℕ} (h : ∑ i, pairCount c m i = 2*m) : Equiv.Perm (State c m) :=
  let inv : Function.Involutive (partner h) := fun x => state_ext fun i => by
    have h₁ := partner_pair h x i
    have h₂ := partner_pair h (partner h x) i
    omega
  ⟨partner h, partner h, inv, inv⟩

#print axioms coordinate_values
#print axioms forced_pair_count
#print axioms reversal

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount
