import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitCompositions
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The dominant highest digit block

At most p−1 occurrences of each power are permitted. The full collection
below exponent k has value `p^k−1`, so every subcollection below k has
value strictly less than `p^k`.

The whole highest digit block of a nonempty collection consequently carries
more than half its total value. Its content in every residue class is at
most p−1, making it an admissible layer for the inverse-content bounds.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- All permitted occurrences of powers strictly below p^k. -/
def digitsBelow (p k : ℕ) : Finset (Digit p) := (range k).product univ

theorem value_digitsBelow (p k : ℕ) (hp : 1 ≤ p) :
    digitValue p (digitsBelow p k) = (p : ℤ) ^ k - 1 := by
  have hgeom (n : ℕ) : (∑ e ∈ range n, ((p : ℤ) - 1) * (p : ℤ) ^ e) =
      (p : ℤ) ^ n - 1 := by
    induction n with
    | zero => simp only [range_zero, sum_empty, pow_zero, sub_self]
    | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring
  simpa only [digitsBelow, digitValue, tokenValue, product_eq_sprod, sum_product, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hp, Nat.cast_one] using hgeom k

/-- A base-p digit collection supported below k has value strictly less than p^k. -/
theorem digitValue_lt_pow {p k : ℕ} (hp : 1 ≤ p) (S : Finset (Digit p))
    (hS : ∀ x ∈ S, x.1 < k) : digitValue p S < (p : ℤ) ^ k := by
  have hsub : S ⊆ digitsBelow p k := by
    intro x hx
    exact mem_product.mpr ⟨mem_range.mpr (hS x hx), mem_univ x.2⟩
  have hle := tokenValue_subset p Prod.fst hsub
  change digitValue p S ≤ digitValue p (digitsBelow p k) at hle
  rw [value_digitsBelow p k hp] at hle
  omega

/-- All occurrences of a specified power in a digit collection. -/
def digitBlock (S : Finset (Digit p)) (k : ℕ) : Finset (Digit p) := S.filter fun x => x.1 = k

theorem card_digitBlock_le (S : Finset (Digit p)) (k : ℕ) : (digitBlock S k).card ≤ p - 1 := by
  have hsub : digitBlock S k ⊆ ({k} : Finset ℕ).product (univ : Finset (Fin (p - 1))) := by
    intro x hx
    exact mem_product.mpr ⟨mem_singleton.mpr (mem_filter.mp hx).2, mem_univ x.2⟩
  have hh := card_le_card hsub
  simpa only [product_eq_sprod, card_product, card_singleton, card_univ, Fintype.card_fin, one_mul] using hh

theorem content_digitBlock_le {s : ℕ} (S : Finset (Digit p)) (k : ℕ) (h : ZMod s) :
    tokenContent (fun x : Digit p => (x.1 : ZMod s)) (digitBlock S k) h ≤ (p - 1 : ℕ) := by
  dsimp only [tokenContent]
  exact_mod_cast (card_le_card (filter_subset _ _)).trans (card_digitBlock_le S k)

/-- A nonempty digit block has value at least that of one of its powers. -/
theorem pow_le_value_digitBlock (S : Finset (Digit p)) (k : ℕ)
    (hne : (digitBlock S k).Nonempty) : (p : ℤ) ^ k ≤ digitValue p (digitBlock S k) := by
  obtain ⟨x, hx⟩ := hne
  have hle := tokenValue_subset p Prod.fst (singleton_subset_iff.mpr hx)
  simpa only [digitValue, tokenValue, sum_singleton, (mem_filter.mp hx).2] using hle

/-- The highest digit block contains more than half the value of the entire digit collection. -/
theorem value_lt_two_mul_top_block {p : ℕ} (hp : 1 ≤ p) (S : Finset (Digit p)) (k : ℕ)
    (hmax : ∀ x ∈ S, x.1 ≤ k) (hne : (digitBlock S k).Nonempty) :
    digitValue p S < 2 * digitValue p (digitBlock S k) := by
  have hrest : ∀ x ∈ S \ digitBlock S k, x.1 < k := by
    intro x hx
    have hle := hmax x (mem_sdiff.mp hx).1
    have hn : x.1 ≠ k := by
      intro he
      exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1, he⟩)
    omega
  have hlow := digitValue_lt_pow hp (S \ digitBlock S k) hrest
  have htop := pow_le_value_digitBlock S k hne
  have he := tokenValue_sdiff p Prod.fst (filter_subset (fun x : Digit p => x.1 = k) S)
  change digitValue p (S \ digitBlock S k) + digitValue p (digitBlock S k) = digitValue p S at he
  linarith only [hlow, htop, he]

/-- Every nonempty digit collection has a highest block carrying more than half its value. -/
theorem exists_dominant_digitBlock {p : ℕ} (hp : 1 ≤ p) (S : Finset (Digit p)) (hS : S.Nonempty) :
    ∃ k, (∀ x ∈ S, x.1 ≤ k) ∧ (digitBlock S k).Nonempty ∧
      digitValue p S < 2 * digitValue p (digitBlock S k) := by
  obtain ⟨x, hx, hmax⟩ := S.exists_max_image Prod.fst hS
  have hne : (digitBlock S x.1).Nonempty := ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  exact ⟨x.1, hmax, hne, value_lt_two_mul_top_block hp S x.1 hmax hne⟩

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.exists_dominant_digitBlock
