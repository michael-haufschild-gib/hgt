import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TopDigits
import Mathlib.Order.Interval.Finset.Nat

/-!
# Residue-prefix cardinality gaps force exponent gaps

In a fixed residue class, each exponent has at most `p−1` digit occurrences.
Removing `n(p−1)` largest occurrences therefore lowers every retained
exponent by at least `ns`. Consecutive positive prefix gaps accumulate.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss


/-- The quotient by the residue degree injects a fixed residue's digits into
an interval of levels, each with at most `p−1` occurrences. -/
theorem card_residue_quotient_interval_le (p s r a b : ℕ) (S : Finset (Digit p))
    (hres : ∀ x ∈ S, x.1 % s = r)
    (hbound : ∀ x ∈ S, a ≤ x.1 / s ∧ x.1 / s ≤ b) :
    S.card ≤ (b + 1 - a) * (p - 1) := by
  let f : Digit p → Digit p := fun x => (x.1 / s, x.2)
  have hinj : Set.InjOn f (↑S : Set (Digit p)) := by
    intro x hx y hy he
    change (x.1 / s, x.2) = (y.1 / s, y.2) at he
    obtain ⟨hq, hl⟩ := Prod.mk.inj he
    apply Prod.ext _ hl
    have hxid := Nat.mod_add_div x.1 s
    have hyid := Nat.mod_add_div y.1 s
    rw [hres x hx, hq] at hxid
    rw [hres y hy] at hyid
    omega
  have hsub : S.image f ⊆ (Icc a b).product (univ : Finset (Fin (p - 1))) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    exact mem_product.mpr ⟨mem_Icc.mpr (hbound x hx), mem_univ _⟩
  have hc := card_le_card hsub
  simpa only [card_image_of_injOn hinj, product_eq_sprod, card_product,
    Nat.card_Icc, card_univ, Fintype.card_fin] using hc

/-- Deleting `n(p−1)` largest digits of one residue lowers every retained
exponent by at least `ns` below the terminal maximum. -/
theorem exponent_gap_of_prefix_card_gap {p s r n E : ℕ}
    {A B : Finset (Digit p)} (hAB : A ⊆ B)
    (hres : ∀ z ∈ B, z.1 % s = r) (hEres : E % s = r)
    (hmax : ∀ z ∈ B, z.1 ≤ E)
    (hsmall : ∀ z ∈ A, ∀ y ∈ B \ A, z.1 ≤ y.1)
    (hcard : A.card + n * (p - 1) ≤ B.card) {x : Digit p} (hx : x ∈ A) :
    x.1 + n * s ≤ E := by
  let T := insert x (B \ A)
  have hxnot : x ∉ B \ A := fun h => (mem_sdiff.mp h).2 hx
  have hTsub : T ⊆ B := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hAB hx
    · exact (mem_sdiff.mp hz).1
  have hTbelow (z : Digit p) (hz : z ∈ T) : x.1 ≤ z.1 := by
    rcases mem_insert.mp hz with rfl | hz
    · exact le_rfl
    · exact hsmall x hx z hz
  have hc := card_residue_quotient_interval_le p s r (x.1 / s) (E / s) T
    (fun z hz => hres z (hTsub hz))
    (fun z hz => ⟨Nat.div_le_div_right (hTbelow z hz),
      Nat.div_le_div_right (hmax z (hTsub hz))⟩)
  have hsize : n * (p - 1) + 1 ≤ T.card := by
    rw [show T = insert x (B \ A) from rfl, card_insert_of_notMem hxnot, card_sdiff_of_subset hAB]
    omega
  have hlt : n * (p - 1) < (E / s + 1 - x.1 / s) * (p - 1) := by omega
  have hn : n < E / s + 1 - x.1 / s := Nat.lt_of_mul_lt_mul_right hlt
  have hquot : x.1 / s + n ≤ E / s := by
    have hle := Nat.div_le_div_right (hmax x (hAB hx)) (c := s)
    omega
  have hm := Nat.mul_le_mul_left s hquot
  have hxid := Nat.mod_add_div x.1 s
  have hEid := Nat.mod_add_div E s
  rw [hres x (hAB hx)] at hxid
  rw [hEres] at hEid
  nlinarith only [hm, hxid, hEid]

/-- A nonempty prefix accumulates the same digit-count gap at each later step. -/
theorem card_gap_of_positive_prefixes {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (b : ℕ)
    (hgap : ∀ i, (A i).Nonempty → (A i).card + b ≤ (A (i + 1)).card)
    {j : ℕ} (hj : (A j).Nonempty) :
    ∀ n, (A j).card + n * b ≤ (A (j + n)).card := by
  intro n
  induction n with
  | zero => simp only [zero_mul, add_zero, le_refl]
  | succ n ih =>
    have hn : (A (j + n)).Nonempty := by
      apply card_pos.mp
      have hpos := card_pos.mpr hj
      omega
    have hg := hgap (j + n) hn
    rw [Nat.succ_mul]
    have hi : j + (n + 1) = (j + n) + 1 := by omega
    rw [hi]
    omega

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.exponent_gap_of_prefix_card_gap
