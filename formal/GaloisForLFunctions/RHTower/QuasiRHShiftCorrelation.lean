import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Power degeneracies of shifted sextic correlations

A character correlation with fewer than `m` shifts on either side has an
`m`-th-power polynomial precisely when the two shift multisets coincide.
For the sextic fourth moment this leaves the two matching diagonals, with
exactly `2H²-H` exceptional ordered quadruples in a shift set of size `H`.
-/

noncomputable section

namespace RHTower.QuasiRHShiftCorrelation

open Polynomial Finset

variable {K : Type*} [Field K]

/-- Polynomial representing positive shifts and `m-1` conjugate shifts. -/
def shiftCorrelationPolynomial (m : ℕ) (s t : Multiset K) : K[X] :=
  ofMultiset s * ofMultiset t ^ (m - 1)

private theorem ofMultiset_ne_zero (s : Multiset K) : ofMultiset s ≠ 0 := by
  change (s.map (fun a => (X : K[X]) - C a)).prod ≠ 0
  rw [ne_eq, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  rintro ⟨a, _, h⟩
  exact X_sub_C_ne_zero a h

/-- Below order `m`, equal root counts modulo `m` are equal root counts. -/
theorem shiftCorrelationPolynomial_power_iff {m : ℕ} (hm : 0 < m)
    (s t : Multiset K) (hs : s.card < m) (ht : t.card < m) :
    (∃ Q : K[X], Q ^ m = shiftCorrelationPolynomial m s t) ↔ s = t := by
  classical
  constructor
  · rintro ⟨Q, hQ⟩
    have hr := congrArg Polynomial.roots hQ
    rw [roots_pow, shiftCorrelationPolynomial,
      roots_mul (mul_ne_zero (ofMultiset_ne_zero s)
        (pow_ne_zero _ (ofMultiset_ne_zero t))),
      roots_ofMultiset, roots_pow, roots_ofMultiset] at hr
    apply Multiset.ext.mpr
    intro u
    have hc := congrArg (Multiset.count u) hr
    simp only [Multiset.count_nsmul, Multiset.count_add] at hc
    have hs' : s.count u < m := (Multiset.count_le_card u s).trans_lt hs
    have ht' : t.count u < m := (Multiset.count_le_card u t).trans_lt ht
    have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have he : s.count u + m * t.count u = m * Q.roots.count u + t.count u := by
      calc
        _ = (s.count u + (m - 1) * t.count u) + t.count u := by
          conv_lhs => rw [← hm']
          ring
        _ = _ := by rw [← hc]
    have he' := congrArg (fun n : ℕ => n % m) he
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
      add_zero, zero_add, Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt ht'] using he'
  · rintro rfl
    refine ⟨ofMultiset s, ?_⟩
    rw [shiftCorrelationPolynomial, ← pow_succ', Nat.sub_add_cancel hm]

private theorem pair_multiset_eq_iff {α : Type*} (a b c d : α) :
    ({a, b} : Multiset α) = {c, d} ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a = c ∨ a = d := by
      have : a ∈ ({c, d} : Multiset α) := h ▸ (by simp)
      simpa using this
    rcases ha with rfl | rfl
    · exact Or.inl ⟨rfl, by simpa using h⟩
    · exact Or.inr ⟨rfl, by simpa [Multiset.pair_comm c a] using h⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Multiset.pair_comm _ _

/-- The polynomial of a four-shift sextic correlation, including repeated shifts. -/
def sexticCorrelationPolynomial (a b c d : K) : K[X] :=
  shiftCorrelationPolynomial 6 {a, b} {c, d}

theorem sexticCorrelationPolynomial_eq (a b c d : K) :
    sexticCorrelationPolynomial a b c d =
      (X - C a) * (X - C b) * (X - C c) ^ 5 * (X - C d) ^ 5 := by
  simp [sexticCorrelationPolynomial, shiftCorrelationPolynomial, ofMultiset_apply, mul_pow,
    mul_assoc]

/-- A sixth-power correlation polynomial occurs exactly on the matching diagonals. -/
theorem sexticCorrelationPolynomial_power_iff (a b c d : K) :
    (∃ Q : K[X], Q ^ 6 = sexticCorrelationPolynomial a b c d) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [sexticCorrelationPolynomial,
    shiftCorrelationPolynomial_power_iff (by norm_num) _ _ (by simp) (by simp)]
  exact pair_multiset_eq_iff a b c d

/-- Ordered shift quadruples whose correlation polynomial is a sixth power. -/
def sexticExceptionalTuples (S : Finset K) : Finset ((K × K) × (K × K)) := by
  classical
  exact ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun p =>
    ∃ Q : K[X], Q ^ 6 = sexticCorrelationPolynomial p.1.1 p.1.2 p.2.1 p.2.2

/-- The overlap of the two matching diagonals consists of the constant quadruples. -/
theorem sexticExceptionalTuples_card (S : Finset K) :
    (sexticExceptionalTuples S).card + S.card = 2 * S.card ^ 2 := by
  classical
  let D := (S ×ˢ S).image (fun p : K × K => (p, p))
  let E := (S ×ˢ S).image (fun p : K × K => (p, p.swap))
  have hDE : sexticExceptionalTuples S = D ∪ E := by
    ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [sexticExceptionalTuples, mem_filter, mem_product,
      sexticCorrelationPolynomial_power_iff, mem_union, D, E, mem_image, Prod.exists,
      Prod.mk.injEq, Prod.swap_prod_mk]
    aesop
  have hI : D ∩ E = S.image (fun a => ((a, a), (a, a))) := by
    ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [mem_inter, D, E, mem_image, mem_product, Prod.exists,
      Prod.mk.injEq, Prod.swap_prod_mk]
    aesop
  have hD : D.card = S.card * S.card := by
    rw [show D.card = (S ×ˢ S).card from card_image_iff.mpr
      (fun p _ q _ h => congrArg Prod.fst h), card_product]
  have hE : E.card = S.card * S.card := by
    rw [show E.card = (S ×ˢ S).card from card_image_iff.mpr
      (fun p _ q _ h => congrArg Prod.fst h), card_product]
  have hIc : (D ∩ E).card = S.card := by
    rw [hI]
    exact card_image_iff.mpr (fun a _ b _ h => congrArg (fun p => p.1.1) h)
  have hc := card_union_add_card_inter D E
  rw [hIc, hD, hE] at hc
  rw [hDE]
  nlinarith

/-- Complex conjugation of a sextic character is its fifth power, also at zero. -/
theorem sexticCharacter_star [Finite K] (χ : MulChar K ℂ) (hχ : χ ^ 6 = 1) (x : K) :
    star (χ x) = χ x ^ 5 := by
  have hi : χ⁻¹ = χ ^ 5 := inv_eq_of_mul_eq_one_right (by
    rw [← pow_succ']
    exact hχ)
  rw [MulChar.star_apply', hi, MulChar.pow_apply' χ (by norm_num)]

/-- Exact polynomial form of the four-shift integrand; no distinctness is required. -/
theorem sexticCorrelationPolynomial_character [Finite K]
    (χ : MulChar K ℂ) (hχ : χ ^ 6 = 1) (a b c d x : K) :
    χ ((sexticCorrelationPolynomial a b c d).eval x) =
      χ (x - a) * χ (x - b) * star (χ (x - c) * χ (x - d)) := by
  rw [sexticCorrelationPolynomial_eq]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, map_mul, map_pow, star_mul,
    sexticCharacter_star χ hχ]
  ring

end RHTower.QuasiRHShiftCorrelation
