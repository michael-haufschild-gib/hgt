import Mathlib
import GaloisForLFunctions.RHTower.GibbsTruncationSection

/-!
# Energy spread obstructs the truncation mechanism

The truncation lemma needs a clean light/heavy dichotomy: every configuration of at most
`J` elements light, every larger one heavy.  That is only possible when the *heaviest*
`J`-configuration is lighter than the *lightest* `(J+1)`-configuration — an ordering of
energies by cardinality alone.  A set whose elements span a wide range violates it: a
single large element can outweigh a whole primorial.

So the instability produced by the truncation mechanism requires an energy-degenerate
element set (all elements comparable, as in a dyadic window).  The arithmetically natural
gas, whose elements are all primes up to a bound, is energy-spread and admits no
dichotomy at any level — already `{2, 3, 7} ⊆ S` blocks level one, since `2·3 ≤ 7`.
-/

namespace RHTower.GibbsGas

/-- **The dichotomy obstruction.**  A `(J+1)`-configuration no heavier than some
`J`-configuration is incompatible with any light/heavy dichotomy at level `J`. -/
theorem no_truncation_dichotomy (S : Finset ℕ) (x : ℝ) (hx : 0 ≤ x) (J : ℕ) (ε R : ℝ)
    (hεR : ε < R)
    (T₁ T₂ : Finset ℕ) (h₁ : T₁ ∈ S.powerset) (h₂ : T₂ ∈ S.powerset)
    (hc₁ : T₁.card ≤ J) (hc₂ : J < T₂.card)
    (hle : ∏ p ∈ T₂, (p : ℝ) ≤ ∏ p ∈ T₁, (p : ℝ))
    (hlight : ∀ T ∈ S.powerset, T.card ≤ J → x * ∏ p ∈ T, (p : ℝ) ≤ ε)
    (hheavy : ∀ T ∈ S.powerset, J < T.card → R ≤ x * ∏ p ∈ T, (p : ℝ)) :
    False := by
  have hR := hheavy T₂ h₂ hc₂
  have hε := hlight T₁ h₁ hc₁
  have hmid : x * ∏ p ∈ T₂, (p : ℝ) ≤ x * ∏ p ∈ T₁, (p : ℝ) :=
    mul_le_mul_of_nonneg_left hle hx
  linarith

/-- **Level one is blocked by a single dominant element.**  If `S` contains two elements
whose product is at most a third element, no dichotomy at level one exists. -/
theorem no_truncation_dichotomy_of_dominant (S : Finset ℕ) (x : ℝ) (hx : 0 ≤ x)
    (ε R : ℝ) (hεR : ε < R) (a b c : ℕ)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b)
    (hdom : ((a : ℝ)) * (b : ℝ) ≤ (c : ℝ))
    (hlight : ∀ T ∈ S.powerset, T.card ≤ 1 → x * ∏ p ∈ T, (p : ℝ) ≤ ε)
    (hheavy : ∀ T ∈ S.powerset, 1 < T.card → R ≤ x * ∏ p ∈ T, (p : ℝ)) :
    False := by
  classical
  refine no_truncation_dichotomy S x hx 1 ε R hεR {c} {a, b} ?_ ?_ ?_ ?_ ?_
    hlight hheavy
  · rw [Finset.mem_powerset, Finset.singleton_subset_iff]
    exact hc
  · rw [Finset.mem_powerset, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha, hb⟩
  · rw [Finset.card_singleton]
  · rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
    omega
  · rw [Finset.prod_insert (by simpa using hab), Finset.prod_singleton,
      Finset.prod_singleton]
    exact hdom

/-- The natural gas contains a dominant configuration already at the third prime:
`2 · 3 ≤ 7`. -/
theorem no_truncation_dichotomy_of_two_three_seven (S : Finset ℕ) (x : ℝ) (hx : 0 ≤ x)
    (ε R : ℝ) (hεR : ε < R)
    (h2 : 2 ∈ S) (h3 : 3 ∈ S) (h7 : 7 ∈ S)
    (hlight : ∀ T ∈ S.powerset, T.card ≤ 1 → x * ∏ p ∈ T, (p : ℝ) ≤ ε)
    (hheavy : ∀ T ∈ S.powerset, 1 < T.card → R ≤ x * ∏ p ∈ T, (p : ℝ)) :
    False := by
  refine no_truncation_dichotomy_of_dominant S x hx ε R hεR 2 3 7 h2 h3 h7
    (by norm_num) ?_ hlight hheavy
  norm_num

end RHTower.GibbsGas
