import GaloisForLFunctions.RHTower.Sieve.LogWindowMultiplicative

/-!
# A linear window inside a multiplicative one

A multiplicative window `(x, y]` with `x + L ≤ y` splits exactly into the linear window `(x, x+L]`
and the excess `(x+L, y]`:

    ∑_{x < n ≤ y} a_n = ∑_{x < n ≤ x+L} a_n + ∑_{x+L < n ≤ y} a_n .

Signed sums admit no comparison by containment, but this identity gives one at the cost of the
excess, and the excess is controlled trivially by its cardinality whenever the coefficients are
bounded.  Choosing the multiplicative ratio so that the excess is a small proportion of `L` is what
transfers a bound for multiplicative windows to linear ones.
-/

namespace RHTower.Sieve

open Finset

/-- The multiplicative window splits into the linear window and the excess. -/
theorem sum_window_split (a : ℕ → ℂ) (s : Finset ℕ) {x L y : ℝ} (hL : 0 ≤ L) (h : x + L ≤ y) :
    (∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y), a n)
      = (∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L), a n)
        + ∑ n ∈ s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y), a n := by
  classical
  have hlow : (s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y)).filter
      (fun n : ℕ => (n : ℝ) ≤ x + L)
      = s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn, h1, _⟩, h3⟩
      exact ⟨hn, h1, h3⟩
    · rintro ⟨hn, h1, h2⟩
      exact ⟨⟨hn, h1, le_trans h2 h⟩, h2⟩
  have hhigh : (s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y)).filter
      (fun n : ℕ => ¬ ((n : ℝ) ≤ x + L))
      = s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y) := by
    ext n
    simp only [Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hn, _, h2⟩, h3⟩
      exact ⟨hn, h3, h2⟩
    · rintro ⟨hn, h1, h2⟩
      exact ⟨⟨hn, by linarith, h2⟩, h1⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y))
    (fun n : ℕ => (n : ℝ) ≤ x + L) a
  rw [hlow, hhigh] at hsplit
  exact hsplit.symm

/-- A sum of coefficients of modulus at most one is bounded by the number of terms. -/
theorem norm_sum_le_card (a : ℕ → ℂ) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (T : Finset ℕ) :
    ‖∑ n ∈ T, a n‖ ≤ (T.card : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun n _ => ha n) ?_
  rw [nsmul_eq_mul, mul_one]

/-- **A linear window is a multiplicative window up to the excess.** -/
theorem normSq_linear_le_multiplicative (a : ℕ → ℂ) (s : Finset ℕ) {x L y : ℝ} (hL : 0 ≤ L)
    (h : x + L ≤ y) :
    ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2
      ≤ 2 * ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y), a n‖ ^ 2
        + 2 * ‖∑ n ∈ s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y), a n‖ ^ 2 := by
  classical
  set A : ℂ := ∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y), a n with hA
  set B : ℂ := ∑ n ∈ s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y), a n with hB
  have hsum : (∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L), a n) = A - B := by
    rw [hA, hB, sum_window_split a s hL h]
    ring
  rw [hsum]
  have htri : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le A B
  have h0 : (0 : ℝ) ≤ ‖A - B‖ := norm_nonneg _
  nlinarith [htri, h0, norm_nonneg A, norm_nonneg B, sq_nonneg (‖A‖ - ‖B‖)]

/-- **The transfer, with the excess bounded trivially.** -/
theorem normSq_linear_le_multiplicative_card (a : ℕ → ℂ) (s : Finset ℕ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) {x L y : ℝ} (hL : 0 ≤ L) (h : x + L ≤ y) :
    ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2
      ≤ 2 * ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y), a n‖ ^ 2
        + 2 * ((s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y)).card : ℝ) ^ 2 := by
  classical
  refine le_trans (normSq_linear_le_multiplicative a s hL h) ?_
  have hcard := norm_sum_le_card a ha (s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y))
  have h0 : (0 : ℝ) ≤ ‖∑ n ∈ s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y), a n‖ :=
    norm_nonneg _
  nlinarith [hcard, h0]

/-- The number of integers in a real window is at most its length plus one. -/
theorem card_window_le (s : Finset ℕ) {c y : ℝ} (hc : 0 ≤ c) (hcy : c ≤ y) :
    ((s.filter (fun n : ℕ => c < (n : ℝ) ∧ (n : ℝ) ≤ y)).card : ℝ) ≤ y - c + 1 := by
  classical
  have hsub : s.filter (fun n : ℕ => c < (n : ℝ) ∧ (n : ℝ) ≤ y)
      ⊆ Finset.Ioc ⌊c⌋₊ ⌊y⌋₊ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨-, h1, h2⟩ := hn
    rw [Finset.mem_Ioc]
    exact ⟨(Nat.floor_lt hc).2 h1, Nat.le_floor h2⟩
  have hcard : (s.filter (fun n : ℕ => c < (n : ℝ) ∧ (n : ℝ) ≤ y)).card
      ≤ ⌊y⌋₊ - ⌊c⌋₊ := by
    have := Finset.card_le_card hsub
    rwa [Nat.card_Ioc] at this
  have hfl : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le (le_trans hc hcy)
  have hfc : c - 1 < ((⌊c⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one c
    linarith
  have hfloor : ⌊c⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hcy
  have hmono : ((⌊y⌋₊ - ⌊c⌋₊ : ℕ) : ℝ) = ((⌊y⌋₊ : ℕ) : ℝ) - ((⌊c⌋₊ : ℕ) : ℝ) := by
    rw [Nat.cast_sub hfloor]
  have hcast : ((s.filter (fun n : ℕ => c < (n : ℝ) ∧ (n : ℝ) ≤ y)).card : ℝ)
      ≤ ((⌊y⌋₊ - ⌊c⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

/-- **The transfer with the excess measured by its length.** -/
theorem normSq_linear_le_multiplicative_length (a : ℕ → ℂ) (s : Finset ℕ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) {x L y : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L) (h : x + L ≤ y) :
    ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2
      ≤ 2 * ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y), a n‖ ^ 2
        + 2 * (y - (x + L) + 1) ^ 2 := by
  classical
  refine le_trans (normSq_linear_le_multiplicative_card a s ha hL h) ?_
  have hcard := card_window_le s (c := x + L) (y := y) (by linarith) h
  have h0 : (0 : ℝ) ≤ ((s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y)).card : ℝ) :=
    Nat.cast_nonneg _
  nlinarith [hcard, h0]

end RHTower.Sieve
