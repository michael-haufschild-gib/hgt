import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenForbiddenSupport

/-!
# Distinct `E₃` numbers in a dyadic slice

The all-interval theorem counts triples `(p₁, p₂, n)` with the weight `ρ⁻(n)`.  On the cofactor
windows `ρ⁻ ≤ 1_prime`, so after removing the diagonal `n = p₂` the weighted count is at most the
number of prime triples, and a product `p₁p₂n` with `p₁ ∈ (P, 2P]` below `p₂, n > R > 2P` has at most
two triples (`p₁` is its only small prime factor; `{p₂, n}` is determined up to order).  Hence
(`eventually_card_sliceTokens_ge`): for every `P ∈ [(log x)^{1.0999}, (log x)^{1.1}]` the natural
window `(x, x + √(xP) log x]` contains at least `√(xP) log x/(72000 log P (log x)²)` distinct
`E₃` numbers of the slice.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- **Unique factorisation of an `E₃` triple.**  If `p₁p₂n = p₁'p₂'n'` with five primes and each
small prime below the large primes of the other triple, then `p₁ = p₁'` and `{p₂, n} = {p₂', n'}`. -/
theorem threePrime_eq_of_mul_eq {p₁ p₂ n p₁' p₂' n' : ℕ} (h₁ : p₁.Prime) (h₂ : p₂.Prime)
    (h₁' : p₁'.Prime) (h₂' : p₂'.Prime) (h₃' : n'.Prime) (a : p₁ < p₂')
    (b : p₁ < n') (c : p₁' < p₂) (d : p₁' < n) (h : p₁ * p₂ * n = p₁' * p₂' * n') :
    p₁ = p₁' ∧ ((p₂ = p₂' ∧ n = n') ∨ (p₂ = n' ∧ n = p₂')) := by
  have hmem : ∀ {q r s t : ℕ}, q.Prime → r.Prime → s.Prime → t.Prime → q ∣ r * s * t →
      q = r ∨ q = s ∨ q = t := by
    intro q r s t hq hr hs ht hd
    rcases (Nat.Prime.dvd_mul hq).1 hd with h12 | h3
    · rcases (Nat.Prime.dvd_mul hq).1 h12 with h1 | h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hr).1 h1)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq hs).1 h2))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq ht).1 h3))
  have e1 : p₁ = p₁' := by
    rcases hmem h₁ h₁' h₂' h₃' (h ▸ dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) n) with e | e | e
    · exact e
    · omega
    · omega
  subst e1
  have h2 : p₂ * n = p₂' * n' := by
    have := h; rw [mul_assoc, mul_assoc] at this
    exact Nat.eq_of_mul_eq_mul_left h₁.pos this
  refine ⟨rfl, ?_⟩
  rcases (Nat.Prime.dvd_mul h₂).1 (h2 ▸ dvd_mul_right p₂ n) with hd | hd
  · have e := (Nat.prime_dvd_prime_iff_eq h₂ h₂').1 hd
    subst e
    exact Or.inl ⟨rfl, Nat.eq_of_mul_eq_mul_left h₂.pos h2⟩
  · have e := (Nat.prime_dvd_prime_iff_eq h₂ h₃').1 hd
    subst e
    refine Or.inr ⟨rfl, ?_⟩
    rw [mul_comm p₂' p₂] at h2
    exact Nat.eq_of_mul_eq_mul_left h₂.pos h2

/-- The triples `(p₁, p₂, n)` of an `E₃` slice: `p₁ ∈ B₁`, `p₂ ∈ B₂`, `n ≠ p₂` prime,
`x < p₁p₂n ≤ x + h`. -/
def sliceTriples (B₁ B₂ : Finset ℕ) (x h : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((B₁ ×ˢ B₂ ×ˢ Finset.Icc 1 ⌊x + h⌋₊)).filter fun t =>
    t.2.2.Prime ∧ t.2.2 ≠ t.2.1 ∧ x < ((t.1 * t.2.1 * t.2.2 : ℕ) : ℝ) ∧
      ((t.1 * t.2.1 * t.2.2 : ℕ) : ℝ) ≤ x + h

/-- The `E₃` numbers of a slice: the products `p₁p₂n` of its triples. -/
def sliceTokens (B₁ B₂ : Finset ℕ) (x h : ℝ) : Finset ℕ :=
  (sliceTriples B₁ B₂ x h).image fun t => t.1 * t.2.1 * t.2.2

/-- Each slice token has at most two triples, so `#triples ≤ 2 #tokens`, when all primes of
`B₁` lie below all primes of `B₂` and all cofactors of the window. -/
theorem card_sliceTriples_le {B₁ B₂ : Finset ℕ} {x h R : ℝ}
    (hB₁ : ∀ p ∈ B₁, p.Prime ∧ (p : ℝ) < R) (hB₂ : ∀ p ∈ B₂, p.Prime ∧ R < p)
    (hn : ∀ t ∈ sliceTriples B₁ B₂ x h, R < t.2.2) :
    (sliceTriples B₁ B₂ x h).card ≤ 2 * (sliceTokens B₁ B₂ x h).card := by
  classical
  refine Finset.card_le_mul_card_image _ 2 fun m _ => ?_
  -- a fibre is contained in two explicit points
  set F := (sliceTriples B₁ B₂ x h).filter fun t => t.1 * t.2.1 * t.2.2 = m
  rcases F.eq_empty_or_nonempty with hF | ⟨t₀, ht₀⟩
  · rw [hF]; simp
  have ht₀' := Finset.mem_filter.1 ht₀
  have hsub : F ⊆ {t₀, (t₀.1, t₀.2.2, t₀.2.1)} := by
    intro t ht
    obtain ⟨htS, htm⟩ := Finset.mem_filter.1 ht
    obtain ⟨htS', -⟩ := Finset.mem_filter.1 htS
    obtain ⟨ht₀S, ht₀m⟩ := ht₀'
    obtain ⟨ht₀S', -⟩ := Finset.mem_filter.1 ht₀S
    have hmemt := Finset.mem_product.1 (Finset.mem_filter.1 htS).1
    have hmemt₀ := Finset.mem_product.1 (Finset.mem_filter.1 ht₀S).1
    obtain ⟨a1, a2⟩ := hB₁ _ hmemt.1
    obtain ⟨b1, b2⟩ := hB₂ _ (Finset.mem_product.1 hmemt.2).1
    obtain ⟨a1', a2'⟩ := hB₁ _ hmemt₀.1
    obtain ⟨b1', b2'⟩ := hB₂ _ (Finset.mem_product.1 hmemt₀.2).1
    have c1 := hn t htS
    have c1' := hn t₀ ht₀S
    have lt : ∀ {p q : ℕ}, (p : ℝ) < R → R < q → p < q := fun hp hq => by
      exact_mod_cast hp.trans hq
    obtain ⟨e1, e2⟩ := threePrime_eq_of_mul_eq a1 b1 a1' b1'
      (Finset.mem_filter.1 ht₀S).2.1 (lt a2 b2') (lt a2 c1') (lt a2' b2) (lt a2' c1)
      (htm.trans ht₀m.symm)
    rcases e2 with ⟨e2, e3⟩ | ⟨e2, e3⟩
    · rw [Finset.mem_insert]; left
      exact Prod.ext e1 (Prod.ext e2 e3)
    · rw [Finset.mem_insert, Finset.mem_singleton]; right
      exact Prod.ext e1 (Prod.ext e2 e3)
  calc F.card ≤ ({t₀, (t₀.1, t₀.2.2, t₀.2.1)} : Finset (ℕ × ℕ × ℕ)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- The window of a pair as a filter of `[1, ⌊x + h⌋]`. -/
theorem window_eq_filter {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {p₁ p₂ : ℕ} (hp₁ : 0 < p₁)
    (hp₂ : 0 < p₂) :
    Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊ =
      (Finset.Icc 1 ⌊x + h⌋₊).filter fun n =>
        x < ((p₁ * p₂ * n : ℕ) : ℝ) ∧ ((p₁ * p₂ * n : ℕ) : ℝ) ≤ x + h := by
  have hq : (0 : ℝ) < (p₁ : ℝ) * p₂ := by positivity
  have hq1 : (1 : ℝ) ≤ (p₁ : ℝ) * p₂ := by
    have : (1 : ℝ) ≤ p₁ := by exact_mod_cast hp₁
    have : (1 : ℝ) ≤ p₂ := by exact_mod_cast hp₂
    nlinarith
  ext n
  rw [mem_Ioc_natFloor_div_iff hx (by linarith) hq, Finset.mem_filter, Finset.mem_Icc]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    have hn0 : (0 : ℝ) < n := by
      by_contra hc; push Not at hc
      have : (n : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
      rw [this, mul_zero] at h1; linarith
    refine ⟨⟨by exact_mod_cast hn0, Nat.le_floor ?_⟩, h1, h2⟩
    nlinarith
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩

/-- **The weighted slice sum is at most the number of triples.**  If `ρ⁻ ≤ 1_prime` on the windows,
the coprime `E₃` sum at `A = 1` is at most `#triples`. -/
theorem mtCoprimeE3Sum_one_le_card {B₁ B₂ : Finset ℕ} {z Q D E : ℕ} {x h : ℝ} (hx : 0 ≤ x)
    (hh : 0 ≤ h) (hB₁ : ∀ p ∈ B₁, 0 < p) (hB₂ : ∀ p ∈ B₂, 0 < p)
    (hρ1 : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂,
      ∀ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊,
        (rhoMinus z Q D E n : ℝ) ≤ if n.Prime then 1 else 0) :
    mtCoprimeE3Sum B₁ B₂ 1 z Q D E x h ≤ ((sliceTriples B₁ B₂ x h).card : ℝ) := by
  classical
  unfold mtCoprimeE3Sum
  have hcard : ((sliceTriples B₁ B₂ x h).card : ℝ) = ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂,
      (((Finset.Icc 1 ⌊x + h⌋₊).filter fun n => n.Prime ∧ n ≠ p₂ ∧
        x < ((p₁ * p₂ * n : ℕ) : ℝ) ∧ ((p₁ * p₂ * n : ℕ) : ℝ) ≤ x + h).card : ℝ) := by
    rw [sliceTriples, Finset.card_filter, Finset.sum_product]
    push_cast
    refine Finset.sum_congr rfl fun p₁ _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun p₂ _ => ?_
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hcard]
  refine Finset.sum_le_sum fun p₁ hp₁ => ?_
  calc ∑ p₂ ∈ B₂.filter (fun p => Nat.Coprime p 1),
        ∑ n ∈ (Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊).filter
          (fun n => Nat.Coprime n 1 ∧ n ≠ p₂), (rhoMinus z Q D E n : ℝ)
      ≤ ∑ p₂ ∈ B₂, ∑ n ∈ (Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊).filter
          (fun n => n ≠ p₂), (if n.Prime then (1 : ℝ) else 0) := by
        rw [Finset.filter_true_of_mem fun p _ => Nat.coprime_one_right p]
        refine Finset.sum_le_sum fun p₂ hp₂ => ?_
        rw [show ((Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊).filter
          (fun n => Nat.Coprime n 1 ∧ n ≠ p₂)) = ((Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊
            ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊).filter (fun n => n ≠ p₂)) by
          ext n; simp]
        exact Finset.sum_le_sum fun n hn => hρ1 p₁ hp₁ p₂ hp₂ n (Finset.mem_filter.1 hn).1
    _ = ∑ p₂ ∈ B₂, (((Finset.Icc 1 ⌊x + h⌋₊).filter fun n => n.Prime ∧ n ≠ p₂ ∧
          x < ((p₁ * p₂ * n : ℕ) : ℝ) ∧ ((p₁ * p₂ * n : ℕ) : ℝ) ≤ x + h).card : ℝ) := by
        refine Finset.sum_congr rfl fun p₂ hp₂ => ?_
        rw [window_eq_filter hx hh (hB₁ p₁ hp₁) (hB₂ p₂ hp₂), Finset.filter_filter,
          ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
        congr 2
        ext n; simp only [Finset.mem_filter]; tauto

/-- **The windows of the all-interval sum at one `x`.**  Under the scale facts, every cofactor
`n` of a window `(x/(p₁p₂), (x+h)/(p₁p₂)]`, `p₁ ∈ (P₁, 2P₁]`, `p₂ ∈ (R, 2R]`, `h = XL`, has
`R < n ≤ 6R` and `ρ⁻(n) ≤ 1_prime(n)`. -/
theorem mt_window_rho_facts {x L a P₁ ε : ℝ} {B₁ B₂ : Finset ℕ} (hx : 0 < x)
    (hL : L = Real.log x) (hL16 : 16 ≤ L) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a)
    (hε : 0 < ε) (h64 : 64 * L ^ 2 ≤ x) (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ))
    (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ)) (hL12 : 3 * L ≤ x ^ (1 / 12 : ℝ))
    (hz2 : 2 ≤ mtProposition22ZNat (Real.sqrt (x * P₁)))
    (hz6 : 4 * Real.sqrt (x * P₁) < (mtProposition22ZNat (Real.sqrt (x * P₁)) : ℝ) ^ 6)
    (hB₁ : ∀ p ∈ B₁, P₁ < p ∧ (p : ℝ) ≤ 2 * P₁)
    (hB₂ : ∀ p ∈ B₂, Real.sqrt (x / P₁) / 2 < p ∧ (p : ℝ) ≤ 2 * (Real.sqrt (x / P₁) / 2)) :
    ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂, ∀ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊
        ⌊(x + Real.sqrt (x * P₁) * L) / ((p₁ : ℝ) * p₂)⌋₊,
      Real.sqrt (x / P₁) / 2 < n ∧ (n : ℝ) ≤ 6 * (Real.sqrt (x / P₁) / 2) ∧
        (rhoMinus (mtProposition22ZNat (Real.sqrt (x * P₁))) (mtProposition22QNat (Real.sqrt (x * P₁)))
          (mtProposition22DNat (Real.sqrt (x * P₁)) ε) (mtProposition22ENat (Real.sqrt (x * P₁)) ε)
          n : ℝ) ≤ if n.Prime then 1 else 0 := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hX1, hPR, hxRX, hhx, hQR, -, hP2, -, -⟩ :=
    mt_forbidden_scales hx hL hL16 ha1 ha11 hP h64 hL2x hL6 hL12
  generalize hXg : Real.sqrt (x * P₁) = X at *
  generalize hRg : Real.sqrt (x / P₁) / 2 = R at *
  have hX0 : 0 < X := by linarith
  have hR0 : 0 < R := by
    have h1 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
    linarith
  have hwin := mt_window_facts (B₁ := B₁) (B₂ := B₂) (h := X * L) hx (by positivity) hhx hX0 hP2
    hR0 hPR hxRX hB₁ hB₂
  intro p₁ hp₁ p₂ hp₂ n hn
  obtain ⟨-, -, hW⟩ := hwin p₁ hp₁ p₂ hp₂
  obtain ⟨hnR, hnX, hn6⟩ := hW n hn
  exact ⟨hnR, hn6, (mt_rhoMinus_window_bounds hX1 hε hQR hz2 hz6 hnR hnX).2⟩

/-- **The slice supply at one `x`.**  If the all-interval sum is at least `h/(18000 ℓ L²)` and the
diagonal costs at most `h/(36000 ℓ L²)`, and `ρ⁻ ≤ 1_prime` on the windows, then the slice has at
least `h/(72000 ℓ L²)` distinct `E₃` numbers in `(x, x+h]`. -/
theorem card_sliceTokens_ge_of {B₁ B₂ : Finset ℕ} {z Q D E : ℕ} {x h R ℓ L : ℝ} (hx : 0 ≤ x)
    (hh : 0 ≤ h) (hB₁ : ∀ p ∈ B₁, p.Prime ∧ (p : ℝ) < R) (hB₂ : ∀ p ∈ B₂, p.Prime ∧ R < p)
    (hWR : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂,
      ∀ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊,
        R < n ∧ (rhoMinus z Q D E n : ℝ) ≤ if n.Prime then 1 else 0)
    (hS : h / (18000 * ℓ * L ^ 2) ≤ mtAllIntervalSumOn B₁ B₂ z Q D E x h)
    (hdel : mtAllIntervalSumOn (B₁.filter (fun p => Nat.Coprime p 1)) B₂ z Q D E x h -
      mtCoprimeE3Sum (B₁.filter (fun p => Nat.Coprime p 1)) B₂ 1 z Q D E x h ≤
        h / (36000 * ℓ * L ^ 2)) :
    h / (72000 * ℓ * L ^ 2) ≤ ((sliceTokens B₁ B₂ x h).card : ℝ) := by
  classical
  have hf : B₁.filter (fun p => Nat.Coprime p 1) = B₁ :=
    Finset.filter_true_of_mem fun p _ => Nat.coprime_one_right p
  rw [hf] at hdel
  have hB₁p : ∀ p ∈ B₁, 0 < p := fun p hp => (hB₁ p hp).1.pos
  have hB₂p : ∀ p ∈ B₂, 0 < p := fun p hp => (hB₂ p hp).1.pos
  have hsum := mtCoprimeE3Sum_one_le_card (z := z) (Q := Q) (D := D) (E := E) hx hh hB₁p hB₂p
    fun p₁ hp₁ p₂ hp₂ n hn => (hWR p₁ hp₁ p₂ hp₂ n hn).2
  have hn : ∀ t ∈ sliceTriples B₁ B₂ x h, R < t.2.2 := by
    intro t ht
    obtain ⟨hmem, -, -, h1, h2⟩ := Finset.mem_filter.1 ht
    obtain ⟨ht1, hmem2⟩ := Finset.mem_product.1 hmem
    obtain ⟨ht2, -⟩ := Finset.mem_product.1 hmem2
    have hq : (0 : ℝ) < (t.1 : ℝ) * t.2.1 := by
      have := hB₁p _ ht1; have := hB₂p _ ht2; positivity
    have hW : t.2.2 ∈ Finset.Ioc ⌊x / ((t.1 : ℝ) * t.2.1)⌋₊ ⌊(x + h) / ((t.1 : ℝ) * t.2.1)⌋₊ := by
      rw [mem_Ioc_natFloor_div_iff hx (by linarith) hq]
      push_cast at h1 h2
      exact ⟨h1, h2⟩
    exact (hWR _ ht1 _ ht2 _ hW).1
  have hcard := card_sliceTriples_le (fun p hp => hB₁ p hp) (fun p hp => hB₂ p hp) hn
  have hcard' : ((sliceTriples B₁ B₂ x h).card : ℝ) ≤ 2 * ((sliceTokens B₁ B₂ x h).card : ℝ) := by
    exact_mod_cast hcard
  have e : h / (18000 * ℓ * L ^ 2) - h / (36000 * ℓ * L ^ 2) = 2 * (h / (72000 * ℓ * L ^ 2)) := by
    ring
  linarith

/-- **The slice supply.**  Assume `(E1)` and `(E2)`.  For all large `x` and every
`P ∈ [(log x)^{1.0999}, (log x)^{1.1}]`, the natural window `(x, x + √(xP) log x]` contains at
least `√(xP) log x/(72000 log P (log x)²)` distinct `E₃` numbers `p₁p₂n`, `p₁ ∈ (P, 2P]`,
`p₂ ∈ (R, 2R]`, `n ≠ p₂` prime, `R = √(x/P)/2`. -/
theorem eventually_card_sliceTokens_ge (hDI : MTDeshouillersIwaniecBound) (hW : MTWattBound) :
    ∀ᶠ x : ℝ in atTop, ∀ P : ℝ, Real.log x ^ (10999 / 10000 : ℝ) ≤ P →
      P ≤ Real.log x ^ (11 / 10 : ℝ) →
      Real.sqrt (x * P) * Real.log x / (72000 * Real.log P * Real.log x ^ 2) ≤
        ((sliceTokens ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime)
          ((Finset.Ioc ⌊Real.sqrt (x / P) / 2⌋₊ ⌊2 * (Real.sqrt (x / P) / 2)⌋₊).filter Nat.Prime) x
          (Real.sqrt (x * P) * Real.log x)).card : ℝ) := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 eventually_mtProposition22ZNat_facts
  have hpl : ∀ {C κ : ℝ} (m : ℕ), 0 ≤ C → 0 < κ →
      ∀ᶠ x : ℝ in atTop, C * Real.log x ^ m ≤ x ^ κ := by
    intro C κ m hC hκ
    filter_upwards [eventually_polylog_le_rpow m hC hκ, eventually_ge_atTop (1 : ℝ)] with x h hx
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    have hle : Real.log x ≤ 1 + Real.log (24 * x) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hle m) hC) h
  filter_upwards [eventually_mtAllIntervalSum_short_ge hDI hW (a₀ := 10999 / 10000) le_rfl,
    Real.tendsto_log_atTop.eventually_ge_atTop 16,
    hpl (C := 64) 2 (by norm_num) (by norm_num : (0 : ℝ) < 1),
    hpl (C := 1) 2 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4),
    hpl (C := 2) 1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 6),
    hpl (C := 3) 1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 12),
    hpl (C := 216000 * (471 * 1 + 1)) 5 (by positivity) (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (max X₁ 1 ^ 2)] with x hMT hL16 h64 hL2x hL6 hL12 hpoly hxX
  intro P hPlo hPhi
  have hx1 : 1 ≤ x := le_trans (one_le_pow₀ (le_max_right _ _)) hxX
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hL1 : 1 < L := by linarith
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hPlo
  set a := Real.logb L P with hadef
  have hPa : L ^ a = P := Real.rpow_logb hL0 hL1.ne' hP0
  have ha₀ : 10999 / 10000 ≤ a := by
    rw [← hPa] at hPlo
    exact (Real.rpow_le_rpow_left_iff hL1).1 hPlo
  have ha11 : a ≤ 11 / 10 := by
    rw [← hPa] at hPhi
    exact (Real.rpow_le_rpow_left_iff hL1).1 hPhi
  have ha1 : 1 ≤ a := by linarith
  have hS := hMT a ⟨ha₀, ha11⟩
  rw [hPa, mtAllIntervalSum_eq_on] at hS
  have hsxX : max X₁ 1 ≤ Real.sqrt x := (Real.le_sqrt (by positivity) hx0.le).2 hxX
  obtain ⟨-, -, -, hsX, -, -, -, -, -⟩ :=
    mt_all_interval_scale_X hx0 rfl hL16 ha1 ha11 hPa.symm rfl (by simpa using h64)
  obtain ⟨hz2, hz6⟩ := hX₁ _ (by linarith [le_max_left X₁ 1])
  have hdel := mt_forbidden_delete_small (a := a) (B := 1) (A := 1) (ε := 1 / 10 ^ 7) hx0 rfl hL16
    ha1 ha11 hPa.symm (by positivity) one_pos (by simpa using h64) (by simpa using hL2x)
    (by simpa using hL6) (by simpa using hL12) (by simpa using hpoly) hz2 hz6 le_rfl
    (by rw [Real.rpow_one, Nat.cast_one]; exact hx1)
  obtain ⟨-, -, -, -, hQR, -, hP2, hPL2, -⟩ :=
    mt_forbidden_scales hx0 rfl hL16 ha1 ha11 hPa.symm (by simpa using h64) (by simpa using hL2x)
      (by simpa using hL6) (by simpa using hL12)
  -- `2P < R`
  have h2P : 2 * P < Real.sqrt (x / P) / 2 := by
    have h1 : x ^ (1 / 4 : ℝ) ≤ Real.sqrt (Real.sqrt (x * P)) := by
      have e : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow (Real.sqrt x), Real.sqrt_eq_rpow x, ← Real.rpow_mul hx0.le]; norm_num
      rw [← e]; exact Real.sqrt_le_sqrt hsX
    have h2 : L ^ 2 ≤ x ^ (1 / 4 : ℝ) := by simpa using hL2x
    linarith
  have hR0 : 0 ≤ Real.sqrt (x / P) / 2 := by positivity
  have hrho := mt_window_rho_facts (ε := 1 / 10 ^ 7) hx0 rfl hL16 ha1 ha11 hPa.symm (by positivity)
    (by simpa using h64) (by simpa using hL2x) (by simpa using hL6) (by simpa using hL12) hz2 hz6
    (B₁ := (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime)
    (B₂ := (Finset.Ioc ⌊Real.sqrt (x / P) / 2⌋₊ ⌊2 * (Real.sqrt (x / P) / 2)⌋₊).filter Nat.Prime)
    (fun p hp => ((mem_primes_Ioc_floor_iff hP0.le).1 hp).2)
    (fun p hp => ((mem_primes_Ioc_floor_iff hR0).1 hp).2)
  clear hMT hX₁ hpl
  have hsX0 : 0 ≤ Real.sqrt (x * P) := Real.sqrt_nonneg _
  exact card_sliceTokens_ge_of hx0.le (by positivity)
    (fun p hp => ⟨((mem_primes_Ioc_floor_iff hP0.le).1 hp).1,
      (((mem_primes_Ioc_floor_iff hP0.le).1 hp).2.2).trans_lt h2P⟩)
    (fun p hp => ⟨((mem_primes_Ioc_floor_iff hR0).1 hp).1, ((mem_primes_Ioc_floor_iff hR0).1 hp).2.1⟩)
    (fun p₁ hp₁ p₂ hp₂ n hn => ⟨(hrho p₁ hp₁ p₂ hp₂ n hn).1, (hrho p₁ hp₁ p₂ hp₂ n hn).2.2⟩) hS hdel

end

end RHTower.Sieve
