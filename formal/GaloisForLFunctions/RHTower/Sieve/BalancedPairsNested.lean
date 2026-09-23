import GaloisForLFunctions.RHTower.Sieve.PrimeRangeSplit

/-!
# The balanced pairs as a nested sum

The balanced pair set is a filter of a product, so any sum over it is a sum over the first entry of
a sum over the second.  That is the decomposition the card's `(10)` needs: for fixed `n₁` the second
entry ranges over `[x/n₁, (x+h√x)/n₁]`, whose length is `h√x/n₁ ≤ h` because `n₁ ≥ √x` — a bound
invisible in the two-dimensional description.

The counting lemma for a closed interval is recorded here as well: `Icc a b = Ioc (a-1) b` for
`a ≥ 1`, so the corpus's `Ioc` estimate applies with length `b - a + 1`.
-/

namespace RHTower.Sieve

open Finset

/-- A closed interval is a half-open one. -/
theorem Icc_eq_Ioc_pred {a b : ℕ} (ha : 1 ≤ a) : Finset.Icc a b = Finset.Ioc (a - 1) b := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- **Multiples in a closed interval.** -/
theorem card_filter_dvd_Icc_le {p a b : ℕ} (hp : 0 < p) (ha : 1 ≤ a) (hab : a ≤ b) :
    (((Finset.Icc a b).filter (fun n => p ∣ n)).card : ℝ) ≤ ((b : ℝ) - (a : ℝ) + 1) / p + 1 := by
  classical
  rw [Icc_eq_Ioc_pred ha]
  have hle : a - 1 ≤ b := by omega
  have h := abs_card_filter_dvd_Ioc_sub_lt p (a - 1) b hp hle
  have hcast : ((b : ℕ) : ℝ) - (((a - 1 : ℕ)) : ℝ) = (b : ℝ) - (a : ℝ) + 1 := by
    have : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ a := ha
      push_cast [Nat.cast_sub h1]
      ring
    rw [this]
    ring
  rw [hcast] at h
  have := (abs_lt.1 h).2
  linarith

/-- **The balanced pairs, as a nested sum.**  A sum over the pair set, further filtered by any
predicate, is a sum over the first entry of a sum over the second. -/
theorem sum_balancedPairs_filter_nested {x h : ℝ} (w : ℕ × ℕ → ℝ)
    (R : ℕ × ℕ → Prop) [DecidablePred R] :
    ∑ q ∈ (balancedPairs x h).filter R, w q
      = ∑ a ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
          ∑ b ∈ (Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊).filter
              (fun b => (x ≤ ((a * b : ℕ) : ℝ) ∧ ((a * b : ℕ) : ℝ) ≤ x + h * Real.sqrt x
                ∧ Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ R (a, b)),
            w (a, b) := by
  classical
  rw [balancedPairs, Finset.filter_filter, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Finset.sum_filter]

/-- The inner interval count, for a fixed first entry. -/
theorem inner_count_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {p : ℕ} (hp : 0 < p) {a : ℕ}
    (ha1 : Real.sqrt x ≤ (a : ℝ)) (ha2 : (a : ℝ) ≤ 2 * Real.sqrt x) (M : ℕ) :
    (((Finset.Icc 1 M).filter
        (fun b => (x ≤ ((a * b : ℕ) : ℝ) ∧ ((a * b : ℕ) : ℝ) ≤ x + h * Real.sqrt x
            ∧ Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ (p ∣ a ∧ p ∣ b))).card : ℝ)
      ≤ (h + 2) / p + 1 := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs2 : (2 : ℝ) ≤ Real.sqrt x := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    have : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h4, this.le, this.ge]
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hs0 ha1
  set c : ℕ := ⌊x / (a : ℝ)⌋₊ with hc
  set d : ℕ := ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ with hd
  have hxa : (1 : ℝ) ≤ x / (a : ℝ) := by
    rw [le_div_iff₀ ha0]
    nlinarith [ha2, hs2, Real.sq_sqrt hx0.le]
  have hc1 : 1 ≤ c := Nat.le_floor (by exact_mod_cast hxa)
  have hcd : c ≤ d := by
    refine Nat.floor_le_floor ?_
    have hnum : x ≤ x + h * Real.sqrt x := by nlinarith [hh, hs0]
    gcongr
  have hsub : (Finset.Icc 1 M).filter
      (fun b => (x ≤ ((a * b : ℕ) : ℝ) ∧ ((a * b : ℕ) : ℝ) ≤ x + h * Real.sqrt x
          ∧ Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ (p ∣ a ∧ p ∣ b))
      ⊆ (Finset.Icc c d).filter (fun b => p ∣ b) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨-, ⟨hb1, hb2, -, -⟩, -, hpb⟩ := hb
    have hab : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; ring
    rw [hab] at hb1 hb2
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hpb⟩
    · have hxb : x / (a : ℝ) ≤ ((b : ℕ) : ℝ) := by
        rw [div_le_iff₀ ha0]
        linarith [hb1]
      calc c = ⌊x / (a : ℝ)⌋₊ := hc
        _ ≤ ⌊((b : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor hxb
        _ = b := Nat.floor_natCast b
    · refine Nat.le_floor ?_
      rw [le_div_iff₀ ha0]
      linarith [hb2]
  have hcard := Finset.card_le_card hsub
  have hcardR : (((Finset.Icc 1 M).filter
      (fun b => (x ≤ ((a * b : ℕ) : ℝ) ∧ ((a * b : ℕ) : ℝ) ≤ x + h * Real.sqrt x
          ∧ Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x) ∧ (p ∣ a ∧ p ∣ b))).card : ℝ)
      ≤ (((Finset.Icc c d).filter (fun b => p ∣ b)).card : ℝ) := by exact_mod_cast hcard
  refine le_trans hcardR ?_
  refine le_trans (card_filter_dvd_Icc_le hp hc1 hcd) ?_
  have hdle : (d : ℝ) ≤ (x + h * Real.sqrt x) / (a : ℝ) := by
    refine Nat.floor_le ?_
    have : (0 : ℝ) ≤ h * Real.sqrt x := by positivity
    positivity
  have hcge : x / (a : ℝ) - 1 < (c : ℝ) := by
    have := Nat.lt_floor_add_one (x / (a : ℝ))
    linarith
  have hlen : (d : ℝ) - (c : ℝ) + 1 ≤ h + 2 := by
    have hgap : (x + h * Real.sqrt x) / (a : ℝ) - x / (a : ℝ) = h * Real.sqrt x / (a : ℝ) := by
      field_simp
      ring
    have hle : h * Real.sqrt x / (a : ℝ) ≤ h := by
      rw [div_le_iff₀ ha0]
      nlinarith [hh, ha1, hs0]
    linarith [hdle, hcge, hgap.le, hgap.ge, hle]
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hdiv : ((d : ℝ) - (c : ℝ) + 1) / p ≤ (h + 2) / p := by gcongr
  linarith

end RHTower.Sieve
