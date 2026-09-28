import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardPairTuples

/-!
# The discarded quadruple tail as prime counts over prime quadruples

The fourth-level discarded tail `D₄(n)` sums `ρ(n/(q₁q₂q₃q₄), q₄)` over admissible triples
`q₃ < q₂ < q₁ < D`, `q₁ q₂⁴ < E`, and `z ≤ q₄ < q₃`.  Below `q₄²` the cofactor is `1` or a prime
`≥ q₄`, so over a window `(a, b]` the tail is at most prime counts in `(a/d, b/d]`,
`d = q₁q₂q₃q₄`.
-/

namespace RHTower.Sieve

open Finset

theorem rho_le_one_or_prime {m q : ℕ} (hm : m < q ^ 2) :
    rho m q ≤ (if m = 1 then 1 else 0) + (if m.Prime ∧ q ≤ m then 1 else 0) := by
  by_cases hρ : rho m q = 0
  · rw [hρ]; exact Nat.zero_le _
  have hρ1 : rho m q = 1 := by have := rho_le_one m q; omega
  rw [hρ1]
  obtain ⟨hm0, hall⟩ := rho_eq_one_iff.1 hρ1
  have hge : ∀ p, p.Prime → p ∣ m → q ≤ p := fun p hp hpm =>
    hall p (Nat.mem_primeFactors.2 ⟨hp, hpm, by omega⟩)
  by_cases h1 : m = 1
  · simp only [h1, if_true]; omega
  have hp := Nat.minFac_prime h1
  have hpm := Nat.minFac_dvd m
  have hqp := hge _ hp hpm
  by_cases hmp : m.Prime
  · have hqm : q ≤ m := hqp.trans (Nat.minFac_le hm0)
    simp only [h1, if_false, hmp, hqm, and_self, if_true]; omega
  · exfalso
    obtain ⟨k, hk⟩ := hpm
    have hk1 : k ≠ 1 := by rintro rfl; rw [mul_one] at hk; exact hmp (hk ▸ hp)
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    have hkp := Nat.minFac_prime hk1
    have hkm : k.minFac ∣ m := hk ▸ Dvd.dvd.mul_left (Nat.minFac_dvd k) _
    have hqk : q ≤ k := (hge _ hkp hkm).trans (Nat.minFac_le hk0)
    have : q ^ 2 ≤ m := by rw [hk, sq]; exact Nat.mul_le_mul hqp hqk
    omega

/-- The admissible prime quadruples `z ≤ q₄ < q₃ < q₂ < q₁ < D`, `q₁ q₂⁴ < E`. -/
def harmanDiscardQuadSet (z D E : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Finset.Ico z D) ×ˢ (Finset.Ico z D)) ×ˢ ((Finset.Ico z D) ×ˢ (Finset.Ico z D))).filter
    (fun t => t.1.1.Prime ∧ t.1.2.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧
      t.1.2 < t.1.1 ∧ t.2.1 < t.1.2 ∧ t.2.2 < t.2.1 ∧ t.1.1 * t.1.2 ^ (4 : ℕ) < E)

/-- The product `q₁q₂q₃q₄` of a quadruple. -/
def quadProd (t : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := t.1.1 * t.1.2 * t.2.1 * t.2.2

theorem sum_le_sum_superset {α : Type*} {s t : Finset α} (hst : s ⊆ t) {g G : α → ℕ}
    (h : ∀ x ∈ s, g x ≤ G x) : ∑ x ∈ s, g x ≤ ∑ x ∈ t, G x :=
  (Finset.sum_le_sum h).trans (Finset.sum_le_sum_of_subset hst)

theorem harmanDiscardQuadrupleSum_le {z D E n : ℕ} :
    harmanDiscardQuadrupleSum z D E n ≤ ∑ t ∈ harmanDiscardQuadSet z D E,
      (if quadProd t ∣ n then rho (n / quadProd t) t.2.2 else 0) := by
  unfold harmanDiscardQuadrupleSum harmanDiscardQuadSet
  rw [Finset.sum_filter]
  simp only [Finset.sum_product]
  refine sum_le_sum_superset (Finset.filter_subset _ _) (fun q₁ hq₁ => ?_)
  obtain ⟨hq₁I, hq₁p, hq₁n⟩ : q₁ ∈ Finset.Ico z D ∧ q₁.Prime ∧ q₁ ∣ n := by
    simp only [Finset.mem_filter] at hq₁; exact ⟨hq₁.1, hq₁.2⟩
  refine sum_le_sum_superset (fun q₂ hq₂ => ?_) (fun q₂ hq₂ => ?_)
  · simp only [harmanPairs, primeWindow, Finset.mem_filter, Finset.mem_Ico] at hq₂ hq₁I ⊢
    exact ⟨hq₂.1.1.1, by omega⟩
  obtain ⟨hq₂I, hq₂p, hq₂n, hE⟩ : q₂ ∈ Finset.Ico z q₁ ∧ q₂.Prime ∧ q₂ ∣ n / q₁ ∧
      q₁ * q₂ ^ (4 : ℕ) < E := by
    simp only [harmanPairs, primeWindow, Finset.mem_filter] at hq₂
    exact ⟨hq₂.1.1, hq₂.1.2.1, hq₂.1.2.2, hq₂.2⟩
  refine sum_le_sum_superset (fun q₃ hq₃ => ?_) (fun q₃ hq₃ => ?_)
  · simp only [primeWindow, Finset.mem_filter, Finset.mem_Ico] at hq₃ hq₂I hq₁I ⊢
    exact ⟨hq₃.1.1, by omega⟩
  obtain ⟨hq₃I, hq₃p, hq₃n⟩ : q₃ ∈ Finset.Ico z q₂ ∧ q₃.Prime ∧ q₃ ∣ n / q₁ / q₂ := by
    simp only [primeWindow, Finset.mem_filter] at hq₃; exact ⟨hq₃.1, hq₃.2⟩
  refine sum_le_sum_superset (fun q₄ hq₄ => ?_) (fun q₄ hq₄ => ?_)
  · simp only [primeWindow, Finset.mem_filter, Finset.mem_Ico] at hq₄ hq₃I hq₂I hq₁I ⊢
    exact ⟨hq₄.1.1, by omega⟩
  obtain ⟨hq₄I, hq₄p, hq₄n⟩ : q₄ ∈ Finset.Ico z q₃ ∧ q₄.Prime ∧ q₄ ∣ n / q₁ / q₂ / q₃ := by
    simp only [primeWindow, Finset.mem_filter] at hq₄; exact ⟨hq₄.1, hq₄.2⟩
  simp only [Finset.mem_Ico] at hq₁I hq₂I hq₃I hq₄I
  have hstatic : q₁.Prime ∧ q₂.Prime ∧ q₃.Prime ∧ q₄.Prime ∧ q₂ < q₁ ∧ q₃ < q₂ ∧ q₄ < q₃ ∧
      q₁ * q₂ ^ (4 : ℕ) < E := ⟨hq₁p, hq₂p, hq₃p, hq₄p, hq₂I.2, hq₃I.2, hq₄I.2, hE⟩
  have hd12 : q₁ * q₂ ∣ n := (Nat.dvd_div_iff_mul_dvd hq₁n).1 hq₂n
  have hd123 : q₁ * q₂ * q₃ ∣ n := by
    simp only [Nat.div_div_eq_div_mul] at hq₃n
    exact (Nat.dvd_div_iff_mul_dvd hd12).1 hq₃n
  have hd : q₁ * q₂ * q₃ * q₄ ∣ n := by
    simp only [Nat.div_div_eq_div_mul] at hq₄n
    exact (Nat.dvd_div_iff_mul_dvd hd123).1 hq₄n
  simp only [quadProd]
  rw [if_pos hstatic, if_pos hd]
  simp only [Nat.div_div_eq_div_mul, le_refl]

/-- The prime-count bound for one quadruple: the cofactor is `1` or a prime `≥ q₄`. -/
def harmanQuadTupleBound (a b q₄ : ℕ) : ℕ :=
  (if 1 ∈ Finset.Ioc a b then 1 else 0) + primeCountAbove a b q₄

/-- **The discarded quadruple tail over a window.** -/
theorem sum_Ioc_harmanDiscardQuadrupleSum_le {z D E a b : ℕ}
    (hsmall : ∀ t ∈ harmanDiscardQuadSet z D E, b / quadProd t < t.2.2 ^ 2) :
    ∑ n ∈ Finset.Ioc a b, harmanDiscardQuadrupleSum z D E n ≤
      ∑ t ∈ harmanDiscardQuadSet z D E,
        harmanQuadTupleBound (a / quadProd t) (b / quadProd t) t.2.2 := by
  refine (Finset.sum_le_sum (fun n _ => harmanDiscardQuadrupleSum_le)).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun t ht => ?_)
  have hd : 0 < quadProd t := by
    simp only [harmanDiscardQuadSet, Finset.mem_filter] at ht
    unfold quadProd
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ht.2.1.pos ht.2.2.1.pos) ht.2.2.2.1.pos)
      ht.2.2.2.2.1.pos
  rw [sum_Ioc_dvd_eq hd (fun m => rho m t.2.2)]
  calc ∑ m ∈ Finset.Ioc (a / quadProd t) (b / quadProd t), rho m t.2.2
      ≤ ∑ m ∈ Finset.Ioc (a / quadProd t) (b / quadProd t),
          ((if m = 1 then 1 else 0) + (if m.Prime ∧ t.2.2 ≤ m then 1 else 0)) := by
        refine Finset.sum_le_sum (fun m hm => rho_le_one_or_prime ?_)
        exact lt_of_le_of_lt (Finset.mem_Ioc.1 hm).2 (hsmall t ht)
    _ = harmanQuadTupleBound (a / quadProd t) (b / quadProd t) t.2.2 := by
        rw [Finset.sum_add_distrib, sum_Ioc_prime_indicator_eq, Finset.sum_ite_eq']
        rfl

end RHTower.Sieve
