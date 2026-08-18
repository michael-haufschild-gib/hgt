import GaloisForLFunctions.RHTower.Sieve.PrimePairAverage
import GaloisForLFunctions.RHTower.Sieve.GallagherAlmostDiagonal
import GaloisForLFunctions.RHTower.Sieve.SmallestPart

/-!
# The Gallagher neighbour count of a dyadic prime block

The almost-diagonal mean value theorem of `Sieve/GallagherAlmostDiagonal` weighs each frequency by
the number of its multiplicative neighbours.  On a dyadic block of primes that count is a shifted
prime-pair count, so the two-dimensional sieve applies:

```text
∑_{p ≍ R} #{p' ≍ R : |log p − log p'| < δ}
    ≤ π(2R) − π(R) + 2 ∑_{1 ≤ d ≤ K} #{p ≤ 2R : p, p + d prime} ,      K ≥ 6Rδ .
```

The first step is pure bookkeeping; the second is the observation that a multiplicative window of
ratio `e^δ` around a point of size `≤ 2R` has additive length at most `6Rδ`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The near-diagonal pair count, split by the shift.** -/
theorem sum_card_neighbour_le (s : Finset ℕ) (K : ℕ) (P : ℕ → ℕ → Prop)
    [DecidableRel P]
    (hP : ∀ n ∈ s, ∀ m ∈ s, P n m → n ≤ m + K ∧ m ≤ n + K) :
    ∑ n ∈ s, (#(s.filter (fun m => P n m)) : ℝ)
      ≤ (s.card : ℝ)
        + 2 * ∑ d ∈ Finset.Icc 1 K, (#(s.filter (fun n => n + d ∈ s)) : ℝ) := by
  classical
  have hcount : ((s ×ˢ s).filter (fun q => P q.1 q.2)).card
      = ∑ n ∈ s, (s.filter (fun m => P n m)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun n _ => (Finset.card_filter _ _).symm
  set Up : Finset (ℕ × ℕ) := (Finset.Icc 1 K).biUnion
    (fun d => (s.filter (fun n => n + d ∈ s)).image (fun n => (n, n + d))) with hUpdef
  set Down : Finset (ℕ × ℕ) := (Finset.Icc 1 K).biUnion
    (fun d => (s.filter (fun n => n + d ∈ s)).image (fun n => (n + d, n))) with hDowndef
  set Diag : Finset (ℕ × ℕ) := s.image (fun n => (n, n)) with hDiagdef
  have hsub : (s ×ˢ s).filter (fun q => P q.1 q.2) ⊆ Diag ∪ (Up ∪ Down) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2⟩, hPq⟩ := hq
    obtain ⟨hle1, hle2⟩ := hP q.1 h1 q.2 h2 hPq
    rcases lt_trichotomy q.1 q.2 with hlt | heq | hgt
    · refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
      refine Finset.mem_biUnion.2 ⟨q.2 - q.1, ?_, ?_⟩
      · rw [Finset.mem_Icc]; omega
      · refine Finset.mem_image.2 ⟨q.1, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨h1, ?_⟩
          have hq2 : q.1 + (q.2 - q.1) = q.2 := by omega
          rw [hq2]; exact h2
        · exact Prod.ext rfl (by omega)
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨q.1, h1, Prod.ext rfl heq⟩)
    · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
      refine Finset.mem_biUnion.2 ⟨q.1 - q.2, ?_, ?_⟩
      · rw [Finset.mem_Icc]; omega
      · refine Finset.mem_image.2 ⟨q.2, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨h2, ?_⟩
          have hq1 : q.2 + (q.1 - q.2) = q.1 := by omega
          rw [hq1]; exact h1
        · exact Prod.ext (by omega) rfl
  have hDiagle : Diag.card ≤ s.card := Finset.card_image_le
  have hUple : Up.card ≤ ∑ d ∈ Finset.Icc 1 K, (s.filter (fun n => n + d ∈ s)).card :=
    le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun d _ => Finset.card_image_le)
  have hDownle : Down.card ≤ ∑ d ∈ Finset.Icc 1 K, (s.filter (fun n => n + d ∈ s)).card :=
    le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun d _ => Finset.card_image_le)
  have hchain : ((s ×ˢ s).filter (fun q => P q.1 q.2)).card
      ≤ s.card + 2 * ∑ d ∈ Finset.Icc 1 K, (s.filter (fun n => n + d ∈ s)).card := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    have := Finset.card_union_le Up Down
    omega
  rw [hcount] at hchain
  have hcast : ((∑ n ∈ s, (s.filter (fun m => P n m)).card : ℕ) : ℝ)
      ≤ ((s.card + 2 * ∑ d ∈ Finset.Icc 1 K, (s.filter (fun n => n + d ∈ s)).card : ℕ) : ℝ) := by
    exact_mod_cast hchain
  push_cast at hcast
  exact hcast

/-- `e^δ − 1 ≤ 3δ` on the unit interval. -/
theorem exp_sub_one_le_three_mul {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Real.exp δ - 1 ≤ 3 * δ := by
  have hexp : (0 : ℝ) < Real.exp δ := Real.exp_pos δ
  have h1 : 1 - δ ≤ Real.exp (-δ) := by
    have := Real.add_one_le_exp (-δ)
    linarith
  have h2 : Real.exp δ * (1 - δ) ≤ Real.exp δ * Real.exp (-δ) :=
    mul_le_mul_of_nonneg_left h1 hexp.le
  have h3 : Real.exp δ * Real.exp (-δ) = 1 := by
    rw [← Real.exp_add]
    simp
  have h4 : Real.exp δ ≤ 3 := by
    have h5 := Real.exp_le_exp.2 hδ1
    have h6 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  nlinarith [h2, h3, h4, hδ0]

/-- A small logarithmic gap forces a small ratio. -/
theorem lt_mul_exp_of_log_sub_lt {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.log a - Real.log b < δ) : a < b * Real.exp δ := by
  have hlt : Real.log a < Real.log b + δ := by linarith
  have := Real.exp_lt_exp.2 hlt
  rwa [Real.exp_log ha, Real.exp_add, Real.exp_log hb] at this

/-- **A multiplicative window on a dyadic block is an additive window.** -/
theorem le_add_of_log_close {R K : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 6 * (R : ℝ) * δ ≤ (K : ℝ)) {n m : ℕ}
    (hn : n ∈ bigPrimeSet R (2 * R)) (hm : m ∈ bigPrimeSet R (2 * R))
    (hlog : |Real.log (n : ℝ) - Real.log (m : ℝ)| < δ) :
    n ≤ m + K ∧ m ≤ n + K := by
  rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hn hm
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hnR : (n : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast (by omega : n ≤ 2 * R)
  have hmR : (m : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast (by omega : m ≤ 2 * R)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hexp := exp_sub_one_le_three_mul hδ0.le hδ1
  rw [abs_lt] at hlog
  constructor
  · have h1 : (n : ℝ) < (m : ℝ) * Real.exp δ :=
      lt_mul_exp_of_log_sub_lt hn0 hm0 hlog.2
    have h2 : (n : ℝ) < (m : ℝ) + (K : ℝ) := by nlinarith [h1, hexp, hmR, hδ0.le]
    have : n < m + K := by exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((m + K : ℕ) : ℝ))
    omega
  · have h1 : (m : ℝ) < (n : ℝ) * Real.exp δ :=
      lt_mul_exp_of_log_sub_lt hm0 hn0 (by linarith [hlog.1])
    have h2 : (m : ℝ) < (n : ℝ) + (K : ℝ) := by nlinarith [h1, hexp, hnR, hδ0.le]
    have : m < n + K := by exact_mod_cast (by push_cast; linarith : (m : ℝ) < ((n + K : ℕ) : ℝ))
    omega

/-- **The neighbour count of a dyadic prime block, in shifted prime pairs.** -/
theorem sum_logNeighbourCount_bigPrimeSet_le {R h K : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 6 * (R : ℝ) * δ ≤ (K : ℝ)) (hhR : h ≤ R) :
    ∑ n ∈ bigPrimeSet R (2 * R),
        (logNeighbourCount (bigPrimeSet R (2 * R)) δ n : ℝ)
      ≤ ((bigPrimeSet R (2 * R)).card : ℝ)
        + 2 * ∑ d ∈ Finset.Icc 1 K,
            ((((Finset.Icc 1 (2 * R)).filter
                (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ) := by
  classical
  set s : Finset ℕ := bigPrimeSet R (2 * R) with hs
  have hstep := sum_card_neighbour_le s K
    (fun n m => |Real.log (n : ℝ) - Real.log (m : ℝ)| < δ)
    (fun n hn m hm hnm => le_add_of_log_close hδ0 hδ1 hK hn hm hnm)
  have hsum : ∑ d ∈ Finset.Icc 1 K, (#(s.filter (fun n => n + d ∈ s)) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 K,
          ((((Finset.Icc 1 (2 * R)).filter
              (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ) := by
    refine Finset.sum_le_sum fun d _ => ?_
    have hsubset : s.filter (fun n => n + d ∈ s)
        ⊆ (Finset.Icc 1 (2 * R)).filter (fun m => m.Prime ∧ (m + d).Prime ∧ h < m) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      have hn1 := hn.1
      have hn2 := hn.2
      rw [hs, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hn1
      rw [hs, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hn2
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hn1.2, hn2.2, by omega⟩
    exact_mod_cast Nat.cast_le.2 (Finset.card_le_card hsubset)
  have heq : ∑ n ∈ s, (logNeighbourCount s δ n : ℝ)
      = ∑ n ∈ s, (#(s.filter (fun m : ℕ => |Real.log (n : ℝ) - Real.log (m : ℝ)| < δ)) : ℝ) :=
    Finset.sum_congr rfl fun n _ => rfl
  rw [heq]
  linarith [hstep, hsum]

end

end RHTower.Sieve
