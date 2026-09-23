import GaloisForLFunctions.RHTower.Sieve.CoprimeMoebiusSeries
import GaloisForLFunctions.RHTower.Sieve.SquarefreeWindowCount

/-!
# Squarefree integers coprime to one prime, in a window

Sieving the squarefree indicator against the condition `p ∤ n` replaces each inner count
`#{n ∈ (t,t+L] : d² ∣ n}` by `#{d² ∣ n} - #{p d² ∣ n}`, which is within `2` of
`L(1 - 1/p)/d²`.  Hence

    | #{n ∈ (t, t+L] : n squarefree, p ∤ n} - L·(1 - 1/p)·S_p | ≤ 2R + L/R,

for `1 ≤ R` and `t + L ≤ R²`, with `S_p = ∑_{p ∤ d} μ(d)/d²`.  Since `S_p = D/(1 - p^{-2})`, the
density is `D·p/(p+1)` — the card's equation `(8)`.
-/

namespace RHTower.Sieve

open Finset Nat
open scoped ArithmeticFunction.Moebius

/-- Below the square root of the range the two truncations of the divisor sum agree. -/
theorem filter_sq_dvd_Icc_eq {n R : ℕ} (hn : 0 < n) (hnR : n ≤ R ^ (2 : ℕ)) :
    (Finset.Icc 1 n).filter (fun d => d ^ (2 : ℕ) ∣ n)
      = (Finset.Icc 1 R).filter (fun d => d ^ (2 : ℕ) ∣ n) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd1, -⟩, hdvd⟩
    refine ⟨⟨hd1, ?_⟩, hdvd⟩
    have hle : d ^ (2 : ℕ) ≤ n := Nat.le_of_dvd hn hdvd
    by_contra hc
    have hRd : R < d := by omega
    have : R ^ (2 : ℕ) < d ^ (2 : ℕ) := Nat.pow_lt_pow_left hRd (by norm_num)
    omega
  · rintro ⟨⟨hd1, -⟩, hdvd⟩
    exact ⟨⟨hd1, le_of_sq_dvd hd1 hn hdvd⟩, hdvd⟩

/-- **The truncated squarefree indicator is exact below the square root.** -/
theorem moebius_sq_eq_sum_trunc {n R : ℕ} (hn : 0 < n) (hnR : n ≤ R ^ (2 : ℕ)) :
    ((μ n : ℤ) : ℝ) ^ (2 : ℕ)
      = ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ^ (2 : ℕ) ∣ n), ((μ d : ℤ) : ℝ) := by
  rw [moebius_sq_eq_sum_sq_dvd hn, filter_sq_dvd_Icc_eq hn hnR]

/-- A prime and a square coprime to it divide together exactly when their product does. -/
theorem sq_dvd_and_prime_dvd_iff {p d n : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) :
    (d ^ (2 : ℕ) ∣ n ∧ p ∣ n) ↔ (p * d ^ (2 : ℕ)) ∣ n := by
  constructor
  · rintro ⟨hd, hpn⟩
    have hcop : Nat.Coprime p (d ^ (2 : ℕ)) :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpn hd
  · intro h
    exact ⟨dvd_trans ⟨p, by ring⟩ h, dvd_trans ⟨d ^ (2 : ℕ), rfl⟩ h⟩

/-- The coprime count splits as a difference of two multiple counts. -/
theorem card_filter_coprime_eq {p d t L : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) :
    (((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℤ)
      = (((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℤ)
        - (((Finset.Ioc t (t + L)).filter (fun n => (p * d ^ (2 : ℕ)) ∣ n)).card : ℤ) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)) (p := fun n => p ∣ n)
  have hAnd : ((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).filter (fun n => p ∣ n)
      = (Finset.Ioc t (t + L)).filter (fun n => (p * d ^ (2 : ℕ)) ∣ n) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro n _
    exact sq_dvd_and_prime_dvd_iff hp hpd
  have hNot : ((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).filter (fun n => ¬ p ∣ n)
      = (Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n) := by
    rw [Finset.filter_filter]
  rw [hAnd, hNot] at hsplit
  omega

/-- The inner count against its expected value. -/
theorem abs_count_coprime_sub_le {p d t L : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) (hd : 1 ≤ d) :
    |(((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℝ)
        - (L : ℝ) * (1 - 1 / (p : ℝ)) / (d : ℝ) ^ (2 : ℕ)| ≤ 2 := by
  classical
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdsq : 0 < d ^ (2 : ℕ) := by positivity
  have hpdsq : 0 < p * d ^ (2 : ℕ) := Nat.mul_pos hp.pos hdsq
  have h1 := abs_card_filter_dvd_Ioc_sub_lt (d ^ (2 : ℕ)) t (t + L) hdsq (by omega)
  have h2 := abs_card_filter_dvd_Ioc_sub_lt (p * d ^ (2 : ℕ)) t (t + L) hpdsq (by omega)
  have hcast : (((t + L : ℕ)) : ℝ) - (t : ℝ) = (L : ℝ) := by push_cast; ring
  have hcast2 : (((d ^ (2 : ℕ) : ℕ)) : ℝ) = (d : ℝ) ^ (2 : ℕ) := by push_cast; ring
  have hcast3 : (((p * d ^ (2 : ℕ) : ℕ)) : ℝ) = (p : ℝ) * (d : ℝ) ^ (2 : ℕ) := by push_cast; ring
  rw [hcast, hcast2] at h1
  rw [hcast, hcast3] at h2
  have hsplit := card_filter_coprime_eq (p := p) (d := d) (t := t) (L := L) hp hpd
  have hreal : (((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℝ)
      = (((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℝ)
        - (((Finset.Ioc t (t + L)).filter (fun n => (p * d ^ (2 : ℕ)) ∣ n)).card : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsplit
  have hexp : (L : ℝ) * (1 - 1 / (p : ℝ)) / (d : ℝ) ^ (2 : ℕ)
      = (L : ℝ) / (d : ℝ) ^ (2 : ℕ) - (L : ℝ) / ((p : ℝ) * (d : ℝ) ^ (2 : ℕ)) := by
    field_simp
  rw [hreal, hexp]
  have h1' := abs_lt.1 h1
  have h2' := abs_lt.1 h2
  rw [abs_le]
  constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-- Multiples of `p` carry no coprime count. -/
theorem filter_coprime_eq_empty_of_dvd {p d t L : ℕ} (hpd : p ∣ d) :
    (Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n) = ∅ := by
  refine Finset.filter_eq_empty_iff.2 ?_
  rintro n - ⟨hdvd, hnp⟩
  exact hnp (dvd_trans (dvd_trans hpd ⟨d, by ring⟩) hdvd)

/-- **The truncated coprime squarefree count of a window.**  Separating the truncation defect
removes the constraint between `R` and the range, which is what an averaged argument needs. -/
theorem abs_trunc_coprime_squarefree_sub_le {p t L R : ℕ} (hp : p.Prime) (hR : 1 ≤ R) :
    |∑ n ∈ Finset.Ioc t (t + L),
        (∑ d ∈ Finset.Icc 1 R, (if d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n then ((μ d : ℤ) : ℝ) else 0))
        - (L : ℝ) * ((1 - 1 / (p : ℝ)) * coprimeSquarefreeSum p)|
      ≤ 2 * (R : ℝ) + (L : ℝ) / (R : ℝ) := by
  classical
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hfac0 : (0 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_one hp0]
    linarith
  have hfac1 : 1 - 1 / (p : ℝ) ≤ 1 := by
    have : (0 : ℝ) < 1 / (p : ℝ) := by positivity
    linarith
  rw [Finset.sum_comm]
  have hinner : ∀ d ∈ Finset.Icc 1 R,
      (∑ n ∈ Finset.Ioc t (t + L), (if d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n then ((μ d : ℤ) : ℝ) else 0))
        = ((μ d : ℤ) : ℝ)
          * ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℕ) : ℝ) := by
    intro d _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl hinner]
  -- compare with the truncated series
  set A : ℝ := ∑ d ∈ Finset.Icc 1 R, ((μ d : ℤ) : ℝ)
    * ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℕ) : ℝ) with hA
  set B : ℝ := (L : ℝ) * (1 - 1 / (p : ℝ))
    * ∑ d ∈ Finset.Icc 1 R, coprimeMoebiusTerm p d with hB
  have hAB : |A - B| ≤ 2 * (R : ℝ) := by
    have hdiff : A - B = ∑ d ∈ Finset.Icc 1 R, (((μ d : ℤ) : ℝ)
        * ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℕ) : ℝ)
        - (L : ℝ) * (1 - 1 / (p : ℝ)) * coprimeMoebiusTerm p d) := by
      rw [hA, hB, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [hdiff]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ Finset.Icc 1 R,
        |((μ d : ℤ) : ℝ)
          * ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℕ) : ℝ)
          - (L : ℝ) * (1 - 1 / (p : ℝ)) * coprimeMoebiusTerm p d| ≤ 2 := by
      intro d hd
      obtain ⟨hd1, -⟩ := Finset.mem_Icc.1 hd
      have hmu : |((μ d : ℤ) : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := d)
        have hc : ((|μ d| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
        rwa [Int.cast_abs] at hc
      by_cases hpd : p ∣ d
      · rw [filter_coprime_eq_empty_of_dvd hpd, coprimeMoebiusTerm, if_pos hpd]
        simp
      · rw [coprimeMoebiusTerm, if_neg hpd]
        have hcount := abs_count_coprime_sub_le (p := p) (d := d) (t := t) (L := L) hp hpd hd1
        have hrw : ((μ d : ℤ) : ℝ)
            * ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℕ) : ℝ)
            - (L : ℝ) * (1 - 1 / (p : ℝ)) * (((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ))
            = ((μ d : ℤ) : ℝ)
              * (((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℕ) : ℝ)
                - (L : ℝ) * (1 - 1 / (p : ℝ)) / (d : ℝ) ^ (2 : ℕ)) := by ring
        rw [hrw, abs_mul]
        calc |((μ d : ℤ) : ℝ)|
              * |((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n)).card : ℕ) : ℝ)
                - (L : ℝ) * (1 - 1 / (p : ℝ)) / (d : ℝ) ^ (2 : ℕ)|
            ≤ 1 * 2 := mul_le_mul hmu hcount (abs_nonneg _) (by norm_num)
          _ = 2 := by norm_num
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have hcard : ((R + 1 - 1 : ℕ) : ℝ) = (R : ℝ) := by
      congr 1
    rw [hcard]
    linarith
  have hBC : |B - (L : ℝ) * ((1 - 1 / (p : ℝ)) * coprimeSquarefreeSum p)|
      ≤ (L : ℝ) / (R : ℝ) := by
    have hdens := abs_sum_Icc_coprimeMoebius_sub_le (p := p) hR
    have hrw : B - (L : ℝ) * ((1 - 1 / (p : ℝ)) * coprimeSquarefreeSum p)
        = (L : ℝ) * (1 - 1 / (p : ℝ))
          * ((∑ d ∈ Finset.Icc 1 R, coprimeMoebiusTerm p d) - coprimeSquarefreeSum p) := by
      rw [hB]; ring
    rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) * (1 - 1 / (p : ℝ)))]
    calc (L : ℝ) * (1 - 1 / (p : ℝ))
          * |(∑ d ∈ Finset.Icc 1 R, coprimeMoebiusTerm p d) - coprimeSquarefreeSum p|
        ≤ (L : ℝ) * (1 - 1 / (p : ℝ)) * (1 / (R : ℝ)) := by
          refine mul_le_mul_of_nonneg_left hdens (by positivity)
      _ ≤ (L : ℝ) * 1 * (1 / (R : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hfac1 (by positivity)
      _ = (L : ℝ) / (R : ℝ) := by ring
  calc |A - (L : ℝ) * ((1 - 1 / (p : ℝ)) * coprimeSquarefreeSum p)|
      ≤ |A - B| + |B - (L : ℝ) * ((1 - 1 / (p : ℝ)) * coprimeSquarefreeSum p)| :=
        abs_sub_le _ _ _
    _ ≤ 2 * (R : ℝ) + (L : ℝ) / (R : ℝ) := by linarith


/-- **The coprime squarefree count of a window.** -/
theorem abs_window_coprime_squarefree_sub_le {p t L R : ℕ} (hp : p.Prime) (hR : 1 ≤ R)
    (hRM : t + L ≤ R ^ (2 : ℕ)) :
    |∑ n ∈ Finset.Ioc t (t + L), (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
        - (L : ℝ) * ((1 - 1 / (p : ℝ)) * coprimeSquarefreeSum p)|
      ≤ 2 * (R : ℝ) + (L : ℝ) / (R : ℝ) := by
  classical
  -- the pointwise identity
  have hpt : ∀ n ∈ Finset.Ioc t (t + L),
      (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
        = ∑ d ∈ Finset.Icc 1 R, (if d ^ (2 : ℕ) ∣ n ∧ ¬ p ∣ n then ((μ d : ℤ) : ℝ) else 0) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le t) hn.1
    have hnR : n ≤ R ^ (2 : ℕ) := le_trans hn.2 hRM
    by_cases hpn : p ∣ n
    · rw [if_pos hpn]
      refine (Finset.sum_eq_zero ?_).symm
      intro d _
      rw [if_neg (by tauto)]
    · rw [if_neg hpn, moebius_sq_eq_sum_trunc hn0 hnR, Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro d _
      by_cases hdn : d ^ (2 : ℕ) ∣ n
      · rw [if_pos hdn, if_pos ⟨hdn, hpn⟩]
      · rw [if_neg hdn, if_neg (by tauto)]
  rw [Finset.sum_congr rfl hpt]
  exact abs_trunc_coprime_squarefree_sub_le hp hR

end RHTower.Sieve
