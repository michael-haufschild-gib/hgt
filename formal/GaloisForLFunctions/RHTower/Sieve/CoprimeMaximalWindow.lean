import GaloisForLFunctions.RHTower.Sieve.SquarefreeMaximalWindow
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogSum

/-!
# The maximal deleted-squarefree window deviation

The same argument as for `μ²`, run on the weight `μ²·1_{p∤·}` of the card's third input.  The only
new ingredient is the pointwise truncation defect: at a multiple of `p` both the weight and its
truncation vanish, and away from the multiples of `p` the condition `¬ p ∣ n` is inert, so the
defect is the squarefree one.

Everything downstream — the trivial length bound, the maximum over lengths, the sum over starting
points with the divisor range cut at `√(B+L)`, and the limit — is the same as for `μ²`, and the
limit is taken by the general lemma `maximalWindowDevMeanSquareAt_of_sum_bound`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The deleted density is at most one. -/
theorem coprime_block_density_le_one {p : ℕ} (hp : p.Prime) :
    squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1) ≤ 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hD0 := squarefreeDensity_nonneg'
  have hD1 := squarefreeDensity_le_one
  rw [div_le_one (by linarith)]
  nlinarith

/-- The weight is between zero and one. -/
theorem coprimeSquarefreeWeight_mem (p n : ℕ) :
    0 ≤ coprimeSquarefreeWeight p n ∧ coprimeSquarefreeWeight p n ≤ 1 := by
  rw [coprimeSquarefreeWeight]
  split
  · constructor <;> norm_num
  · refine ⟨sq_nonneg _, ?_⟩
    exact le_trans (le_abs_self _) (abs_moebius_sq_real_le_one n)

/-- **The pointwise truncation defect of the deleted weight.** -/
theorem abs_coprime_sub_trunc_le {p n R M : ℕ} (hn : 0 < n) (hnM : n ≤ M) :
    |coprimeSquarefreeWeight p n
        - ∑ d ∈ Finset.Icc 1 R, (if d ^ 2 ∣ n ∧ ¬ p ∣ n then ((moebius d : ℤ) : ℝ) else 0)|
      ≤ ((((Finset.Icc (R + 1) M).filter (fun d => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
  classical
  by_cases hpn : p ∣ n
  · have hw : coprimeSquarefreeWeight p n = 0 := by
      rw [coprimeSquarefreeWeight, if_pos hpn]
    have hs : ∑ d ∈ Finset.Icc 1 R,
        (if d ^ 2 ∣ n ∧ ¬ p ∣ n then ((moebius d : ℤ) : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro d _
      rw [if_neg (by tauto)]
    rw [hw, hs, sub_zero, abs_zero]
    positivity
  · have hw : coprimeSquarefreeWeight p n = ((moebius n : ℤ) : ℝ) ^ 2 := by
      rw [coprimeSquarefreeWeight, if_neg hpn]
    have hs : ∑ d ∈ Finset.Icc 1 R,
        (if d ^ 2 ∣ n ∧ ¬ p ∣ n then ((moebius d : ℤ) : ℝ) else 0)
        = ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ^ 2 ∣ n), ((moebius d : ℤ) : ℝ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro d _
      by_cases hdn : d ^ 2 ∣ n
      · rw [if_pos ⟨hdn, hpn⟩, if_pos hdn]
      · rw [if_neg (by tauto), if_neg hdn]
    rw [hw, hs]
    exact abs_moebius_sq_sub_trunc_le hn hnM

/-- Double counting the square divisors of a window. -/
theorem sum_card_swap (t L R M : ℕ) :
    ∑ n ∈ Finset.Ioc t (t + L),
        ((((Finset.Icc (R + 1) M).filter (fun d => d ^ 2 ∣ n)).card : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc (R + 1) M,
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
  classical
  have hL : ∀ n : ℕ, ((((Finset.Icc (R + 1) M).filter (fun d => d ^ 2 ∣ n)).card : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc (R + 1) M, (if d ^ 2 ∣ n then (1 : ℝ) else 0) := by
    intro n
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hR : ∀ d : ℕ, ((((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ)
      = ∑ n ∈ Finset.Ioc t (t + L), (if d ^ 2 ∣ n then (1 : ℝ) else 0) := by
    intro d
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl (fun n _ => hL n), Finset.sum_congr rfl (fun d _ => hR d),
    Finset.sum_comm]

/-- **The window truncation defect of the deleted weight.** -/
theorem abs_window_coprime_sub_trunc_le (p t L R M : ℕ) (hM : t + L ≤ M) :
    |∑ n ∈ Finset.Ioc t (t + L), coprimeSquarefreeWeight p n
        - ∑ n ∈ Finset.Ioc t (t + L),
            ∑ d ∈ Finset.Icc 1 R, (if d ^ 2 ∣ n ∧ ¬ p ∣ n then ((moebius d : ℤ) : ℝ) else 0)|
      ≤ ∑ d ∈ Finset.Icc (R + 1) M,
          ((((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ n ∈ Finset.Ioc t (t + L),
      |coprimeSquarefreeWeight p n
        - ∑ d ∈ Finset.Icc 1 R, (if d ^ 2 ∣ n ∧ ¬ p ∣ n then ((moebius d : ℤ) : ℝ) else 0)|
        ≤ ((((Finset.Icc (R + 1) M).filter (fun d => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le t) hn.1
    exact abs_coprime_sub_trunc_le hn0 (le_trans hn.2 hM)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  exact le_of_eq (sum_card_swap t L R M)

/-- **The window bound for the deleted weight, with the truncation defect.** -/
theorem abs_window_coprime_sub_le_defect {p : ℕ} (hp : p.Prime) (t L R M : ℕ) (hR : 1 ≤ R)
    (hM : t + L ≤ M) :
    |∑ n ∈ Finset.Ioc t (t + L), coprimeSquarefreeWeight p n
        - (L : ℝ) * (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))|
      ≤ 2 * (R : ℝ) + (L : ℝ) / (R : ℝ)
        + ∑ d ∈ Finset.Icc (R + 1) M,
            ((((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
  classical
  have h1 := abs_window_coprime_sub_trunc_le p t L R M hM
  have h2 := abs_trunc_coprime_squarefree_sub_le (p := p) (t := t) (L := L) (R := R) hp hR
  rw [coprime_density_eq hp] at h2
  have hsplit : ∑ n ∈ Finset.Ioc t (t + L), coprimeSquarefreeWeight p n
        - (L : ℝ) * (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      = (∑ n ∈ Finset.Ioc t (t + L), coprimeSquarefreeWeight p n
          - ∑ n ∈ Finset.Ioc t (t + L),
              ∑ d ∈ Finset.Icc 1 R, (if d ^ 2 ∣ n ∧ ¬ p ∣ n then ((moebius d : ℤ) : ℝ) else 0))
        + (∑ n ∈ Finset.Ioc t (t + L),
              ∑ d ∈ Finset.Icc 1 R, (if d ^ 2 ∣ n ∧ ¬ p ∣ n then ((moebius d : ℤ) : ℝ) else 0)
            - (L : ℝ) * (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))) := by ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  linarith

/-- **The trivial window bound for the deleted weight.** -/
theorem abs_window_coprime_sub_le_len {p : ℕ} (hp : p.Prime) (t L : ℕ) :
    |∑ n ∈ Finset.Ioc t (t + L), coprimeSquarefreeWeight p n
        - (L : ℝ) * (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))| ≤ (L : ℝ) := by
  have hc0 := coprime_block_density_nonneg hp
  have hc1 := coprime_block_density_le_one hp
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h0 : 0 ≤ ∑ n ∈ Finset.Ioc t (t + L), coprimeSquarefreeWeight p n :=
    Finset.sum_nonneg (fun n _ => (coprimeSquarefreeWeight_mem p n).1)
  have h1 : ∑ n ∈ Finset.Ioc t (t + L), coprimeSquarefreeWeight p n ≤ (L : ℝ) := by
    refine le_trans (Finset.sum_le_sum (fun n _ => (coprimeSquarefreeWeight_mem p n).2)) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    simp
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- **The maximal squared window deviation of the deleted weight, pointwise.** -/
theorem maxWindowDevSq_coprime_le {p : ℕ} (hp : p.Prime) {y H R M : ℕ} (hy : 1 ≤ y)
    (hR : 1 ≤ R) (hM : (y - 1) + (H + 1) ≤ M) :
    maxWindowDevSq (coprimeSquarefreeWeight p)
        (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) H y
      ≤ ((H : ℝ) + 1) * (2 * (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
        + ∑ d ∈ Finset.Icc (R + 1) M,
            ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
              (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ)) := by
  classical
  refine Finset.sup'_le _ _ ?_
  intro m hm
  rw [Finset.mem_range] at hm
  have hmH : m ≤ H := by omega
  rw [Icc_eq_Ioc_pred_len hy]
  set t : ℕ := y - 1 with ht
  set E : ℝ := (∑ b ∈ Finset.Ioc t (t + (m + 1)), coprimeSquarefreeWeight p b)
    - squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1) * ((m : ℝ) + 1) with hE
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hEeq : E = (∑ b ∈ Finset.Ioc t (t + (m + 1)), coprimeSquarefreeWeight p b)
      - ((m + 1 : ℕ) : ℝ) * (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) := by
    rw [hE, hcast]
    ring
  have htriv : |E| ≤ ((H : ℝ) + 1) := by
    rw [hEeq]
    refine le_trans (abs_window_coprime_sub_le_len hp t (m + 1)) ?_
    rw [hcast]
    have : (m : ℝ) ≤ (H : ℝ) := by exact_mod_cast hmH
    linarith
  have hMle : t + (m + 1) ≤ M := by omega
  have hmain : |E| ≤ 2 * (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
      + ∑ d ∈ Finset.Icc (R + 1) M,
          ((((Finset.Ioc t (t + (H + 1))).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
    rw [hEeq]
    refine le_trans (abs_window_coprime_sub_le_defect hp t (m + 1) R M hR hMle) ?_
    have hmono := defect_mono (t := t) (L := m + 1) (L' := H + 1) (R := R) (M := M) (by omega)
    have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
    have hlen : ((m + 1 : ℕ) : ℝ) ≤ (H : ℝ) + 1 := by
      rw [hcast]
      have : (m : ℝ) ≤ (H : ℝ) := by exact_mod_cast hmH
      linarith
    have hdiv : ((m + 1 : ℕ) : ℝ) / (R : ℝ) ≤ ((H : ℝ) + 1) / (R : ℝ) :=
      div_le_div_of_nonneg_right hlen hR0.le
    linarith
  have hsq : E ^ 2 ≤ ((H : ℝ) + 1) * |E| := by
    have habs : |E| ^ 2 = E ^ 2 := sq_abs E
    nlinarith [abs_nonneg E, htriv]
  refine le_trans hsq ?_
  refine mul_le_mul_of_nonneg_left hmain (by positivity)

/-- **The maximal deviation of the deleted weight, summed over the starting points.** -/
theorem sum_maxWindowDevSq_coprime_le_sqrt {p : ℕ} (hp : p.Prime) {A B H R : ℕ} (hA : 1 ≤ A)
    (hR : 1 ≤ R) (hAB : A - 1 ≤ B + (H + 1)) :
    ∑ y ∈ Finset.Icc A B,
        maxWindowDevSq (coprimeSquarefreeWeight p)
          (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) H y
      ≤ ((H : ℝ) + 1) * (2 * (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)) * ((Finset.Icc A B).card : ℝ)
        + ((H : ℝ) + 1) * (((H : ℝ) + 1)
            * (((B : ℝ) + ((H : ℝ) + 1) - ((A - 1 : ℕ) : ℝ)) / (R : ℝ)
              + ((Nat.sqrt (B + (H + 1)) : ℕ) : ℝ))) := by
  classical
  have hterm : ∀ y ∈ Finset.Icc A B,
      maxWindowDevSq (coprimeSquarefreeWeight p)
          (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) H y
        ≤ ((H : ℝ) + 1) * (2 * (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ))
          + ((H : ℝ) + 1) * tailDefect R (B + (H + 1)) H (y - 1) := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    have hy1 : 1 ≤ y := le_trans hA hy.1
    have hMy : (y - 1) + (H + 1) ≤ B + (H + 1) := by omega
    have hbase := maxWindowDevSq_coprime_le hp (y := y) (H := H) (R := R)
      (M := B + (H + 1)) hy1 hR hMy
    rw [tailDefect]
    calc maxWindowDevSq (coprimeSquarefreeWeight p)
          (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) H y
        ≤ ((H : ℝ) + 1) * (2 * (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
            + ∑ d ∈ Finset.Icc (R + 1) (B + (H + 1)),
                ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
                  (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ)) := hbase
      _ = ((H : ℝ) + 1) * (2 * (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ))
            + ((H : ℝ) + 1) * ∑ d ∈ Finset.Icc (R + 1) (B + (H + 1)),
                ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
                  (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have himg : ∑ y ∈ Finset.Icc A B, tailDefect R (B + (H + 1)) H (y - 1)
      = ∑ t ∈ (Finset.Icc A B).image (fun y : ℕ => y - 1),
          tailDefect R (B + (H + 1)) H t :=
    (Finset.sum_image (fun a ha b hb hab => pred_injOn hA ha hb hab)).symm
  have hsub : ∑ t ∈ (Finset.Icc A B).image (fun y : ℕ => y - 1),
        tailDefect R (B + (H + 1)) H t
      ≤ ∑ t ∈ Finset.Ico (A - 1) B, tailDefect R (B + (H + 1)) H t :=
    Finset.sum_le_sum_of_subset_of_nonneg (image_pred_subset hA)
      (fun t _ _ => tailDefect_nonneg R (B + (H + 1)) H t)
  have htail := sum_tail_divisor_count_le_sqrt (A - 1) B (H + 1) R (B + (H + 1)) hR hAB
  have hcast : ((H + 1 : ℕ) : ℝ) = (H : ℝ) + 1 := by push_cast; ring
  rw [hcast] at htail
  have hH0 : (0 : ℝ) ≤ (H : ℝ) + 1 := by positivity
  have hchain : ∑ y ∈ Finset.Icc A B, tailDefect R (B + (H + 1)) H (y - 1)
      ≤ ((H : ℝ) + 1) * (((B : ℝ) + ((H : ℝ) + 1) - ((A - 1 : ℕ) : ℝ)) / (R : ℝ)
          + ((Nat.sqrt (B + (H + 1)) : ℕ) : ℝ)) := by
    rw [himg]
    refine le_trans hsub ?_
    exact htail
  nlinarith [hchain, hH0]

open Filter Topology in
/-- **The deleted-squarefree maximal window mean square, unconditionally.**  The card's third input
is a theorem too. -/
theorem maximalWindowDevMeanSquareAt_coprime {p : ℕ} (hp : p.Prime) {X hh : ℝ → ℝ}
    (hXtop : Tendsto X atTop atTop) (hgrow : Tendsto hh atTop atTop)
    (hsmall : ∀ᶠ x in atTop, hh x ≤ Real.sqrt (X x)) :
    MaximalWindowDevMeanSquareAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) X hh := by
  refine maximalWindowDevMeanSquareAt_of_sum_bound hXtop hgrow hsmall ?_
  intro A B H R hA hR hAB
  exact sum_maxWindowDevSq_coprime_le_sqrt hp hA hR hAB

end RHTower.Sieve
