import GaloisForLFunctions.RHTower.Sieve.FibreDevSeparation
import GaloisForLFunctions.RHTower.Sieve.SquarefreeTruncationDefect
import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail

/-!
# The maximal squarefree window deviation, pointwise

The squarefree count of a window differs from `LD` by the truncation error `R + L/R` of the density
series plus the mass of the square divisors above `R`:

    | ∑_{t < n ≤ t+L} μ²(n) − LD |  ≤  R + L/R + Def_R(t, L),
    Def_R(t, L) = ∑_{R < d ≤ M} #{n ∈ (t, t+L] : d² ∣ n}.

The defect is monotone in the window length, so a single bound at length `H+1` serves every shorter
window, and the deviation is trivially at most the length.  Hence the *maximal* squared deviation
over all lengths `≤ H` obeys

    max_{m ≤ H} (∑_{y ≤ n ≤ y+m} μ²(n) − (m+1)D)²  ≤  (H+1)·(R + (H+1)/R + Def_R(y−1, H+1)).

Bounding the square by the length times the modulus is what makes the estimate cheap: only a
*first* moment of the defect is then needed, and `AveragedSquarefreeTail` supplies exactly that.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The squarefree density is at most one. -/
theorem squarefreeDensity_le_one : squarefreeDensity ≤ 1 := by
  rw [squarefreeDensity_eq]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  rw [div_le_one (by positivity)]
  nlinarith

/-- The squarefree count of a window is between `0` and its length. -/
theorem sum_moebius_sq_window_mem (t L : ℕ) :
    0 ≤ ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2
      ∧ ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2 ≤ (L : ℝ) := by
  constructor
  · positivity
  · have hterm : ∀ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2 ≤ 1 := by
      intro n _
      have h := abs_moebius_sq_real_le_one n
      exact le_trans (le_abs_self _) h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    simp

/-- **The trivial window bound.** -/
theorem abs_window_squarefree_sub_le_len (t L : ℕ) :
    |∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2 - (L : ℝ) * squarefreeDensity|
      ≤ (L : ℝ) := by
  obtain ⟨h0, h1⟩ := sum_moebius_sq_window_mem t L
  have hD0 := squarefreeDensity_nonneg'
  have hD1 := squarefreeDensity_le_one
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- **The window bound with the truncation defect.** -/
theorem abs_window_squarefree_sub_le_defect (t L R M : ℕ) (hR : 1 ≤ R) (hM : t + L ≤ M) :
    |∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2 - (L : ℝ) * squarefreeDensity|
      ≤ (R : ℝ) + (L : ℝ) / (R : ℝ)
        + ∑ d ∈ Finset.Icc (R + 1) M,
            ((((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
  classical
  have h1 := abs_window_squarefree_sub_trunc_le t L R M hM
  have h2 := abs_truncated_squarefree_sub_le t L R hR
  have hsplit : ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2
        - (L : ℝ) * squarefreeDensity
      = (∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ 2
          - ∑ n ∈ Finset.Ioc t (t + L),
              ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ^ 2 ∣ n), ((moebius d : ℤ) : ℝ))
        + (∑ n ∈ Finset.Ioc t (t + L),
              ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ^ 2 ∣ n), ((moebius d : ℤ) : ℝ)
            - (L : ℝ) * squarefreeDensity) := by ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  linarith

/-- The defect is monotone in the window length. -/
theorem defect_mono {t L L' R M : ℕ} (hL : L ≤ L') :
    ∑ d ∈ Finset.Icc (R + 1) M,
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc (R + 1) M,
        ((((Finset.Ioc t (t + L')).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
  classical
  refine Finset.sum_le_sum ?_
  intro d _
  have hsub : (Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)
      ⊆ (Finset.Ioc t (t + L')).filter (fun n => d ^ 2 ∣ n) := by
    refine Finset.filter_subset_filter _ ?_
    exact Finset.Ioc_subset_Ioc_right (by omega)
  exact_mod_cast Finset.card_le_card hsub

/-- The window from `y` of length `m + 1` in the two indexings. -/
theorem Icc_eq_Ioc_pred {y m : ℕ} (hy : 1 ≤ y) :
    Finset.Icc y (y + m) = Finset.Ioc (y - 1) ((y - 1) + (m + 1)) := by
  ext n
  rw [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- **The maximal squared window deviation, pointwise.** -/
theorem maxWindowDevSq_moebius_sq_le {y H R M : ℕ} (hy : 1 ≤ y) (hR : 1 ≤ R)
    (hM : (y - 1) + (H + 1) ≤ M) :
    maxWindowDevSq (fun n : ℕ => ((moebius n : ℤ) : ℝ) ^ 2) squarefreeDensity H y
      ≤ ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
        + ∑ d ∈ Finset.Icc (R + 1) M,
            ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
              (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ)) := by
  classical
  refine Finset.sup'_le _ _ ?_
  intro m hm
  rw [Finset.mem_range] at hm
  have hmH : m ≤ H := by omega
  rw [Icc_eq_Ioc_pred hy]
  set t : ℕ := y - 1 with ht
  set E : ℝ := (∑ b ∈ Finset.Ioc t (t + (m + 1)), ((moebius b : ℤ) : ℝ) ^ 2)
    - squarefreeDensity * ((m : ℝ) + 1) with hE
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hEeq : E = (∑ b ∈ Finset.Ioc t (t + (m + 1)), ((moebius b : ℤ) : ℝ) ^ 2)
      - ((m + 1 : ℕ) : ℝ) * squarefreeDensity := by
    rw [hE, hcast]
    ring
  have htriv : |E| ≤ ((H : ℝ) + 1) := by
    rw [hEeq]
    refine le_trans (abs_window_squarefree_sub_le_len t (m + 1)) ?_
    rw [hcast]
    have : (m : ℝ) ≤ (H : ℝ) := by exact_mod_cast hmH
    linarith
  have hMle : t + (m + 1) ≤ M := by omega
  have hmain : |E| ≤ (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
      + ∑ d ∈ Finset.Icc (R + 1) M,
          ((((Finset.Ioc t (t + (H + 1))).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
    rw [hEeq]
    refine le_trans (abs_window_squarefree_sub_le_defect t (m + 1) R M hR hMle) ?_
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

/-- The shifted starting points of a range of windows. -/
theorem image_pred_subset {A B : ℕ} (hA : 1 ≤ A) :
    (Finset.Icc A B).image (fun y : ℕ => y - 1) ⊆ Finset.Ico (A - 1) B := by
  intro t ht
  rw [Finset.mem_image] at ht
  obtain ⟨y, hy, rfl⟩ := ht
  rw [Finset.mem_Icc] at hy
  rw [Finset.mem_Ico]
  omega

theorem pred_injOn {A B : ℕ} (hA : 1 ≤ A) {y y' : ℕ}
    (hy : y ∈ Finset.Icc A B) (hy' : y' ∈ Finset.Icc A B) (heq : y - 1 = y' - 1) : y = y' := by
  rw [Finset.mem_Icc] at hy hy'
  omega

/-- The mass of the square divisors above `R` in a window of length `H + 1`. -/
noncomputable def tailDefect (R M H t : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (R + 1) M,
    ((((Finset.Ioc t (t + (H + 1))).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ)

theorem tailDefect_nonneg (R M H t : ℕ) : 0 ≤ tailDefect R M H t := by
  rw [tailDefect]
  positivity

/-- **The maximal squarefree window deviation, summed over the starting points.** -/
theorem sum_maxWindowDevSq_moebius_sq_le {A B H R M : ℕ} (hA : 1 ≤ A) (hR : 1 ≤ R)
    (hM : B + (H + 1) ≤ M) (hAB : A - 1 ≤ B + (H + 1)) :
    ∑ y ∈ Finset.Icc A B,
        maxWindowDevSq (fun n : ℕ => ((moebius n : ℤ) : ℝ) ^ 2) squarefreeDensity H y
      ≤ ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)) * ((Finset.Icc A B).card : ℝ)
        + ((H : ℝ) + 1) * (((H : ℝ) + 1)
            * (((B : ℝ) + ((H : ℝ) + 1) - ((A - 1 : ℕ) : ℝ)) / (R : ℝ) + (M : ℝ))) := by
  classical
  have hterm : ∀ y ∈ Finset.Icc A B,
      maxWindowDevSq (fun n : ℕ => ((moebius n : ℤ) : ℝ) ^ 2) squarefreeDensity H y
        ≤ ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ))
          + ((H : ℝ) + 1) * tailDefect R M H (y - 1) := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    have hy1 : 1 ≤ y := le_trans hA hy.1
    have hMy : (y - 1) + (H + 1) ≤ M := by omega
    have hbase := maxWindowDevSq_moebius_sq_le (y := y) (H := H) (R := R) (M := M) hy1 hR hMy
    rw [tailDefect]
    calc maxWindowDevSq (fun n : ℕ => ((moebius n : ℤ) : ℝ) ^ 2) squarefreeDensity H y
        ≤ ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
            + ∑ d ∈ Finset.Icc (R + 1) M,
                ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
                  (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ)) := hbase
      _ = ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ))
            + ((H : ℝ) + 1) * ∑ d ∈ Finset.Icc (R + 1) M,
                ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
                  (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have himg : ∑ y ∈ Finset.Icc A B, tailDefect R M H (y - 1)
      = ∑ t ∈ (Finset.Icc A B).image (fun y : ℕ => y - 1), tailDefect R M H t :=
    (Finset.sum_image (fun a ha b hb hab => pred_injOn hA ha hb hab)).symm
  have hsub : ∑ t ∈ (Finset.Icc A B).image (fun y : ℕ => y - 1), tailDefect R M H t
      ≤ ∑ t ∈ Finset.Ico (A - 1) B, tailDefect R M H t :=
    Finset.sum_le_sum_of_subset_of_nonneg (image_pred_subset hA)
      (fun t _ _ => tailDefect_nonneg R M H t)
  have htail := sum_tail_divisor_count_le (A - 1) B (H + 1) R M hR hAB
  have hcast : ((H + 1 : ℕ) : ℝ) = (H : ℝ) + 1 := by push_cast; ring
  rw [hcast] at htail
  have hH0 : (0 : ℝ) ≤ (H : ℝ) + 1 := by positivity
  have hchain : ∑ y ∈ Finset.Icc A B, tailDefect R M H (y - 1)
      ≤ ((H : ℝ) + 1) * (((B : ℝ) + ((H : ℝ) + 1) - ((A - 1 : ℕ) : ℝ)) / (R : ℝ) + (M : ℝ)) := by
    rw [himg]
    refine le_trans hsub ?_
    exact htail
  nlinarith [hchain, hH0]

/-- A square divisor larger than the square root of the range cannot occur. -/
theorem count_sq_dvd_eq_zero_of_large {t L B d : ℕ} (ht : t < B) (hd : Nat.sqrt (B + L) < d) :
    (((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) = 0 := by
  classical
  rw [Finset.card_eq_zero]
  refine Finset.filter_eq_empty_iff.2 ?_
  intro n hn hdvd
  rw [Finset.mem_Ioc] at hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le t) hn.1
  have hle : d ^ 2 ≤ n := Nat.le_of_dvd hn0 hdvd
  have hnB : n ≤ B + L := by omega
  have hbig : B + L < d * d := Nat.sqrt_lt.mp hd
  have hsq : d ^ 2 = d * d := by ring
  omega

/-- **The averaged tail, with the divisor range cut at the square root.**  Divisors above
`√(B+L)` contribute nothing, so the `M` of `sum_tail_divisor_count_le` may be replaced by
`⌊√(B+L)⌋` — which is what makes the estimate `o` of the window length squared. -/
theorem sum_tail_divisor_count_le_sqrt (A B L R M : ℕ) (hR : 1 ≤ R) (hAB : A ≤ B + L) :
    (∑ t ∈ Finset.Ico A B,
        ∑ d ∈ Finset.Icc (R + 1) M,
          ((((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ))
      ≤ (L : ℝ) * (((B : ℝ) + L - A) / (R : ℝ) + ((Nat.sqrt (B + L) : ℕ) : ℝ)) := by
  classical
  set M' : ℕ := min M (Nat.sqrt (B + L)) with hM'
  have hcut : ∀ t ∈ Finset.Ico A B,
      ∑ d ∈ Finset.Icc (R + 1) M,
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc (R + 1) M',
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ) := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    refine (Finset.sum_subset ?_ ?_).symm
    · intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 (min_le_left _ _)⟩
    · intro d hd hnot
      rw [Finset.mem_Icc] at hd
      rw [Finset.mem_Icc] at hnot
      have hlarge : Nat.sqrt (B + L) < d := by
        rw [hM'] at hnot
        omega
      rw [count_sq_dvd_eq_zero_of_large ht.2 hlarge]
      norm_num
  rw [Finset.sum_congr rfl hcut]
  refine le_trans (sum_tail_divisor_count_le A B L R M' hR hAB) ?_
  have hM'le : ((M' : ℕ) : ℝ) ≤ ((Nat.sqrt (B + L) : ℕ) : ℝ) := by
    have : M' ≤ Nat.sqrt (B + L) := min_le_right _ _
    exact_mod_cast this
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  nlinarith [hM'le, hL0]

/-- **The maximal squarefree window deviation, summed, with the sharp divisor range.** -/
theorem sum_maxWindowDevSq_moebius_sq_le_sqrt {A B H R : ℕ} (hA : 1 ≤ A) (hR : 1 ≤ R)
    (hAB : A - 1 ≤ B + (H + 1)) :
    ∑ y ∈ Finset.Icc A B,
        maxWindowDevSq (fun n : ℕ => ((moebius n : ℤ) : ℝ) ^ 2) squarefreeDensity H y
      ≤ ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)) * ((Finset.Icc A B).card : ℝ)
        + ((H : ℝ) + 1) * (((H : ℝ) + 1)
            * (((B : ℝ) + ((H : ℝ) + 1) - ((A - 1 : ℕ) : ℝ)) / (R : ℝ)
              + ((Nat.sqrt (B + (H + 1)) : ℕ) : ℝ))) := by
  classical
  have hterm : ∀ y ∈ Finset.Icc A B,
      maxWindowDevSq (fun n : ℕ => ((moebius n : ℤ) : ℝ) ^ 2) squarefreeDensity H y
        ≤ ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ))
          + ((H : ℝ) + 1) * tailDefect R (B + (H + 1)) H (y - 1) := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    have hy1 : 1 ≤ y := le_trans hA hy.1
    have hMy : (y - 1) + (H + 1) ≤ B + (H + 1) := by omega
    have hbase := maxWindowDevSq_moebius_sq_le (y := y) (H := H) (R := R)
      (M := B + (H + 1)) hy1 hR hMy
    rw [tailDefect]
    calc maxWindowDevSq (fun n : ℕ => ((moebius n : ℤ) : ℝ) ^ 2) squarefreeDensity H y
        ≤ ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
            + ∑ d ∈ Finset.Icc (R + 1) (B + (H + 1)),
                ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
                  (fun n => d ^ 2 ∣ n)).card : ℕ) : ℝ)) := hbase
      _ = ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ))
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

/-- The algebraic core of the limit: with `u = √h` and `v = √√x`, the summed bound divided by
`h²√x` is at most `16/u + 8/v`. -/
theorem maximal_bound_arith {u v HH RR cardv Bv sqv : ℝ}
    (hu : 3 ≤ u) (hv : 3 ≤ v)
    (hHH0 : 0 ≤ HH) (hHH : HH ≤ 2 * u ^ 2)
    (hRlow : u ≤ RR) (hRup : RR ≤ 2 * u)
    (hcard0 : 0 ≤ cardv) (hcard : cardv ≤ v ^ 2)
    (hrange0 : 0 ≤ Bv) (hrange : Bv ≤ 2 * v ^ 2)
    (hsq0 : 0 ≤ sqv) (hsq : sqv ≤ 2 * v) :
    HH * (RR + HH / RR) * cardv + HH * (HH * (Bv / RR + sqv))
      ≤ 16 * u ^ 3 * v ^ 2 + 8 * u ^ 4 * v := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hR0 : (0 : ℝ) < RR := by linarith
  have hdiv1 : HH / RR ≤ 2 * u := by
    rw [div_le_iff₀ hR0]
    nlinarith
  have hdiv2 : Bv / RR ≤ 2 * v ^ 2 / u := by
    rw [div_le_div_iff₀ hR0 hu0]
    nlinarith
  have hfirst : HH * (RR + HH / RR) * cardv ≤ 8 * u ^ 3 * v ^ 2 := by
    have hsum : RR + HH / RR ≤ 4 * u := by linarith
    have h1 : HH * (RR + HH / RR) ≤ 2 * u ^ 2 * (4 * u) := by
      refine mul_le_mul hHH hsum ?_ (by positivity)
      have : (0 : ℝ) ≤ HH / RR := by positivity
      linarith
    have h2 : HH * (RR + HH / RR) * cardv ≤ (2 * u ^ 2 * (4 * u)) * v ^ 2 := by
      refine mul_le_mul h1 hcard hcard0 (by positivity)
    nlinarith [h2]
  have hsecond : HH * (HH * (Bv / RR + sqv)) ≤ 8 * u ^ 3 * v ^ 2 + 8 * u ^ 4 * v := by
    have hinner : Bv / RR + sqv ≤ 2 * v ^ 2 / u + 2 * v := by linarith
    have hinner0 : (0 : ℝ) ≤ Bv / RR + sqv := by positivity
    have h1 : HH * (Bv / RR + sqv) ≤ 2 * u ^ 2 * (2 * v ^ 2 / u + 2 * v) :=
      mul_le_mul hHH hinner hinner0 (by positivity)
    have h10 : (0 : ℝ) ≤ HH * (Bv / RR + sqv) := by positivity
    have h2 : HH * (HH * (Bv / RR + sqv)) ≤ 2 * u ^ 2 * (2 * u ^ 2 * (2 * v ^ 2 / u + 2 * v)) :=
      mul_le_mul hHH h1 h10 (by positivity)
    have hval : 2 * u ^ 2 * (2 * u ^ 2 * (2 * v ^ 2 / u + 2 * v))
        = 8 * u ^ 3 * v ^ 2 + 8 * u ^ 4 * v := by
      field_simp
      ring
    rw [hval] at h2
    exact h2
  linarith

end RHTower.Sieve
