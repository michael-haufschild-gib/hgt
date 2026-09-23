import GaloisForLFunctions.RHTower.Sieve.AveragedChowlaInterface

/-!
# Short-interval mean squares are Fejér-weighted correlation sums

Expanding the square of a window sum and collecting by the difference of the two indices,

```text
∑_{y < Y} ( ∑_{i < H} f(y+i) )²  =  2 ∑_{k < H} (H − k)·C_k  −  H·C_0  +  O(H³) ,
```

where `C_k = ∑_{y < Y} f(y)f(y+k)` and the error comes only from translating each correlation back
to the origin — a change of at most `2H` terms in each of the `H²` pairs.

This is the exact sense in which a short-interval mean square is a correlation statement: it
controls the **signed**, Fejér-weighted correlation sum.  Averaged Chowla asks for the sum of the
**moduli** `∑_k |C_k|`, which the identity cannot supply — the whole difficulty of
`AveragedChowlaUniform` sits in that replacement.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The correlation of `f` at shift `k` over the initial segment of length `Y`. -/
def corrSum (f : ℕ → ℝ) (Y k : ℕ) : ℝ := ∑ y ∈ Finset.range Y, f y * f (y + k)

/-- The Fejér-weighted signed correlation sum. -/
def fejerCorr (f : ℕ → ℝ) (Y H : ℕ) : ℝ :=
  2 * (∑ k ∈ Finset.range H, ((H : ℝ) - (k : ℝ)) * corrSum f Y k) - (H : ℝ) * corrSum f Y 0

/-- **Collecting a symmetric double sum by the difference of its indices.** -/
theorem sum_dist_double (F : ℕ → ℝ) (H : ℕ) :
    ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, F (max i j - min i j)
      = 2 * (∑ k ∈ Finset.range H, ((H : ℝ) - (k : ℝ)) * F k) - (H : ℝ) * F 0 := by
  induction H with
  | zero => simp
  | succ H ih =>
      have hrow : ∀ j : ℕ, j < H + 1 → max H j - min H j = H - j := by
        intro j hj
        rw [max_eq_left (by omega), min_eq_right (by omega)]
      have hcol : ∀ i : ℕ, i < H → max i H - min i H = H - i := by
        intro i hi
        rw [max_eq_right (by omega), min_eq_left (by omega)]
      -- peel the last row and the last column
      have hsplit : ∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1),
            F (max i j - min i j)
          = (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, F (max i j - min i j))
            + (∑ i ∈ Finset.range H, F (H - i))
            + ∑ j ∈ Finset.range (H + 1), F (H - j) := by
        rw [Finset.sum_range_succ]
        have hinner : ∀ i ∈ Finset.range H,
            ∑ j ∈ Finset.range (H + 1), F (max i j - min i j)
              = (∑ j ∈ Finset.range H, F (max i j - min i j)) + F (H - i) := by
          intro i hi
          rw [Finset.mem_range] at hi
          rw [Finset.sum_range_succ, hcol i hi]
        rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
        have hlast : ∑ j ∈ Finset.range (H + 1), F (max H j - min H j)
            = ∑ j ∈ Finset.range (H + 1), F (H - j) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mem_range] at hj
          rw [hrow j hj]
        rw [hlast]
      -- the two reflected sums
      have hrefl : ∑ j ∈ Finset.range (H + 1), F (H - j)
          = ∑ k ∈ Finset.range (H + 1), F k := by
        have := Finset.sum_range_reflect F (H + 1)
        simpa using this
      have hrefl' : ∑ i ∈ Finset.range H, F (H - i)
          = (∑ k ∈ Finset.range (H + 1), F k) - F 0 := by
        have hstep : ∑ j ∈ Finset.range (H + 1), F (H - j)
            = (∑ i ∈ Finset.range H, F (H - i)) + F (H - H) := Finset.sum_range_succ _ _
        rw [hrefl] at hstep
        have hHH : H - H = 0 := by omega
        rw [hHH] at hstep
        linarith
      rw [hsplit, ih, hrefl, hrefl']
      -- and the right-hand side telescopes the same way
      have hR : ∑ k ∈ Finset.range (H + 1), (((H + 1 : ℕ) : ℝ) - (k : ℝ)) * F k
          = (∑ k ∈ Finset.range H, ((H : ℝ) - (k : ℝ)) * F k)
            + ∑ k ∈ Finset.range (H + 1), F k := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ (f := F) (n := H)]
        have hterms : ∀ k ∈ Finset.range H,
            (((H + 1 : ℕ) : ℝ) - (k : ℝ)) * F k
              = ((H : ℝ) - (k : ℝ)) * F k + F k := by
          intro k _
          push_cast
          ring
        rw [Finset.sum_congr rfl hterms, Finset.sum_add_distrib]
        push_cast
        ring
      rw [hR]
      push_cast
      ring

/-- **The window mean square, expanded.** -/
theorem sum_window_sq_eq (f : ℕ → ℝ) (Y H : ℕ) :
    ∑ y ∈ Finset.range Y, (∑ i ∈ Finset.range H, f (y + i)) ^ (2 : ℕ)
      = ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
          ∑ y ∈ Finset.range Y, f (y + i) * f (y + j) := by
  have hexp : ∀ y : ℕ, (∑ i ∈ Finset.range H, f (y + i)) ^ (2 : ℕ)
      = ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, f (y + i) * f (y + j) := by
    intro y
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun y _ => hexp y]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- Translating a correlation back to the origin changes at most `2i` terms. -/
theorem abs_shifted_corr_sub_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (Y i k : ℕ) :
    |∑ y ∈ Finset.range Y, f (y + i) * f (y + i + k) - corrSum f Y k| ≤ 2 * (i : ℝ) := by
  classical
  set g : ℕ → ℝ := fun y => f y * f (y + k) with hg
  have hone : ∀ y, |g y| ≤ 1 := by
    intro y
    rw [hg, abs_mul]
    nlinarith [hf y, hf (y + k), abs_nonneg (f y), abs_nonneg (f (y + k))]
  have hleft : ∑ y ∈ Finset.range Y, f (y + i) * f (y + i + k)
      = ∑ y ∈ Finset.Ico i (Y + i), g y := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : Y + i - i = Y := by omega
    rw [hlen]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hg]
    have h1 : i + y = y + i := by omega
    rw [h1]
  have hsplit : ∑ y ∈ Finset.Ico 0 (Y + i), g y
      = (∑ y ∈ Finset.Ico 0 i, g y) + ∑ y ∈ Finset.Ico i (Y + i), g y :=
    (Finset.sum_Ico_consecutive g (Nat.zero_le i) (by omega)).symm
  have hsplit' : ∑ y ∈ Finset.Ico 0 (Y + i), g y
      = (∑ y ∈ Finset.Ico 0 Y, g y) + ∑ y ∈ Finset.Ico Y (Y + i), g y :=
    (Finset.sum_Ico_consecutive g (Nat.zero_le Y) (by omega)).symm
  have hcorr : corrSum f Y k = ∑ y ∈ Finset.Ico 0 Y, g y := by
    rw [corrSum, Finset.range_eq_Ico]
  have hdiff : ∑ y ∈ Finset.range Y, f (y + i) * f (y + i + k) - corrSum f Y k
      = (∑ y ∈ Finset.Ico Y (Y + i), g y) - ∑ y ∈ Finset.Ico 0 i, g y := by
    rw [hleft, hcorr]
    linarith [hsplit, hsplit']
  rw [hdiff]
  have hb1 : |∑ y ∈ Finset.Ico Y (Y + i), g y| ≤ (i : ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun y _ => hone y) ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    have : Y + i - Y = i := by omega
    rw [this]
  have hb2 : |∑ y ∈ Finset.Ico 0 i, g y| ≤ (i : ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun y _ => hone y) ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    have : i - 0 = i := by omega
    rw [this]
  refine le_trans (abs_sub _ _) ?_
  linarith

/-- The same, for an unordered pair of shifts. -/
theorem abs_pair_corr_sub_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (Y i j : ℕ) :
    |∑ y ∈ Finset.range Y, f (y + i) * f (y + j) - corrSum f Y (max i j - min i j)|
      ≤ 2 * ((min i j : ℕ) : ℝ) := by
  rcases le_total i j with hij | hij
  · have hmax : max i j - min i j = j - i := by
      rw [max_eq_right hij, min_eq_left hij]
    have hmin : min i j = i := min_eq_left hij
    rw [hmax, hmin]
    have hbase := abs_shifted_corr_sub_le hf Y i (j - i)
    have hcongr : ∑ y ∈ Finset.range Y, f (y + i) * f (y + i + (j - i))
        = ∑ y ∈ Finset.range Y, f (y + i) * f (y + j) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      have : y + i + (j - i) = y + j := by omega
      rw [this]
    rwa [hcongr] at hbase
  · have hmax : max i j - min i j = i - j := by
      rw [max_eq_left hij, min_eq_right hij]
    have hmin : min i j = j := min_eq_right hij
    rw [hmax, hmin]
    have hbase := abs_shifted_corr_sub_le hf Y j (i - j)
    have hcongr : ∑ y ∈ Finset.range Y, f (y + j) * f (y + j + (i - j))
        = ∑ y ∈ Finset.range Y, f (y + i) * f (y + j) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      have : y + j + (i - j) = y + i := by omega
      rw [this, mul_comm]
    rwa [hcongr] at hbase

/-- **The window mean square is the Fejér-weighted correlation sum, up to `2H³`.** -/
theorem abs_sum_window_sq_sub_fejerCorr_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (Y H : ℕ) :
    |∑ y ∈ Finset.range Y, (∑ i ∈ Finset.range H, f (y + i)) ^ (2 : ℕ) - fejerCorr f Y H|
      ≤ 2 * (H : ℝ) ^ (3 : ℕ) := by
  classical
  have hfej : fejerCorr f Y H
      = ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, corrSum f Y (max i j - min i j) := by
    rw [fejerCorr, ← sum_dist_double (corrSum f Y) H]
  rw [sum_window_sq_eq f Y H, hfej, ← Finset.sum_sub_distrib]
  have hrow : ∀ i ∈ Finset.range H,
      |(∑ j ∈ Finset.range H, ∑ y ∈ Finset.range Y, f (y + i) * f (y + j))
        - ∑ j ∈ Finset.range H, corrSum f Y (max i j - min i j)| ≤ 2 * (H : ℝ) ^ (2 : ℕ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ j ∈ Finset.range H,
        |(∑ y ∈ Finset.range Y, f (y + i) * f (y + j))
          - corrSum f Y (max i j - min i j)| ≤ 2 * (H : ℝ) := by
      intro j _
      refine le_trans (abs_pair_corr_sub_le hf Y i j) ?_
      have hmin : ((min i j : ℕ) : ℝ) ≤ (H : ℝ) := by
        have : min i j ≤ H := le_trans (min_le_left i j) (by omega)
        exact_mod_cast this
      linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    nlinarith [Nat.cast_nonneg (α := ℝ) H]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hrow) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) H]

theorem corrSum_zero_nonneg (f : ℕ → ℝ) (Y : ℕ) : 0 ≤ corrSum f Y 0 := by
  rw [corrSum]
  refine Finset.sum_nonneg fun y _ => ?_
  simpa using mul_self_nonneg (f y)

theorem corrSum_zero_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (Y : ℕ) : corrSum f Y 0 ≤ (Y : ℝ) := by
  rw [corrSum]
  have hterm : ∀ y ∈ Finset.range Y, f y * f (y + 0) ≤ 1 := by
    intro y _
    have hy : y + 0 = y := by omega
    rw [hy]
    nlinarith [hf y, abs_nonneg (f y), abs_mul_abs_self (f y)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- Splitting off the diagonal shift. -/
theorem sum_range_fejer_split (f : ℕ → ℝ) (Y H : ℕ) :
    ∑ k ∈ Finset.range H, ((H : ℝ) - (k : ℝ)) * corrSum f Y k
      = (H : ℝ) * corrSum f Y 0
        + ∑ k ∈ Finset.Ico 1 H, ((H : ℝ) - (k : ℝ)) * corrSum f Y k := by
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst hH
    simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hH]
    push_cast
    ring

/-- **Half of averaged Chowla is free.**  For any unit-bounded weight the Fejér-weighted correlation
sum is bounded below by `−HY/2 − H³`, because the window mean square it computes is a sum of
squares.  Only the upper bound, and the passage from the signed sum to the sum of moduli, carry
arithmetic content. -/
theorem fejer_ge {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (Y H : ℕ) :
    -((H : ℝ) * (Y : ℝ) / 2) - (H : ℝ) ^ (3 : ℕ)
      ≤ ∑ k ∈ Finset.Ico 1 H, ((H : ℝ) - (k : ℝ)) * corrSum f Y k := by
  have hsq : (0 : ℝ) ≤ ∑ y ∈ Finset.range Y, (∑ i ∈ Finset.range H, f (y + i)) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun y _ => sq_nonneg _
  have hclose := abs_sum_window_sq_sub_fejerCorr_le hf Y H
  have hlow : -(2 * (H : ℝ) ^ (3 : ℕ)) ≤ fejerCorr f Y H := by
    have := (abs_le.1 hclose).2
    linarith
  rw [fejerCorr, sum_range_fejer_split f Y H] at hlow
  have hc0 := corrSum_zero_le hf Y
  have hc0' := corrSum_zero_nonneg f Y
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  nlinarith [hlow, hc0, hc0', hH0]

/-- **The upper bound is exactly the window mean square.** -/
theorem fejer_le_of_window {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (Y H : ℕ) {W : ℝ}
    (hW : ∑ y ∈ Finset.range Y, (∑ i ∈ Finset.range H, f (y + i)) ^ (2 : ℕ) ≤ W) :
    ∑ k ∈ Finset.Ico 1 H, ((H : ℝ) - (k : ℝ)) * corrSum f Y k ≤ (W + 2 * (H : ℝ) ^ (3 : ℕ)) / 2 := by
  have hclose := abs_sum_window_sq_sub_fejerCorr_le hf Y H
  have hup : fejerCorr f Y H ≤ W + 2 * (H : ℝ) ^ (3 : ℕ) := by
    have := (abs_le.1 hclose).1
    linarith
  rw [fejerCorr, sum_range_fejer_split f Y H] at hup
  have hc0' := corrSum_zero_nonneg f Y
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  nlinarith [hup, hc0', hH0]

end RHTower.Sieve

end
