import GaloisForLFunctions.RHTower.Sieve.DirichletPrefixLittlewood
import GaloisForLFunctions.RHTower.Sieve.ZetaWideRectangle

/-!
# Littlewood's rate on a shifted abscissa

Abel summation against the decreasing weight `n^{-δ}` transports the prefix-uniform Littlewood
estimate from the line `Re s = 1` to every abscissa `Re s = 1 + δ` with `δ ≥ 0`, at no cost: the
weight is one at the first index.  Truncating the zeta function at the same canonical point then
gives

```text
|ζ(1 + δ + it)| ≤ 32 + 2 log(t/2π) / (orderLowerBound(log(t/2π)) - 4/3),
```

uniformly in `δ ∈ [0,1]`.
-/

namespace RHTower.Sieve

open Finset

/-- Splitting the shifted Dirichlet term into the real weight and the unshifted term. -/
theorem cpow_shift_split {n : ℕ} (hn : 1 ≤ n) (δ t : ℝ) :
    (n : ℂ) ^ (-((1 : ℂ) + (δ : ℂ)) - Complex.I * (t : ℂ))
      = (((n : ℝ) ^ (-δ) : ℝ) : ℂ) * (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : 0 < n := hn
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega)
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsplit : -((1 : ℂ) + (δ : ℂ)) - Complex.I * (t : ℂ)
      = ((-δ : ℝ) : ℂ) + (-1 - Complex.I * (t : ℂ)) := by
    push_cast
    ring
  have hbase : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; ring
  rw [hsplit, Complex.cpow_add _ _ hn0]
  congr 1
  rw [← hbase]
  exact (Complex.ofReal_cpow hnR (-δ)).symm

/-- **Abel summation moves the prefix bound to a shifted abscissa.** -/
theorem norm_dirichlet_shifted_prefix_le {t δ : ℝ} (hδ : 0 ≤ δ) {M : ℕ} {P : ℝ}
    (hP : ∀ m : ℕ, m ≤ M →
      ‖∑ n ∈ Finset.Ico 1 m, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-((1 : ℂ) + (δ : ℂ)) - Complex.I * (t : ℂ))‖ ≤ P := by
  have hP0 : 0 ≤ P := le_trans (norm_nonneg _) (hP 0 (Nat.zero_le M))
  rcases Nat.lt_or_ge M 1 with hM0 | hM1
  · have hempty : Finset.Ico 1 M = (∅ : Finset ℕ) := Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, norm_zero]
    exact hP0
  · have hrw : ∑ n ∈ Finset.Ico 1 M, (n : ℂ) ^ (-((1 : ℂ) + (δ : ℂ)) - Complex.I * (t : ℂ))
        = ∑ n ∈ Finset.Ico 1 M,
          ((((n : ℝ) ^ (-δ) : ℝ)) : ℂ) * (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      exact cpow_shift_split (Finset.mem_Ico.mp hn).1 δ t
    rw [hrw]
    have hanti : ∀ m : ℕ, 1 ≤ m → m < M → ((m + 1 : ℕ) : ℝ) ^ (-δ) ≤ ((m : ℕ) : ℝ) ^ (-δ) := by
      intro m hm _
      have hm1 : (1 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm
      have hle : ((m : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ m
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith : -δ ≤ 0)
    have hw0 : (0 : ℝ) ≤ ((M : ℕ) : ℝ) ^ (-δ) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    have habel := abel_block_bound (fun n => (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)))
      (fun n => ((n : ℕ) : ℝ) ^ (-δ)) 1 M hM1 hw0 hanti P
      (fun m _ hmM => hP m hmM)
    have hone : ((1 : ℕ) : ℝ) ^ (-δ) = 1 := by
      norm_num
    rw [hone, mul_one] at habel
    exact habel

/-- **Littlewood's rate for `ζ` on a shifted abscissa.** -/
theorem norm_riemannZeta_shifted_line_rate {t δ : ℝ} (ht16 : 16 * Real.pi ≤ t)
    (ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi)))
    (hd : 4 / 3 < orderLowerBound (Real.log (t / (2 * Real.pi))))
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖
      ≤ 33 + 2 * Real.log (t / (2 * Real.pi))
          / (orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3) := by
  have hπ := Real.pi_pos
  have ht8 : 8 * Real.pi ≤ t := by linarith
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have hM1 : 1 ≤ lineTruncation t := one_le_lineTruncation t
  have hNR : (1 : ℝ) ≤ ((lineTruncation t : ℕ) : ℝ) := by exact_mod_cast hM1
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = ((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ) := ⟨_, rfl⟩
  have hwre : w.re = 1 + δ := by
    rw [hwdef]
    simp
  have hwim : w.im = t := by
    rw [hwdef]
    simp
  have hw0 : 0 < w.re := by
    rw [hwre]
    linarith
  have hwne1 : w ≠ 1 := by
    intro hcon
    have : w.im = 0 := by rw [hcon]; simp
    rw [hwim] at this
    exact absurd this (ne_of_gt ht)
  have hbase := norm_riemannZeta_le_partialSum hw0 hwne1 hM1
  -- the partial sum, in prefix form
  have hsum : ∑ k ∈ Finset.Icc 1 (lineTruncation t), ((k : ℝ) : ℂ) ^ (-w)
      = ∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
          (n : ℂ) ^ (-((1 : ℂ) + (δ : ℂ)) - Complex.I * (t : ℂ)) := by
    have hcast : (((1 + δ : ℝ) : ℂ)) = (1 : ℂ) + (δ : ℂ) := by push_cast; ring
    have hw : ((( 1 + δ : ℝ) : ℂ)) + Complex.I * (t : ℂ) = w := hwdef.symm
    rw [← lineTruncation_add_one t, show (-w) = -(((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) by
      rw [hw]]
    have h := sum_Icc_cpow_eq_sum_Ico_sigma (1 + δ) t (lineTruncation t)
    rw [h]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hcast]
  have hprefix : ∀ m : ℕ, m ≤ 2 ^ (topExponent t + 1) →
      ‖∑ n ∈ Finset.Ico 1 m, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
        ≤ 1 + Real.log 2 + 2 * Real.log (t / (2 * Real.pi))
            / (orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3) :=
    fun m hm => norm_dirichlet_partial_littlewood_rate_prefix ht16 ht2 hd hm
  have hhead := norm_dirichlet_shifted_prefix_le (t := t) (δ := δ) hδ0
    (M := 2 ^ (topExponent t + 1)) hprefix
  rw [← hsum] at hhead
  -- the two tail terms
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have htail1 : ((lineTruncation t : ℕ) : ℝ) ^ (1 - w.re) / ‖w - 1‖ ≤ 1 := by
    have h1 : ((lineTruncation t : ℕ) : ℝ) ^ (1 - w.re) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos hNR ?_
      rw [hwre]
      linarith
    have h2 : (1 : ℝ) ≤ ‖w - 1‖ := by
      have h := Complex.abs_im_le_norm (w - 1)
      have him' : (w - 1).im = t := by
        rw [Complex.sub_im, hwim]
        simp
      rw [him', abs_of_pos ht] at h
      have h16 : (1 : ℝ) ≤ t := by
        have hpi3 := Real.pi_gt_three
        linarith
      linarith
    have h3 : (0 : ℝ) < ‖w - 1‖ := by linarith
    rw [div_le_one h3]
    linarith
  have hcube : (1 : ℝ) < (t / (8 * Real.pi)) ^ (3 : ℕ) := by
    have h2 : (2 : ℝ) ≤ t / (8 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    calc (1 : ℝ) < 2 ^ (3 : ℕ) := by norm_num
      _ ≤ (t / (8 * Real.pi)) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 3
  have hden : (0 : ℝ) < (t / (8 * Real.pi)) ^ (3 : ℕ) - 1 := by linarith
  have hNpos : (0 : ℝ) < ((lineTruncation t : ℕ) : ℝ) :=
    lt_of_lt_of_le hden (cube_sub_one_le_lineTruncation ht8)
  have hnormw : ‖w‖ ≤ 2 + t := by
    rw [hwdef]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖((1 + δ : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have h2 : ‖Complex.I * (t : ℂ)‖ = t := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht]
    linarith [h1, h2.le, h2.ge]
  have htail2 : ‖w‖ * (((lineTruncation t : ℕ) : ℝ) ^ (-w.re) / w.re) ≤ 30 := by
    have hmono : ((lineTruncation t : ℕ) : ℝ) ^ (-w.re) ≤ ((lineTruncation t : ℕ) : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNR (by rw [hwre]; linarith)
    have hone : ((lineTruncation t : ℕ) : ℝ) ^ (-1 : ℝ) = 1 / ((lineTruncation t : ℕ) : ℝ) := by
      rw [Real.rpow_neg hNpos.le, Real.rpow_one, one_div]
    rw [hone] at hmono
    have hdiv : ((lineTruncation t : ℕ) : ℝ) ^ (-w.re) / w.re
        ≤ 1 / ((lineTruncation t : ℕ) : ℝ) := by
      have hstep : ((lineTruncation t : ℕ) : ℝ) ^ (-w.re) / w.re
          ≤ ((lineTruncation t : ℕ) : ℝ) ^ (-w.re) / 1 := by
        refine div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _) (by norm_num) ?_
        rw [hwre]
        linarith
      rw [div_one] at hstep
      linarith
    have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
    have hstep2 : ‖w‖ * (((lineTruncation t : ℕ) : ℝ) ^ (-w.re) / w.re)
        ≤ (2 + t) * (1 / ((lineTruncation t : ℕ) : ℝ)) := by
      have h1 : ‖w‖ * (((lineTruncation t : ℕ) : ℝ) ^ (-w.re) / w.re)
          ≤ ‖w‖ * (1 / ((lineTruncation t : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hwnn
      have h2 : ‖w‖ * (1 / ((lineTruncation t : ℕ) : ℝ))
          ≤ (2 + t) * (1 / ((lineTruncation t : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hnormw (by positivity)
      linarith
    have hlarge : (2 + t) * (1 / ((lineTruncation t : ℕ) : ℝ)) ≤ 30 := by
      have hcubeLow : (t / (8 * Real.pi)) ^ (3 : ℕ) - 1 ≤ ((lineTruncation t : ℕ) : ℝ) :=
        cube_sub_one_le_lineTruncation ht8
      have hπd : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      have ht16' : (50 : ℝ) ≤ t := by nlinarith [hπd]
      have hpow : ((t / (8 * Real.pi)) ^ (3 : ℕ)) = (t / (8 * Real.pi)) * (t / (8 * Real.pi))
          * (t / (8 * Real.pi)) := by ring
      have hbig : 2 + t ≤ 30 * ((t / (8 * Real.pi)) ^ (3 : ℕ) - 1) := by
        rw [hpow]
        have hq : (2 : ℝ) ≤ t / (8 * Real.pi) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [hπd]
        have hπhi : Real.pi < 3.15 := by
          have := Real.pi_lt_315
          linarith
        have hlin : t = 8 * Real.pi * (t / (8 * Real.pi)) := by
          field_simp
        have hcubelow : 4 * (t / (8 * Real.pi))
            ≤ t / (8 * Real.pi) * (t / (8 * Real.pi)) * (t / (8 * Real.pi)) := by
          nlinarith [hq]
        nlinarith [hq, hπhi, hlin, hcubelow]
      rw [mul_one_div, div_le_iff₀ hNpos]
      nlinarith [hbig, hcubeLow, hNpos]
    linarith
  rw [hwdef] at hbase
  rw [← hwdef]
  linarith [hbase, hhead, htail1, htail2]

end RHTower.Sieve
