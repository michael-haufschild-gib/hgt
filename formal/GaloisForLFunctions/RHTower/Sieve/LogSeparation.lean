import GaloisForLFunctions.RHTower.Sieve.DirichletDiagonal

/-!
# Logarithmic separation of distinct indices

`log x - log y ≥ (x - y)/x` for `0 < y ≤ x`, because `log(y/x) ≤ y/x - 1`.  Applied to consecutive
integers this bounds the logarithmic separation of two indices below by their ordinary separation
divided by the range:

`|log(m+1) - log(n+1)| ≥ |m - n| / N`   for `m, n < N`,

so the reciprocal logarithmic separations appearing in the mean square of a Dirichlet polynomial are
at most `N` times the reciprocal integer separations.

This is the elementary substitute for the Hilbert inequality at the frequencies `log n`: it costs a
factor `N`, which is exactly the size the mean value theorem's error term carries anyway.
-/

namespace RHTower.Sieve

open Finset

/-- **The logarithm separates points at least as well as the relative gap.** -/
theorem log_sub_ge {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    (x - y) / x ≤ Real.log x - Real.log y := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have hdiv : Real.log (y / x) = Real.log y - Real.log x := Real.log_div hy.ne' hx.ne'
  have hle : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [hdiv] at hle
  have hxy : y / x - 1 = -((x - y) / x) := by
    field_simp
    ring
  rw [hxy] at hle
  linarith

/-- Distinct positive integers bounded by `R` have logarithms separated by at least `1 / R`.
This form is useful when frequencies are logarithms of integer products rather than consecutive
indices. -/
theorem one_div_nat_upper_le_abs_log_sub
    {a b R : ℕ} (ha : 0 < a) (hb : 0 < b) (haR : a ≤ R) (hbR : b ≤ R)
    (hab : a ≠ b) :
    1 / (R : ℝ) ≤ |Real.log (a : ℝ) - Real.log (b : ℝ)| := by
  have hR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast lt_of_lt_of_le ha haR
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · have habSucc : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hablt
    have hgap : (1 : ℝ) ≤ (b : ℝ) - (a : ℝ) := by linarith
    have habLe : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hablt.le
    have hlog := log_sub_ge ha' habLe
    have hfrac : 1 / (R : ℝ) ≤ ((b : ℝ) - (a : ℝ)) / (b : ℝ) := by
      rw [div_le_div_iff₀ hR hb']
      have hbR' : (b : ℝ) ≤ (R : ℝ) := by exact_mod_cast hbR
      nlinarith
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha' habLe))]
    linarith
  · have hbaSucc : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hbalt
    have hgap : (1 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by linarith
    have hbaLe : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hbalt.le
    have hlog := log_sub_ge hb' hbaLe
    have hfrac : 1 / (R : ℝ) ≤ ((a : ℝ) - (b : ℝ)) / (a : ℝ) := by
      rw [div_le_div_iff₀ hR ha']
      have haR' : (a : ℝ) ≤ (R : ℝ) := by exact_mod_cast haR
      nlinarith
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb' hbaLe))]
    linarith

/-- **Logarithmic separation of distinct indices.** -/
theorem abs_log_succ_sub_ge {m n N : ℕ} (hm : m < N) (hn : n < N) :
    |(m : ℝ) - (n : ℝ)| / (N : ℝ)
      ≤ |Real.log ((m : ℝ) + 1) - Real.log ((n : ℝ) + 1)| := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have key : ∀ i j : ℕ, j ≤ i → i < N →
      ((i : ℝ) - (j : ℝ)) / (N : ℝ) ≤ Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1) := by
    intro i j hji hiN
    have hjR : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
    have hy : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hyx : (j : ℝ) + 1 ≤ (i : ℝ) + 1 := by linarith
    have hbase := log_sub_ge hy hyx
    have hiNR : (i : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hiN
    have hipos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hstep : ((i : ℝ) - (j : ℝ)) / (N : ℝ)
        ≤ (((i : ℝ) + 1) - ((j : ℝ) + 1)) / ((i : ℝ) + 1) := by
      rw [div_le_div_iff₀ hNR hipos]
      nlinarith [hjR, hiNR, hipos]
    linarith
  rcases le_total (n : ℕ) (m : ℕ) with hnm | hmn
  · have h := key m n hnm hm
    have habs1 : |(m : ℝ) - (n : ℝ)| = (m : ℝ) - (n : ℝ) := by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      rw [abs_of_nonneg (by linarith)]
    have habs2 : Real.log ((m : ℝ) + 1) - Real.log ((n : ℝ) + 1)
        ≤ |Real.log ((m : ℝ) + 1) - Real.log ((n : ℝ) + 1)| := le_abs_self _
    rw [habs1]
    linarith
  · have h := key n m hmn hn
    have habs1 : |(m : ℝ) - (n : ℝ)| = (n : ℝ) - (m : ℝ) := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      rw [abs_of_nonpos (by linarith)]
      ring
    have habs2 : Real.log ((n : ℝ) + 1) - Real.log ((m : ℝ) + 1)
        ≤ |Real.log ((m : ℝ) + 1) - Real.log ((n : ℝ) + 1)| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    rw [habs1]
    linarith

/-- **Reciprocal logarithmic separations cost a factor `N`.** -/
theorem two_div_abs_log_le {m n N : ℕ} (hm : m < N) (hn : n < N) (h : m ≠ n) :
    2 / |Real.log ((m : ℝ) + 1) - Real.log ((n : ℝ) + 1)|
      ≤ 2 * (N : ℝ) / |(m : ℝ) - (n : ℝ)| := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hgap : (0 : ℝ) < |(m : ℝ) - (n : ℝ)| := by
    rw [abs_pos, sub_ne_zero]
    intro hcon
    exact h (by exact_mod_cast hcon)
  have hlow := abs_log_succ_sub_ge hm hn
  have hpos : (0 : ℝ) < |(m : ℝ) - (n : ℝ)| / (N : ℝ) := by positivity
  have hlogpos : (0 : ℝ) < |Real.log ((m : ℝ) + 1) - Real.log ((n : ℝ) + 1)| :=
    lt_of_lt_of_le hpos hlow
  rw [div_le_div_iff₀ hlogpos hgap]
  have hmul : |(m : ℝ) - (n : ℝ)| ≤ (N : ℝ) * |Real.log ((m : ℝ) + 1) - Real.log ((n : ℝ) + 1)| := by
    rw [div_le_iff₀ hNR] at hlow
    linarith [hlow]
  nlinarith [hmul, hlogpos, hNR]

end RHTower.Sieve
