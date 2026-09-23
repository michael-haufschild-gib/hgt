import GaloisForLFunctions.RHTower.Sieve.DyadicMeanSquareGallagher
import GaloisForLFunctions.RHTower.Sieve.MRFibreReduction

/-!
# Harmonic-to-ordinary window transfer for Menon's normalization

Menon's frequency argument estimates the harmonic Möbius polynomial, whereas the reciprocal-marker
card consumes ordinary Möbius sums on literal integer windows.  Abel summation on one window gives
an exact identity: multiplying the harmonic coefficients by the left endpoint recovers the
ordinary sum up to a linearly weighted endpoint error.  Since `|μ| ≤ 1`, that error is at most
`L² / (z+1)`.

The terminal theorem sums this pointwise inequality over an unchanged integer-start range.  It
introduces no analytic hypothesis and retains the full endpoint error needed for the growing
reciprocal-marker schedule.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- Real harmonic Möbius coefficient `μ(n) / n`. -/
def harmonicMoebiusR (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ) / (n : ℝ)

/-- Exact Abel decomposition of one ordinary Möbius window through its harmonic counterpart. -/
theorem sum_moebius_eq_start_mul_harmonic_add_error (z l : ℕ) :
    (∑ n ∈ Finset.Ioc z (z + l), ((μ n : ℤ) : ℝ)) =
      (z : ℝ) * (∑ n ∈ Finset.Ioc z (z + l), harmonicMoebiusR n) +
        ∑ n ∈ Finset.Ioc z (z + l),
          ((n - z : ℕ) : ℝ) * harmonicMoebiusR n := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [harmonicMoebiusR]
  have hnz : z < n := (Finset.mem_Ioc.1 hn).1
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le z) hnz))
  rw [Nat.cast_sub (Nat.le_of_lt hnz)]
  field_simp
  ring

/-- The literal Abel endpoint error is at most `l² / (z+1)`. -/
theorem abs_harmonicMoebius_window_error_le (z l : ℕ) :
    |∑ n ∈ Finset.Ioc z (z + l),
        ((n - z : ℕ) : ℝ) * harmonicMoebiusR n| ≤
      (l : ℝ) ^ (2 : ℕ) / ((z + 1 : ℕ) : ℝ) := by
  calc
    |∑ n ∈ Finset.Ioc z (z + l),
        ((n - z : ℕ) : ℝ) * harmonicMoebiusR n|
        ≤ ∑ n ∈ Finset.Ioc z (z + l),
            |((n - z : ℕ) : ℝ) * harmonicMoebiusR n| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ioc z (z + l),
          (l : ℝ) / ((z + 1 : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hnz : z < n := (Finset.mem_Ioc.1 hn).1
      have hnle : n ≤ z + l := (Finset.mem_Ioc.1 hn).2
      have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le z) hnz
      have hmu := abs_moebius_real_le_one n
      have hdiff : n - z ≤ l := by omega
      have hden : z + 1 ≤ n := by omega
      rw [abs_mul, harmonicMoebiusR, abs_div]
      rw [abs_of_nonneg (by positivity : 0 ≤ ((n - z : ℕ) : ℝ))]
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hzR : (0 : ℝ) < ((z + 1 : ℕ) : ℝ) := by positivity
      have hnum : (((n - z : ℕ) : ℝ)) * |((μ n : ℤ) : ℝ)| ≤ (l : ℝ) := by
        have hdiffR : (((n - z : ℕ) : ℝ)) ≤ (l : ℝ) := by exact_mod_cast hdiff
        have hdiff0 : (0 : ℝ) ≤ ((n - z : ℕ) : ℝ) := by positivity
        nlinarith
      calc
        ((n - z : ℕ) : ℝ) * (|((μ n : ℤ) : ℝ)| / |(n : ℝ)|)
            = ((n - z : ℕ) : ℝ) * |((μ n : ℤ) : ℝ)| / (n : ℝ) := by
              rw [abs_of_pos hnR]
              ring
        _ ≤ (l : ℝ) / (n : ℝ) := div_le_div_of_nonneg_right hnum hnR.le
        _ ≤ (l : ℝ) / ((z + 1 : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_left (by positivity) hzR (by exact_mod_cast hden)
    _ = (l : ℝ) ^ (2 : ℕ) / ((z + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Ioc z (z + l)).card = l := by simp
      rw [hcard]
      push_cast
      ring

/-- Pointwise square transfer on one literal integer window. -/
theorem fixedWindowSq_moebius_le_harmonic (l z : ℕ) (hl : 1 ≤ l) :
    fixedWindowSq (fun n => ((μ n : ℤ) : ℝ)) l z ≤
      2 * (z : ℝ) ^ (2 : ℕ) * fixedWindowSq harmonicMoebiusR l z +
        2 * ((l : ℝ) ^ (2 : ℕ) / ((z + 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
  rw [fixedWindowSq_eq_sq_sum (fun n => ((μ n : ℤ) : ℝ)) hl z,
    fixedWindowSq_eq_sq_sum harmonicMoebiusR hl z]
  rw [sum_moebius_eq_start_mul_harmonic_add_error]
  have herr := abs_harmonicMoebius_window_error_le z l
  have hsquare := pow_le_pow_left₀ (abs_nonneg _) herr 2
  rw [sq_abs] at hsquare
  nlinarith [sq_nonneg ((z : ℝ) *
    (∑ n ∈ Finset.Ioc z (z + l), harmonicMoebiusR n) -
    ∑ n ∈ Finset.Ioc z (z + l), ((n - z : ℕ) : ℝ) * harmonicMoebiusR n)]

/-- Ordinary Möbius windows are controlled by harmonic Möbius windows on the same literal
integer-start range, with the exact endpoint error retained. -/
theorem dyadicMeanSquare_moebius_le_harmonic
    {l A B : ℕ} (hl : 1 ≤ l) :
    dyadicMeanSquare (fun n => ((μ n : ℤ) : ℝ)) l A B ≤
      2 * (B : ℝ) ^ (2 : ℕ) * dyadicMeanSquare harmonicMoebiusR l A B +
        2 * ((Finset.Icc A B).card : ℝ) *
          ((l : ℝ) ^ (2 : ℕ) / ((A + 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
  rw [dyadicMeanSquare, dyadicMeanSquare]
  calc
    ∑ z ∈ Finset.Icc A B,
        fixedWindowSq (fun n => ((μ n : ℤ) : ℝ)) l z
      ≤ ∑ z ∈ Finset.Icc A B,
          (2 * (B : ℝ) ^ (2 : ℕ) * fixedWindowSq harmonicMoebiusR l z +
            2 * ((l : ℝ) ^ (2 : ℕ) / ((A + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hzAB := Finset.mem_Icc.1 hz
        have hpoint := fixedWindowSq_moebius_le_harmonic l z hl
        have hzsq : (z : ℝ) ^ (2 : ℕ) ≤ (B : ℝ) ^ (2 : ℕ) := by
          exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hzAB.2) 2
        have hmain : 2 * (z : ℝ) ^ (2 : ℕ) * fixedWindowSq harmonicMoebiusR l z ≤
            2 * (B : ℝ) ^ (2 : ℕ) * fixedWindowSq harmonicMoebiusR l z := by
          have hF := fixedWindowSq_nonneg harmonicMoebiusR l z
          have hdiff : 0 ≤ (B : ℝ) ^ (2 : ℕ) - (z : ℝ) ^ (2 : ℕ) := by linarith
          nlinarith [mul_nonneg hdiff hF]
        have hden : ((A + 1 : ℕ) : ℝ) ≤ ((z + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_le_add_right hzAB.1 1
        have hquot : (l : ℝ) ^ (2 : ℕ) / ((z + 1 : ℕ) : ℝ) ≤
            (l : ℝ) ^ (2 : ℕ) / ((A + 1 : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        have hquot0 : 0 ≤ (l : ℝ) ^ (2 : ℕ) / ((z + 1 : ℕ) : ℝ) := by positivity
        have herr := pow_le_pow_left₀ hquot0 hquot 2
        nlinarith
    _ = 2 * (B : ℝ) ^ (2 : ℕ) *
          (∑ z ∈ Finset.Icc A B, fixedWindowSq harmonicMoebiusR l z) +
        2 * ((Finset.Icc A B).card : ℝ) *
          ((l : ℝ) ^ (2 : ℕ) / ((A + 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

end

end RHTower.Sieve
