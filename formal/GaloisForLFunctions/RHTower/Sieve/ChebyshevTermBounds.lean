import GaloisForLFunctions.RHTower.Sieve.ChebyshevSavingFactors
import GaloisForLFunctions.RHTower.Sieve.ChebyshevMassBound

/-!
# The error terms at the balanced parameters

Each term of the contour bound is a constant times a power of `t = (log N)^{1/10}` times `N` times
one of the two decaying factors.  The three ingredients are:

* the right-edge decay constant divided by any positive power of the truncation height is at most
  `81C·N·G` — the height's exponent `1` already beats the constant's growth `A`;
* the bracket shared by the two left-edge terms is at most `(8 + 54C)·N·E`;
* the regular part's bound is at most `M₀ + 2240t⁹/A + 1/9`.

Everything else is arithmetic.
-/

namespace RHTower.Sieve

open RHTower GaloisForLFunctions.HTGeometry

/-- **The right-edge decay constant against any power of the height.** -/
theorem decay_right_div_height_le {N Cj : ℝ} (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hCj : 0 ≤ Cj)
    {k : ℕ} (hk : 1 ≤ k) :
    (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        / chebHeight N ^ k
      ≤ 81 * Cj * N * savingG N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have ht0 : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
  have hd := decay_right_le hN hL hCj
  have hheight : chebHeight N ^ k = Real.exp ((k : ℝ) * (Real.log N) ^ ((1 : ℝ) / 10)) := by
    rw [chebHeight, ← Real.exp_nat_mul]
  have hpos : (0 : ℝ) < Real.exp ((k : ℝ) * (Real.log N) ^ ((1 : ℝ) / 10)) := Real.exp_pos _
  rw [hheight]
  have hstep : (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        / Real.exp ((k : ℝ) * (Real.log N) ^ ((1 : ℝ) / 10))
      ≤ (81 * Cj * N * (Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
          * Real.exp (zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10))))
        / Real.exp ((k : ℝ) * (Real.log N) ^ ((1 : ℝ) / 10)) := by
    gcongr
  refine le_trans hstep ?_
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp : (Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
        * Real.exp (zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)))
        / Real.exp ((k : ℝ) * (Real.log N) ^ ((1 : ℝ) / 10))
      ≤ savingG N := by
    rw [savingG, div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    have : (1 : ℝ) * (Real.log N) ^ ((1 : ℝ) / 10)
        ≤ (k : ℝ) * (Real.log N) ^ ((1 : ℝ) / 10) :=
      mul_le_mul_of_nonneg_right hk1 ht0
    nlinarith [this]
  have hcoef : (0 : ℝ) ≤ 81 * Cj * N := by positivity
  calc (81 * Cj * N * (Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
          * Real.exp (zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10))))
        / Real.exp ((k : ℝ) * (Real.log N) ^ ((1 : ℝ) / 10))
      = 81 * Cj * N * ((Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
          * Real.exp (zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)))
          / Real.exp ((k : ℝ) * (Real.log N) ^ ((1 : ℝ) / 10))) := by
        rw [mul_div_assoc]
    _ ≤ 81 * Cj * N * savingG N := mul_le_mul_of_nonneg_left hexp hcoef

/-- **The bracket shared by the two left-edge terms.** -/
theorem bracket_le {N Cj : ℝ} (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hCj : 0 ≤ Cj) :
    2 * ((N + chebWidth N) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
          / (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        + 2 * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
          * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
      ≤ (8 + 54 * Cj) * N * savingE N := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) < chebWidth N := chebWidth_pos hN0
  have hHle : chebWidth N ≤ N := chebWidth_le (by linarith) hN0
  have hpow9 : (1 : ℝ) ≤ (Real.log N) ^ ((9 : ℝ) / 10) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL (by norm_num : (0 : ℝ) ≤ 9 / 10)
    rwa [Real.one_rpow] at h
  have hw0 : (0 : ℝ) < zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) := by positivity
  have hwhalf : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have := zetaLowerA_le_half
    linarith
  have hden : (1 : ℝ) / 2 ≤ 1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) := by linarith
  have hexpu : (1 : ℝ) ≤ Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)) := by
    refine Real.one_le_exp ?_
    have : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 20) := Real.rpow_nonneg (by linarith) _
    linarith
  have hsav := rpow_left_le_saving (x := N) (Y := N + chebWidth N) (by linarith) hN0 (by linarith)
  have hE : Real.exp (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10))) ≤ savingE N := by
    rw [savingE]
    nlinarith [Real.exp_pos (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10))), hexpu]
  have hfirst : (N + chebWidth N) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
      ≤ 2 * N * savingE N := by
    refine le_trans hsav ?_
    have h1 : (N + chebWidth N)
        * Real.exp (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)))
        ≤ (2 * N) * Real.exp (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10))) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    have h2 : (2 * N) * Real.exp (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)))
        ≤ (2 * N) * savingE N := mul_le_mul_of_nonneg_left hE (by linarith)
    linarith
  have hpow0 : (0 : ℝ) ≤ (N + chebWidth N)
      ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) :=
    Real.rpow_nonneg (by linarith) _
  have hdiv : (N + chebWidth N) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
        / (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
      ≤ 2 * (2 * N * savingE N) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hfirst, hden, savingE_pos N, hN0]
  have hsecond := decay_left_le hN (by linarith) hCj
  have hsecond' : Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
      ≤ 27 * Cj * N * savingE N := by
    rw [savingE]
    exact hsecond
  nlinarith [hdiv, hsecond', savingE_pos N, hN0]

/-- **The regular part's bound, split.** -/
theorem regBound_le {N M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hL : 1 ≤ Real.log N) :
    max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9)
      ≤ M₀ + (2240 / zetaLowerA * ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 + 1 / 9) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hrw : (Real.log N) ^ ((9 : ℝ) / 10) = ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 :=
    rpow_nine_tenths_eq (by linarith)
  rw [hrw]
  have hpos : (0 : ℝ) ≤ 2240 / zetaLowerA * ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 + 1 / 9 := by
    have : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
    positivity
  exact max_le (by linarith) (by linarith)

end RHTower.Sieve
