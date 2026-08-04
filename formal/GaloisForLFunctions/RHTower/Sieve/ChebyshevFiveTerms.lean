import GaloisForLFunctions.RHTower.Sieve.ChebyshevTermBounds
import GaloisForLFunctions.RHTower.Sieve.ChebyshevAtChoice

/-!
# The error as five decaying terms

Collecting the term bounds, the whole contour error at the balanced parameters is at most

    a₀·N·E + a₉·t⁹·N·E + b₀·N·G + b₉·t⁹·N·G + b₁₈·t¹⁸·N·G,

with constants built from `C`, `M₀` and `A` alone.  Divided by `N`, every summand tends to `0`.

The powers of `t` are exactly the three places the strip's width appears: `w⁻¹ = t⁹/A` in the two
left-edge terms, `w⁻²` in the truncation error, and the regular part's own bound `2240t⁹/A`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction RHTower GaloisForLFunctions.HTGeometry

variable {N Cj M₀ : ℝ}

/-- **The tail term.** -/
theorem term_tail_le (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hCj : 0 ≤ Cj) :
    2 * ((8 / (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) ^ 2)
        * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
          * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))))
        / chebHeight N
      ≤ 1296 * Cj / zetaLowerA ^ 2 * (((Real.log N) ^ ((1 : ℝ) / 10)) ^ 18
          * (N * savingG N)) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hN0 : (0 : ℝ) < N := by linarith
  have htpos : (0 : ℝ) < (Real.log N) ^ ((1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hp : (Real.log N) ^ ((9 : ℝ) / 10) = ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 :=
    rpow_nine_tenths_eq (by linarith)
  have hdiv := decay_right_div_height_le (N := N) (Cj := Cj) hN hL hCj (k := 1) (le_refl 1)
  rw [pow_one] at hdiv
  have hrw : 2 * ((8 / (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) ^ 2)
        * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
          * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))))
        / chebHeight N
      = (2 * (8 / (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) ^ 2))
        * ((Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
          * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
          / chebHeight N) := by ring
  rw [hrw]
  refine le_trans (mul_le_mul_of_nonneg_left hdiv (by positivity)) (le_of_eq ?_)
  rw [hp]
  field_simp
  ring

/-- **The left-edge divided-difference term.** -/
theorem term_left_dslope_le (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hCj : 0 ≤ Cj) :
    (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))⁻¹
        * (2 * ((N + chebWidth N) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
              / (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
            + 2 * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
              * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))))
      ≤ (8 + 54 * Cj) / zetaLowerA * (((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9
          * (N * savingE N)) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hN0 : (0 : ℝ) < N := by linarith
  have htpos : (0 : ℝ) < (Real.log N) ^ ((1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hp : (Real.log N) ^ ((9 : ℝ) / 10) = ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 :=
    rpow_nine_tenths_eq (by linarith)
  refine le_trans (mul_le_mul_of_nonneg_left (bracket_le hN hL hCj) (by positivity))
    (le_of_eq ?_)
  rw [hp]
  field_simp

/-- **The horizontal divided-difference term.** -/
theorem term_horizontal_dslope_le (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hCj : 0 ≤ Cj) :
    2 * ((2 * (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        * (((Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
              * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
            / chebHeight N ^ (1 + 1)
          + ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖)
          / chebHeight N))
      ≤ (324 * Cj + 8) * (N * savingG N) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) < chebWidth N := chebWidth_pos hN0
  have hHle : chebWidth N ≤ N := chebWidth_le (by linarith) hN0
  have htpos : (0 : ℝ) < (Real.log N) ^ ((1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hpow9 : (1 : ℝ) ≤ (Real.log N) ^ ((9 : ℝ) / 10) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL (by norm_num : (0 : ℝ) ≤ 9 / 10)
    rwa [Real.one_rpow] at h
  have hw0 : (0 : ℝ) < zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) := by positivity
  have hwle : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hheight : chebHeight N = Real.exp ((Real.log N) ^ ((1 : ℝ) / 10)) := rfl
  have hT0 : (0 : ℝ) < chebHeight N := by rw [hheight]; exact Real.exp_pos _
  have hdiv3 := decay_right_div_height_le (N := N) (Cj := Cj) hN hL hCj (k := 3)
    (by norm_num)
  have hsplit : ((Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
            * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
          / chebHeight N ^ (1 + 1)
        + ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖)
        / chebHeight N
      = (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
            * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
          / chebHeight N ^ 3
        + ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖
          / chebHeight N := by
    rw [add_div, div_div, ← pow_succ]
  have hmass : ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖
      ≤ 2 * N := by
    refine le_trans (norm_mellin_smoothWeight_one_le hN0.le hH0) ?_
    linarith
  have hinvT : (chebHeight N)⁻¹ ≤ savingG N := by
    rw [hheight, ← Real.exp_neg, savingG]
    have hu : (0 : ℝ) ≤ Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)) := (Real.exp_pos _).le
    have hstep : Real.exp (-((Real.log N) ^ ((1 : ℝ) / 10)))
        ≤ Real.exp (-((1 - zetaLowerA) * (Real.log N) ^ ((1 : ℝ) / 10))) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [htpos, hA0]
    have hone : (1 : ℝ) ≤ Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)) := by
      refine Real.one_le_exp ?_
      have : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 20) := Real.rpow_nonneg (by linarith) _
      linarith
    nlinarith [Real.exp_pos (-((1 - zetaLowerA) * (Real.log N) ^ ((1 : ℝ) / 10))), hstep, hone]
  have hmassT : ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖
      / chebHeight N ≤ 2 * (N * savingG N) := by
    rw [div_eq_mul_inv]
    have h1 : ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖
        * (chebHeight N)⁻¹ ≤ (2 * N) * (chebHeight N)⁻¹ :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    have h2 : (2 * N) * (chebHeight N)⁻¹ ≤ (2 * N) * savingG N :=
      mul_le_mul_of_nonneg_left hinvT (by linarith)
    linarith
  rw [hsplit]
  have hinner : (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
          * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        / chebHeight N ^ 3
      + ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖ / chebHeight N
      ≤ 81 * Cj * N * savingG N + 2 * (N * savingG N) := by linarith
  have hinner0 : (0 : ℝ) ≤ (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
          * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        / chebHeight N ^ 3
      + ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖ / chebHeight N := by
    have h1 : (0 : ℝ) ≤ (N + chebWidth N + 1)
        ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) :=
      Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) ≤ ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖ :=
      norm_nonneg _
    positivity
  nlinarith [hinner, hinner0, hw0, hwle, savingG_pos N, hN0, hCj]

/-- **The left-edge regular term.** -/
theorem term_left_reg_le (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hCj : 0 ≤ Cj) (hM₀ : 0 ≤ M₀) :
    max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9)
        * (2 * ((N + chebWidth N) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
              / (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
            + 2 * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
              * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))))
      ≤ (M₀ + 1 / 9) * (8 + 54 * Cj) * (N * savingE N)
        + 2240 * (8 + 54 * Cj) / zetaLowerA * (((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9
            * (N * savingE N)) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hN0 : (0 : ℝ) < N := by linarith
  have htpos : (0 : ℝ) < (Real.log N) ^ ((1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hbr := bracket_le hN hL hCj
  have hbr0 : (0 : ℝ) ≤ 2 * ((N + chebWidth N) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
        / (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
      + 2 * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))) := by
    have hpow9 : (1 : ℝ) ≤ (Real.log N) ^ ((9 : ℝ) / 10) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL (by norm_num : (0 : ℝ) ≤ 9 / 10)
      rwa [Real.one_rpow] at h
    have hden : (0 : ℝ) < 1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) := by
      have hA1 : zetaLowerA ≤ 1 / 2 := zetaLowerA_le_half
      have : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      linarith
    have h1 : (0 : ℝ) ≤ (N + chebWidth N)
        ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) :=
      Real.rpow_nonneg (by have := chebWidth_pos hN0; linarith) _
    have h2 : (0 : ℝ) ≤ (N + chebWidth N + 1)
        ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) :=
      Real.rpow_nonneg (by have := chebWidth_pos hN0; linarith) _
    have hH0 : (0 : ℝ) < chebWidth N := chebWidth_pos hN0
    positivity
  have hM := regBound_le (N := N) hM₀ hL
  have hMt : max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9)
      * (2 * ((N + chebWidth N) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
            / (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
          + 2 * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
            * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))))
      ≤ (M₀ + (2240 / zetaLowerA * ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 + 1 / 9))
        * ((8 + 54 * Cj) * N * savingE N) := by
    refine mul_le_mul hM hbr hbr0 ?_
    have hpos : (0 : ℝ) ≤ 2240 / zetaLowerA * ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 + 1 / 9 := by
      positivity
    linarith
  refine le_trans hMt (le_of_eq ?_)
  field_simp
  ring

/-- **The horizontal regular term.** -/
theorem term_horizontal_reg_le (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hCj : 0 ≤ Cj)
    (hM₀ : 0 ≤ M₀) :
    2 * ((2 * (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        * (max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9)
          * ((Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
              * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
            / chebHeight N ^ (1 + 1))))
      ≤ 324 * Cj * (M₀ + 1 / 9) * (N * savingG N)
        + 324 * Cj * 2240 / zetaLowerA * (((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9
            * (N * savingG N)) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  have hN0 : (0 : ℝ) < N := by linarith
  have htpos : (0 : ℝ) < (Real.log N) ^ ((1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hpow9 : (1 : ℝ) ≤ (Real.log N) ^ ((9 : ℝ) / 10) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL (by norm_num : (0 : ℝ) ≤ 9 / 10)
    rwa [Real.one_rpow] at h
  have hw0 : (0 : ℝ) < zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) := by positivity
  have hwle : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hdiv2 := decay_right_div_height_le (N := N) (Cj := Cj) hN hL hCj (k := 2) (by norm_num)
  have hdiv2' : (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        / chebHeight N ^ (1 + 1) ≤ 81 * Cj * N * savingG N := by
    simpa using hdiv2
  have hdiv0 : (0 : ℝ) ≤ (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        / chebHeight N ^ (1 + 1) := by
    have hH0 : (0 : ℝ) < chebWidth N := chebWidth_pos hN0
    have h1 : (0 : ℝ) ≤ (N + chebWidth N + 1)
        ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) :=
      Real.rpow_nonneg (by linarith) _
    have hT0 : (0 : ℝ) < chebHeight N := Real.exp_pos _
    positivity
  have hM := regBound_le (N := N) hM₀ hL
  have hM0 : (0 : ℝ) ≤ max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9) :=
    le_trans hM₀ (le_max_left _ _)
  have hprod : max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9)
      * ((Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
          * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
        / chebHeight N ^ (1 + 1))
      ≤ (M₀ + (2240 / zetaLowerA * ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 + 1 / 9))
        * (81 * Cj * N * savingG N) := by
    refine mul_le_mul hM hdiv2' hdiv0 ?_
    have hpos : (0 : ℝ) ≤ 2240 / zetaLowerA * ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 + 1 / 9 := by
      positivity
    linarith
  have hprod0 : (0 : ℝ) ≤ (M₀ + (2240 / zetaLowerA * ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 + 1 / 9))
      * (81 * Cj * N * savingG N) := by
    have := savingG_pos N
    positivity
  have hfinal : 2 * ((2 * (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
      * (max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9)
        * ((Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
            * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
          / chebHeight N ^ (1 + 1))))
      ≤ 4 * ((M₀ + (2240 / zetaLowerA * ((Real.log N) ^ ((1 : ℝ) / 10)) ^ 9 + 1 / 9))
        * (81 * Cj * N * savingG N)) := by
    have hstep : max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9)
        * ((Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
            * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
          / chebHeight N ^ (1 + 1)) ≥ 0 := by positivity
    nlinarith [hprod, hstep, hw0, hwle, hprod0]
  refine le_trans hfinal (le_of_eq ?_)
  field_simp
  ring

end RHTower.Sieve
