import GaloisForLFunctions.RHTower.Sieve.MoebiusKappaTwoTerms
import GaloisForLFunctions.RHTower.Sieve.MoebiusContourKappaTwoRatio

/-!
# The smoothed Möbius sum at the balanced parameter

Choosing `K = contourParamTwo (N+H+1)` in the width-`log^{-2}` contour bound makes every one of the
four edges of size

```text
(N+H+1) · (log(N+H+1))^{2/3} · exp( -(log(N+H+1))^{1/3} / 18 ),
```

the truncation height absorbing the growth of the right line and the rectangle width cancelling the
`log²K` of the horizontal edges.  The coefficient is a polynomial in the smoothing ratio `L = N/H`
and in nothing else.

The exponent `1/3` is the saving the exponent-one zero-free region supports; the exponent-nine
region gives `1/10` by the same argument.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- The right line's coefficient against the common majorant. -/
theorem majorant_right_le {R A Z E s e : ℝ} (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hE : 0 ≤ E)
    (hR : R ≤ 10 * e * s ^ 2) :
    8 * (R * A * Z * E) ≤ 80 * e * A * (Z * s ^ 2 * E) := by
  have hAZE : (0 : ℝ) ≤ A * (Z * E) := mul_nonneg hA (mul_nonneg hZ hE)
  have h := mul_le_mul_of_nonneg_right hR hAZE
  linarith [h]

/-- A horizontal edge's coefficient against the common majorant. -/
theorem majorant_horizontal_le {M B Z E s : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hE : 0 ≤ E) (hs : 1 ≤ s ^ 2) :
    16 * (M * B * Z * E) ≤ 16 * M * B * (Z * s ^ 2 * E) := by
  have hX : (0 : ℝ) ≤ M * B * Z * E := mul_nonneg (mul_nonneg (mul_nonneg hM hB) hZ) hE
  have h := mul_nonneg hX (by linarith : (0 : ℝ) ≤ s ^ 2 - 1)
  linarith [h]

/-- The left edge's coefficient against the common majorant. -/
theorem majorant_left_le {M W A Y Z E s : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hY : 0 ≤ Y)
    (hE : 0 ≤ E) (hYZ : Y ≤ Z) (hW : W ≤ 9 * s ^ 2) :
    M * W * (4 * (Y * E) + 2 * (A * (Z * E))) ≤ 9 * M * (4 + 2 * A) * (Z * s ^ 2 * E) := by
  have hZ0 : (0 : ℝ) ≤ Z := le_trans hY hYZ
  have hinner : 4 * (Y * E) + 2 * (A * (Z * E)) ≤ 4 * (Z * E) + 2 * (A * (Z * E)) := by
    have := mul_le_mul_of_nonneg_right hYZ hE
    linarith
  have hinner0 : (0 : ℝ) ≤ 4 * (Y * E) + 2 * (A * (Z * E)) := by
    have h1 := mul_nonneg hY hE
    have h2 := mul_nonneg hA (mul_nonneg hZ0 hE)
    linarith
  have hMW : M * W ≤ M * (9 * s ^ 2) := mul_le_mul_of_nonneg_left hW hM
  have hMW0 : (0 : ℝ) ≤ M * (9 * s ^ 2) := mul_nonneg hM (by positivity)
  have hstep := mul_le_mul hMW hinner hinner0 hMW0
  have hring : M * (9 * s ^ 2) * (4 * (Z * E) + 2 * (A * (Z * E)))
      = 9 * M * (4 + 2 * A) * (Z * s ^ 2 * E) := by ring
  linarith [hstep, hring]

/-- The coefficient of the rate: a polynomial in the smoothing ratio. -/
noncomputable def coeffMajorantTwo (C C' Ms L : ℝ) : ℝ :=
  80 * Real.exp (22 / 4) * (C * (L + 2) ^ 2)
    + 16 * Ms * (C' * (L + 2))
    + 9 * Ms * (4 + 2 * (C * (L + 2) ^ 2))

/-- **The smoothed Möbius sum, with an explicit saving of exponent `1/3`.** -/
theorem exists_norm_tsum_moebius_smoothWeight_kappa_two_rate :
    ∃ (C C' Ms : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ Ms ∧
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → 2 ≤ N + H →
        1 ≤ Real.log (N + H + 1) → K₀ ≤ contourParamTwo (N + H + 1) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ coeffMajorantTwo C C' Ms L
            * ((N + H + 1) * ((Real.log (N + H + 1)) ^ ((1 : ℝ) / 3)) ^ 2
                * Real.exp (-((Real.log (N + H + 1)) ^ ((1 : ℝ) / 3) / 18))) := by
  obtain ⟨C, C', Ms, K₀, hC, hC', hMs, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_le_kappa_two_ratio
  refine ⟨C, C', Ms, K₀, hC, hC', hMs, fun N H L hN hH1 hL hY2 hlogZ hK₀ => ?_⟩
  have hH : (0 : ℝ) < H := by linarith
  have hbase := hmain N H L hN hH1 hL (contourParamTwo (N + H + 1)) hK₀
  rw [truncHeight, rightAbscissaTwo_sub_leftAbscissaTwo] at hbase
  rw [coeffMajorantTwo]
  have hZ0 : (0 : ℝ) < N + H + 1 := by linarith
  have hY0 : (0 : ℝ) ≤ N + H := by linarith
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (div_pos hN hH) hL
  set A : ℝ := C * (L + 2) ^ 2 with hAdef
  set B : ℝ := C' * (L + 2) with hBdef
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  have hB0 : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  set s : ℝ := (Real.log (N + H + 1)) ^ ((1 : ℝ) / 3) with hsdef
  have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Real.one_le_rpow hlogZ (by norm_num)
  have hssq : (1 : ℝ) ≤ s ^ 2 := by nlinarith
  have hK7 : (7 : ℝ) ≤ ((contourParamTwo (N + H + 1) : ℕ) : ℝ) :=
    seven_le_contourParamTwo hlogZ
  have hΛlow : 2 * s ≤ Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) :=
    le_log_contourParamTwo (N + H + 1)
  have hΛhi : Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) ≤ 3 * s :=
    log_contourParamTwo_le_three hlogZ
  have hΛ0 : (0 : ℝ) < Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) := by linarith
  have hΛsq : Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) ^ 2 ≤ 9 * s ^ 2 := by nlinarith
  have hΛsq4 : (4 : ℝ) ≤ Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) ^ 2 := by nlinarith
  have hΛsq0 : (0 : ℝ) < Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) ^ 2 := by linarith
  set E : ℝ := Real.exp (-(s / 18)) with hEdef
  have hE0 : (0 : ℝ) < E := by rw [hEdef]; exact Real.exp_pos _
  -- the three powers at the balanced parameter
  have hZd : (N + H + 1) ^ rightAbscissaTwo (contourParamTwo (N + H + 1))
      ≤ (N + H + 1) * E * ((contourParamTwo (N + H + 1) : ℕ) : ℝ) := by
    refine le_trans (rpow_rightAbscissaTwo_le hZ0 hlogZ) ?_
    have hexp : Real.exp (-(7 / 4) * s) ≤ E := by
      rw [hEdef]; exact Real.exp_le_exp.mpr (by linarith)
    have hfac : (0 : ℝ) ≤ (N + H + 1) * ((contourParamTwo (N + H + 1) : ℕ) : ℝ) :=
      mul_nonneg hZ0.le (by linarith)
    have h := mul_le_mul_of_nonneg_left hexp hfac
    linarith [h]
  have hZc : (N + H + 1) ^ leftAbscissaTwo (contourParamTwo (N + H + 1))
      ≤ (N + H + 1) * E := by
    refine le_trans (rpow_leftAbscissaTwo_le hZ0 hlogZ) ?_
    have hexp : Real.exp (-(s / 9)) ≤ E := by
      rw [hEdef]; exact Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul_of_nonneg_left hexp hZ0.le
  have hYc : (N + H) ^ leftAbscissaTwo (contourParamTwo (N + H + 1)) ≤ (N + H) * E :=
    rpow_leftAbscissaTwo_le_shift hY2 hlogZ
  have hc34 : (3 : ℝ) / 4 ≤ leftAbscissaTwo (contourParamTwo (N + H + 1)) := by
    rw [leftAbscissaTwo]
    have : 1 / Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) ^ 2 ≤ 1 / 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛsq4
    linarith
  -- the four edges
  have hT1 := contour_right_term_le (R := invZetaRightBoundTwo (contourParamTwo (N + H + 1)))
    (A := A) (invZetaRightBoundTwo_nonneg _) hA0 hZ0.le hE0.le hK7 hZd
  have hT2 := contour_horizontal_term_le (M := Ms)
    (W := Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) ^ 2) (B := B)
    hMs hB0 hZ0.le hE0.le hK7 hΛsq0 hZd
  have hT4 := contour_left_term_le (M := Ms)
    (W := Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) ^ 2) (A := A)
    hMs hΛsq0.le hA0 hc34 hY0 hE0.le hYc hZc
  -- the coefficient of the right line
  have hRbound : invZetaRightBoundTwo (contourParamTwo (N + H + 1))
      ≤ 10 * Real.exp (22 / 4) * s ^ 2 := by
    rw [invZetaRightBoundTwo]
    have hstep : (1 : ℝ) + Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) ^ 2 ≤ 10 * s ^ 2 := by
      linarith
    have h := mul_le_mul_of_nonneg_left hstep (Real.exp_pos (22 / 4 : ℝ)).le
    linarith [h]
  have hS1 := majorant_right_le (R := invZetaRightBoundTwo (contourParamTwo (N + H + 1)))
    (A := A) (Z := N + H + 1) (E := E) (s := s) (e := Real.exp (22 / 4))
    hA0 hZ0.le hE0.le hRbound
  have hS2 := majorant_horizontal_le (M := Ms) (B := B) (Z := N + H + 1) (E := E) (s := s)
    hMs hB0 hZ0.le hE0.le hssq
  have hS4 := majorant_left_le (M := Ms)
    (W := Real.log ((contourParamTwo (N + H + 1) : ℕ) : ℝ) ^ 2) (A := A)
    (Y := N + H) (Z := N + H + 1) (E := E) (s := s) hMs hA0 hY0 hE0.le (by linarith) hΛsq
  linarith [hbase, hT1, hT2, hT4, hS1, hS2, hS4]

end RHTower.Sieve
