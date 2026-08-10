import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodContourPlain
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodCoeff
import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneRate

/-!
# The smoothed Chebyshev sum at depth `A`

The exponent-one chain's balance, run at a contour shifted by `A/log T` and the height
`chebHeightLw A x = exp(2√(A log x))`.  The shape is unchanged; every occurrence of `log Z` becomes
`A log Z` and the saving exponent becomes `√(A log Z)/12`.

At `A = 1/40000` this recovers the exponent-one saving up to the constant; the point is that `A` is
free, so `A ≍ log log N` — which the Littlewood region permits — gives
`exp(-√(log N · log log N)/12)`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The smoothed Chebyshev sum at depth `A`.**  The saving is `exp(-√(A log Z)/12)`. -/
theorem exists_norm_tsum_vonMangoldt_littlewood_rate (A : ℝ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthLw A N) (n : ℝ) : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthLw A N) x : ℝ) : ℂ)) 1
              * (((2 * Real.arctan (chebHeightLw A (N + chebWidthLw A N + 1)
                      / (chebRightTwo (chebHeightLw A (N + chebWidthLw A N + 1)) - 1))
                    - 2 * Real.arctan (chebHeightLw A (N + chebWidthLw A N + 1)
                      / (chebLeftLw A (chebHeightLw A (N + chebWidthLw A N + 1)) - 1)) : ℝ)) : ℂ)‖
        ≤ B * (N + chebWidthLw A N + 1)
            * Real.exp (-(1 / 12
                * Real.sqrt (A * Real.log (N + chebWidthLw A N + 1)))) := by
  have hA0 : (0 : ℝ) < A := by linarith
  obtain ⟨Cm, Cr, L₀, hCm, hCr0, hL₀8, hmain⟩ :=
    exists_norm_tsum_vonMangoldt_littlewood_plain A hA0
  refine ⟨250000 * (1 + Cr) * (3 + 27 * Cm) * (4 * (4 / ((1 : ℝ) / 12) ^ 2)), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 1 + Cr := by linarith
    have h2 : (0 : ℝ) ≤ 3 + 27 * Cm := by linarith
    have h3 : (4 : ℝ) * (4 / ((1 : ℝ) / 12) ^ 2) = 2304 := by norm_num
    rw [h3]
    nlinarith [h1, h2]
  filter_upwards [eventually_cheb_littlewood_conditions A L₀ hA0] with N hcond
  obtain ⟨hN0, hH1, hHN, hZ16, hZ16A, hTL⟩ := hcond
  set H : ℝ := chebWidthLw A N with hHdef
  have hH0 : (0 : ℝ) < H := by linarith
  have hZ0 : (0 : ℝ) < N + H + 1 := by linarith
  have hY0 : (0 : ℝ) ≤ N + H := by linarith
  have hY1 : (1 : ℝ) ≤ N + H := by linarith
  have hT1 : (1 : ℝ) ≤ chebHeightLw A (N + H + 1) := one_le_chebHeightLw A _
  have hT8 : (8 : ℝ) ≤ Real.log (chebHeightLw A (N + H + 1)) := eight_le_log_chebHeightLw hZ16
  have hlogZ0 : (0 : ℝ) < Real.log (N + H + 1) := by linarith
  have hAZ : A ≤ Real.log (N + H + 1) := by linarith
  have hTA8 : 8 * A ≤ Real.log (chebHeightLw A (N + H + 1)) :=
    eight_mul_le_log_chebHeightLw hA0 hZ16A
  have hAZ0 : (0 : ℝ) ≤ A * Real.log (N + H + 1) := by positivity
  have hbase := hmain N H hN0 hH0 (chebHeightLw A (N + H + 1)) hT1 hTL
  -- the three edge powers
  have hZd := rpow_chebRightTwo_at_lw_le hA hZ0 hlogZ0
  have hZc := rpow_chebLeftLw_at_le hA0 hZ0 hlogZ0
  have hYc := rpow_chebLeftLw_at_shift hA0 hY1 hAZ
  have hZd0 : (0 : ℝ) ≤ (N + H + 1) ^ chebRightTwo (chebHeightLw A (N + H + 1)) :=
    Real.rpow_nonneg hZ0.le _
  -- the remaining shape data
  have hE0 : (0 : ℝ) ≤ chebFactorLw A (N + H + 1) := (chebFactorLw_pos A _).le
  have hMm := norm_mellin_smoothWeight_one_le hN0.le hH0
  have hTE := one_div_chebHeightLw_le_factor A (N + H + 1)
  have hc := half_le_chebLeftLw hT8 (by linarith : 2 * A ≤ Real.log (chebHeightLw A (N + H + 1)))
  have hS0 : (0 : ℝ) ≤ ∑' n : ℕ, (vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(chebRightTwo (chebHeightLw A (N + H + 1)))) :=
    tsum_nonneg fun n =>
      mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hW0 : (0 : ℝ) ≤ Cm / H ^ 2 * (N + H + 1) ^ 2 :=
    mul_nonneg (div_nonneg hCm (by positivity)) (by positivity)
  -- the five terms collapse to a shape
  have hshaped := cheb_kappa_one_terms_shaped
    (S := ∑' n : ℕ, (vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(chebRightTwo (chebHeightLw A (N + H + 1)))))
    (W := Cm / H ^ 2 * (N + H + 1) ^ 2) (Y := N + H) (Z := N + H + 1)
    (E := chebFactorLw A (N + H + 1)) (T := chebHeightLw A (N + H + 1))
    (Mm := ‖mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖)
    (ci := (1 - chebLeftLw A (chebHeightLw A (N + H + 1)))⁻¹)
    (wd := chebRightTwo (chebHeightLw A (N + H + 1)) - chebLeftLw A (chebHeightLw A (N + H + 1)))
    (M := Cr * Real.log (chebHeightLw A (N + H + 1)) ^ 2)
    (c := chebLeftLw A (chebHeightLw A (N + H + 1)))
    hS0 hW0
    (by rw [one_sub_chebLeftLw_inv]; exact div_nonneg (by linarith) hA0.le)
    (le_of_lt (chebRightTwo_sub_chebLeftLw_pos hA0 hT8))
    (by positivity)
    hT1 hE0 hY0 (by linarith) hc hMm hTE hZd0 hZd hZc hYc
  -- the coefficient
  have hcoeff := cheb_littlewood_coeff_le (A := A)
    (S := ∑' n : ℕ, (vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(chebRightTwo (chebHeightLw A (N + H + 1)))))
    (W := Cm / H ^ 2 * (N + H + 1) ^ 2)
    (ci := (1 - chebLeftLw A (chebHeightLw A (N + H + 1)))⁻¹)
    (wd := chebRightTwo (chebHeightLw A (N + H + 1)) - chebLeftLw A (chebHeightLw A (N + H + 1)))
    (M := Cr * Real.log (chebHeightLw A (N + H + 1)) ^ 2) (Cr := Cr)
    (Lg := Real.log (chebHeightLw A (N + H + 1)))
    (Wb := Cm * (9 * Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6)))
    hT8 hW0
    (width_price_le_gen hH1 hN0.le (le_of_eq (div_chebWidthLw hN0)) hCm (sq_chebRatioLw_le A N))
    hCr0.le (tsum_vonMangoldt_chebRightTwo_le hT8) hA hTA8
    (one_sub_chebLeftLw_inv A _)
    (le_of_lt (chebRightTwo_sub_chebLeftLw_pos hA0 hT8))
    (chebRightTwo_sub_chebLeftLw_le A _) rfl
  -- multiply through by the shape
  have hZE0 : (0 : ℝ) ≤ (N + H + 1) * chebFactorLw A (N + H + 1) := mul_nonneg hZ0.le hE0
  have hstep := mul_le_mul_of_nonneg_right hcoeff hZE0
  -- the final collapse
  have hlogsq : Real.log (chebHeightLw A (N + H + 1)) ^ 2 = 4 * (A * Real.log (N + H + 1)) :=
    sq_log_chebHeightLw A _ hAZ0
  have hsq : A * Real.log (N + H + 1) = Real.sqrt (A * Real.log (N + H + 1)) ^ 2 :=
    (Real.sq_sqrt hAZ0).symm
  have hsplit : Real.sqrt A * Real.sqrt (Real.log (N + H + 1))
      = Real.sqrt (A * Real.log (N + H + 1)) := (Real.sqrt_mul hA0.le _).symm
  have hWbE : (1 + Cm * (9 * Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6)))
        * chebFactorLw A (N + H + 1)
      ≤ (3 + 27 * Cm)
          * Real.exp (-(2 * (1 / 12) * Real.sqrt (A * Real.log (N + H + 1)))) := by
    have h := one_add_width_mul_factor_le_lw (A := A) hA0.le hCm hN0
      (by linarith : N ≤ N + H + 1)
    rw [hsplit] at h
    have heq : -(2 * (1 / 12) * Real.sqrt (A * Real.log (N + H + 1)))
        = -(Real.sqrt (A * Real.log (N + H + 1)) / 6) := by ring
    rw [heq]
    exact h
  have hfin := cheb_final_collapse_lw (Cr := Cr) (Cm := Cm) (Z := N + H + 1)
    (s := Real.sqrt (A * Real.log (N + H + 1))) (r := 1 / 12)
    (Q := A * Real.log (N + H + 1))
    (Wb := Cm * (9 * Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6)))
    (E := chebFactorLw A (N + H + 1)) hCr0.le hCm hZ0.le (Real.sqrt_nonneg _) (by norm_num) hsq
    hWbE
  rw [hlogsq] at hbase hshaped hstep
  linarith [hbase, hshaped, hstep, hfin]


end RHTower.Sieve
