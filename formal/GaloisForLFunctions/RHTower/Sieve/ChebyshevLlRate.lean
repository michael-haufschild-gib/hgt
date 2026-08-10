import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodCoeff
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlContour
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlThreshold

/-!
# The smoothed Chebyshev sum at Littlewood strength

The contour balance run at a rectangle whose depth grows with the height.  The depth is
`c·log log T`, the height is `exp(√(c·log Z·log log Z))`, and the surviving saving is

```text
exp(-√(c·log Z·log log Z)/12) ,
```

Littlewood's prime number theorem error term.  The fixed-depth chain cannot reach it: there the
constants degrade with the depth, so the depth cannot be allowed to grow with the cutoff.  Here
`c` is one absolute constant, supplied by the Littlewood zero-free region, and the balance is a
fixed point rather than a choice.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The smoothed Chebyshev sum at Littlewood strength.**  The saving is
`exp(-√(c·log Z·log log Z)/12)`. -/
theorem exists_norm_tsum_vonMangoldt_ll_rate :
    ∃ c B : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthLl c N) (n : ℝ) : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthLl c N) x : ℝ) : ℂ)) 1
              * (((2 * Real.arctan (chebHeightLl c (N + chebWidthLl c N + 1)
                      / (chebRightTwo (chebHeightLl c (N + chebWidthLl c N + 1)) - 1))
                    - 2 * Real.arctan (chebHeightLl c (N + chebWidthLl c N + 1)
                      / (chebLeftLl c (chebHeightLl c (N + chebWidthLl c N + 1))
                          - 1)) : ℝ)) : ℂ)‖
        ≤ B * (N + chebWidthLl c N + 1)
            * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 12)) := by
  obtain ⟨c, Cm, Cr, L₀, hc0, hchalf, hCm, hCr0, hL₀8, hmain⟩ :=
    exists_norm_tsum_vonMangoldt_ll_plain
  refine ⟨c, 250000 * (1 + Cr) * (3 + 27 * Cm) * (4 * (4 / ((1 : ℝ) / 6) ^ 2)), hc0,
    hchalf, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 1 + Cr := by linarith
    have h2 : (0 : ℝ) ≤ 3 + 27 * Cm := by linarith
    have h3 : (4 : ℝ) * (4 / ((1 : ℝ) / 6) ^ 2) = 576 := by norm_num
    rw [h3]
    nlinarith [h1, h2]
  filter_upwards [eventually_cheb_ll_conditions c L₀ hc0 (by linarith)] with N hcond
  obtain ⟨hN0, hN1, hH1, hHN, hlogZ0, hQ256, hQ2, hdepth, hTL⟩ := hcond
  set H : ℝ := chebWidthLl c N with hHdef
  have hH0 : (0 : ℝ) < H := by linarith
  have hZ0 : (0 : ℝ) < N + H + 1 := by linarith
  have hY0 : (0 : ℝ) ≤ N + H := by linarith
  have hY1 : (1 : ℝ) ≤ N + H := by linarith
  have hcx : Real.log (N + H + 1) ≤ chebQuadLl c (N + H + 1) := by linarith
  have hT1 : (1 : ℝ) ≤ chebHeightLl c (N + H + 1) := one_le_chebHeightLl c _
  have hT16 : (16 : ℝ) ≤ Real.log (chebHeightLl c (N + H + 1)) :=
    sixteen_le_log_chebHeightLl hQ256
  have hT8 : (8 : ℝ) ≤ Real.log (chebHeightLl c (N + H + 1)) := by linarith
  have hbase := hmain N H hN0 hH0 (chebHeightLl c (N + H + 1)) hT1 hTL
  -- the three edge powers
  have hZd := rpow_chebRightTwo_at_ll_le (c := c) hZ0 hQ256 hQ2
  have hZc := rpow_chebLeftLl_at_le hc0 hZ0 hlogZ0 hQ256 hcx
  have hYc := rpow_chebLeftLl_at_shift (c := c) (Y := N + H) hc0 hchalf hY1 hlogZ0 hQ256 hcx
  have hZd0 : (0 : ℝ) ≤ (N + H + 1) ^ chebRightTwo (chebHeightLl c (N + H + 1)) :=
    Real.rpow_nonneg hZ0.le _
  -- the remaining shape data
  have hE0 : (0 : ℝ) ≤ chebFactorLl c (N + H + 1) := (chebFactorLl_pos c _).le
  have hMm := norm_mellin_smoothWeight_one_le hN0.le hH0
  have hTE := one_div_chebHeightLl_le_factor c (N + H + 1)
  have hc := half_le_chebLeftLl hc0 hchalf hT8
  have hS0 : (0 : ℝ) ≤ ∑' n : ℕ, (vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(chebRightTwo (chebHeightLl c (N + H + 1)))) :=
    tsum_nonneg fun n =>
      mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hW0 : (0 : ℝ) ≤ Cm / H ^ 2 * (N + H + 1) ^ 2 :=
    mul_nonneg (div_nonneg hCm (by positivity)) (by positivity)
  -- the effective depth of the rectangle
  have hA1 : 1 ≤ chebDepthLl c (N + H + 1) := one_le_chebDepthLl hc0 hlogZ0 hcx hdepth
  have hALg : 8 * chebDepthLl c (N + H + 1) ≤ Real.log (chebHeightLl c (N + H + 1)) :=
    eight_mul_chebDepthLl_le hc0 hchalf hQ256
  have hwdpos : 0 < chebRightTwo (chebHeightLl c (N + H + 1))
      - chebLeftLl c (chebHeightLl c (N + H + 1)) :=
    chebRightTwo_sub_chebLeftLl_pos hc0 hT8
  have hci0 : (0 : ℝ) ≤ (1 - chebLeftLl c (chebHeightLl c (N + H + 1)))⁻¹ := by
    rw [one_sub_chebLeftLl_inv]
    have hLL : (0 : ℝ) ≤ Real.log (Real.log (chebHeightLl c (N + H + 1))) :=
      Real.log_nonneg (by linarith)
    positivity
  -- the five terms collapse to a shape
  have hshaped := cheb_kappa_one_terms_shaped
    (S := ∑' n : ℕ, (vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(chebRightTwo (chebHeightLl c (N + H + 1)))))
    (W := Cm / H ^ 2 * (N + H + 1) ^ 2) (Y := N + H) (Z := N + H + 1)
    (E := chebFactorLl c (N + H + 1)) (T := chebHeightLl c (N + H + 1))
    (Mm := ‖mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖)
    (ci := (1 - chebLeftLl c (chebHeightLl c (N + H + 1)))⁻¹)
    (wd := chebRightTwo (chebHeightLl c (N + H + 1))
      - chebLeftLl c (chebHeightLl c (N + H + 1)))
    (M := Cr * Real.log (chebHeightLl c (N + H + 1)) ^ 2)
    (c := chebLeftLl c (chebHeightLl c (N + H + 1)))
    hS0 hW0 hci0 hwdpos.le (by positivity)
    hT1 hE0 hY0 (by linarith) hc hMm hTE hZd0 hZd hZc hYc
  -- the coefficient
  have hcoeff := cheb_littlewood_coeff_le (A := chebDepthLl c (N + H + 1))
    (S := ∑' n : ℕ, (vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(chebRightTwo (chebHeightLl c (N + H + 1)))))
    (W := Cm / H ^ 2 * (N + H + 1) ^ 2)
    (ci := (1 - chebLeftLl c (chebHeightLl c (N + H + 1)))⁻¹)
    (wd := chebRightTwo (chebHeightLl c (N + H + 1))
      - chebLeftLl c (chebHeightLl c (N + H + 1)))
    (M := Cr * Real.log (chebHeightLl c (N + H + 1)) ^ 2) (Cr := Cr)
    (Lg := Real.log (chebHeightLl c (N + H + 1)))
    (Wb := Cm * (9 * Real.exp (chebSavingLl c N / 3)))
    hT8 hW0
    (width_price_le_gen hH1 hN0.le (le_of_eq (div_chebWidthLl hN0)) hCm (sq_chebRatioLl_le c N))
    hCr0.le (tsum_vonMangoldt_chebRightTwo_le hT8) hA1 hALg
    (by rw [one_sub_chebLeftLl_inv, chebDepthLl])
    hwdpos.le
    (by rw [chebDepthLl]; exact chebRightTwo_sub_chebLeftLl_le c _) rfl
  -- multiply through by the shape
  have hZE0 : (0 : ℝ) ≤ (N + H + 1) * chebFactorLl c (N + H + 1) := mul_nonneg hZ0.le hE0
  have hstep := mul_le_mul_of_nonneg_right hcoeff hZE0
  -- the final collapse
  have hlogsq : Real.log (chebHeightLl c (N + H + 1)) ^ 2
      = 4 * chebSavingLl c (N + H + 1) ^ 2 := sq_log_chebHeightLl c _
  have hWbE : (1 + Cm * (9 * Real.exp (chebSavingLl c N / 3)))
        * chebFactorLl c (N + H + 1)
      ≤ (3 + 27 * Cm)
          * Real.exp (-(2 * (1 / 6) * chebSavingLl c (N + H + 1))) := by
    have h := one_add_width_mul_factor_le_ll (c := c) hc0.le hCm hN0 hN1
      (by linarith : N ≤ N + H + 1)
    have heq : -(2 * (1 / 6) * chebSavingLl c (N + H + 1))
        = -(chebSavingLl c (N + H + 1) / 3) := by ring
    rw [heq]
    exact h
  have hfin := cheb_final_collapse_lw (Cr := Cr) (Cm := Cm) (Z := N + H + 1)
    (s := chebSavingLl c (N + H + 1)) (r := 1 / 6)
    (Q := chebSavingLl c (N + H + 1) ^ 2)
    (Wb := Cm * (9 * Real.exp (chebSavingLl c N / 3)))
    (E := chebFactorLl c (N + H + 1)) hCr0.le hCm hZ0.le (chebSavingLl_nonneg c _)
    (by norm_num) rfl hWbE
  have hexpeq : Real.exp (-(1 / 6 * chebSavingLl c (N + H + 1)))
      = Real.exp (-(Real.sqrt (chebQuadLl c (N + H + 1)) / 12)) := by
    congr 1
    rw [chebSavingLl]
    ring
  rw [hlogsq] at hbase hshaped hstep
  rw [hexpeq] at hfin
  linarith [hbase, hshaped, hstep, hfin]

end RHTower.Sieve
