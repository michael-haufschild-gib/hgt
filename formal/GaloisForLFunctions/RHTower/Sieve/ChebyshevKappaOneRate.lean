import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneThreshold
import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneContour

/-!
# The smoothed Chebyshev sum at the balanced parameters

Instantiating the width-`1/log` contour bound at

```text
H = chebWidthOne N,      T = chebHeightOne (N + H + 1)
```

and feeding it through the term reductions, the coefficient bound and the two collapse steps gives

```text
‖ 2π ∑' Λ(n)w(n) - (mass)·(bracket) ‖ ≤ B · (N+H+1) · exp( -√(log(N+H+1)) / 480000 ).
```

Every constant is explicit in `Cm` (the Mellin decay constant) and `Cr` (the bound on the regular
part of `ζ'/ζ` on the exponent-one region); nothing depends on the cutoff.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The smoothed Chebyshev sum, with an explicit saving of exponent `1/2`.** -/
theorem exists_norm_tsum_vonMangoldt_kappa_one_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) (n : ℝ) : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1
              * (((2 * Real.arctan (chebHeightOne (N + chebWidthOne N + 1)
                      / (chebRightTwo (chebHeightOne (N + chebWidthOne N + 1)) - 1))
                    - 2 * Real.arctan (chebHeightOne (N + chebWidthOne N + 1)
                      / (chebLeftTwo (chebHeightOne (N + chebWidthOne N + 1)) - 1)) : ℝ)) : ℂ)‖
        ≤ B * (N + chebWidthOne N + 1)
            * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) := by
  obtain ⟨Cm, Cr, L₀, hCm, hCr0, hL₀8, hmain⟩ :=
    exists_norm_tsum_vonMangoldt_kappa_one_general
  refine ⟨250000 * (1 + Cr) * (3 + 27 * Cm) * (4 * (4 * 480000 ^ 2)), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 1 + Cr := by linarith
    have h2 : (0 : ℝ) ≤ 3 + 27 * Cm := by linarith
    nlinarith [h1, h2]
  filter_upwards [eventually_cheb_kappa_one_conditions L₀] with N hcond
  obtain ⟨hN0, hH1, hHN, hZ16, hTL⟩ := hcond
  set H : ℝ := chebWidthOne N with hHdef
  have hH0 : (0 : ℝ) < H := by linarith
  have hZ0 : (0 : ℝ) < N + H + 1 := by linarith
  have hY0 : (0 : ℝ) ≤ N + H := by linarith
  have hY1 : (1 : ℝ) ≤ N + H := by linarith
  have hT1 : (1 : ℝ) ≤ chebHeightOne (N + H + 1) := one_le_chebHeightOne _
  have hT8 : (8 : ℝ) ≤ Real.log (chebHeightOne (N + H + 1)) := eight_le_log_chebHeightOne hZ16
  have hbase := hmain N H hN0 hH0 (chebHeightOne (N + H + 1)) hT1 hTL
  -- the three edge powers
  have hZd := rpow_chebRightTwo_at_le hZ0 hZ16
  have hZc := rpow_chebLeftTwo_at_le hZ0 hZ16
  have hYc := rpow_chebLeftTwo_at_shift hY1 hZ16
  have hZd0 : (0 : ℝ) ≤ (N + H + 1) ^ chebRightTwo (chebHeightOne (N + H + 1)) :=
    Real.rpow_nonneg hZ0.le _
  -- the remaining shape data
  have hE0 : (0 : ℝ) ≤ chebFactorOne (N + H + 1) := (chebFactorOne_pos _).le
  have hMm := norm_mellin_smoothWeight_one_le hN0.le hH0
  have hTE := one_div_chebHeightOne_le_factor (N + H + 1)
  have hc := half_le_chebLeftTwo hT8
  have hS0 : (0 : ℝ) ≤ ∑' n : ℕ, (vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(chebRightTwo (chebHeightOne (N + H + 1)))) :=
    tsum_nonneg fun n =>
      mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hW0 : (0 : ℝ) ≤ Cm / H ^ 2 * (N + H + 1) ^ 2 :=
    mul_nonneg (div_nonneg hCm (by positivity)) (by positivity)
  -- the five terms collapse to a shape
  have hshaped := cheb_kappa_one_terms_shaped
    (S := ∑' n : ℕ, (vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(chebRightTwo (chebHeightOne (N + H + 1)))))
    (W := Cm / H ^ 2 * (N + H + 1) ^ 2) (Y := N + H) (Z := N + H + 1)
    (E := chebFactorOne (N + H + 1)) (T := chebHeightOne (N + H + 1))
    (Mm := ‖mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖)
    (ci := (1 - chebLeftTwo (chebHeightOne (N + H + 1)))⁻¹)
    (wd := chebRightTwo (chebHeightOne (N + H + 1)) - chebLeftTwo (chebHeightOne (N + H + 1)))
    (M := Cr * Real.log (chebHeightOne (N + H + 1)) ^ 2)
    (c := chebLeftTwo (chebHeightOne (N + H + 1)))
    hS0 hW0
    (by rw [one_sub_chebLeftTwo_inv hT8]; positivity)
    (le_of_lt (chebRightTwo_sub_chebLeftTwo_pos hT8))
    (by positivity)
    hT1 hE0 hY0 (by linarith) hc hMm hTE hZd0 hZd hZc hYc
  -- the coefficient
  have hcoeff := cheb_kappa_one_coeff_le
    (S := ∑' n : ℕ, (vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(chebRightTwo (chebHeightOne (N + H + 1)))))
    (W := Cm / H ^ 2 * (N + H + 1) ^ 2)
    (ci := (1 - chebLeftTwo (chebHeightOne (N + H + 1)))⁻¹)
    (wd := chebRightTwo (chebHeightOne (N + H + 1)) - chebLeftTwo (chebHeightOne (N + H + 1)))
    (M := Cr * Real.log (chebHeightOne (N + H + 1)) ^ 2) (Cr := Cr)
    (Lg := Real.log (chebHeightOne (N + H + 1)))
    (Wb := Cm * (9 * Real.exp (Real.sqrt (Real.log N) / 120000)))
    hT8 hW0
    (width_price_le hH1 hN0.le (le_of_eq (div_chebWidthOne hN0)) hCm (sq_chebRatioOne_le N))
    hCr0.le (tsum_vonMangoldt_chebRightTwo_le hT8) (one_sub_chebLeftTwo_inv hT8)
    (le_of_lt (chebRightTwo_sub_chebLeftTwo_pos hT8)) (chebRightTwo_sub_chebLeftTwo_le hT8) rfl
  -- multiply through by the shape
  have hZE0 : (0 : ℝ) ≤ (N + H + 1) * chebFactorOne (N + H + 1) := mul_nonneg hZ0.le hE0
  have hstep := mul_le_mul_of_nonneg_right hcoeff hZE0
  -- the final collapse
  have hlogsq : Real.log (chebHeightOne (N + H + 1)) ^ 2 = 4 * Real.log (N + H + 1) :=
    sq_log_chebHeightOne _ (by linarith)
  have hsq : Real.log (N + H + 1) = Real.sqrt (Real.log (N + H + 1)) ^ 2 :=
    (Real.sq_sqrt (by linarith)).symm
  have hfin := cheb_final_collapse (Cr := Cr) (Cm := Cm) (Z := N + H + 1)
    (s := Real.sqrt (Real.log (N + H + 1)))
    (Wb := Cm * (9 * Real.exp (Real.sqrt (Real.log N) / 120000)))
    (E := chebFactorOne (N + H + 1)) hCr0.le hCm hZ0.le (Real.sqrt_nonneg _) hsq
    (one_add_width_mul_factor_le hCm hN0 (by linarith))
  rw [hlogsq] at hbase hshaped hstep
  linarith [hbase, hshaped, hstep, hfin]

end RHTower.Sieve
