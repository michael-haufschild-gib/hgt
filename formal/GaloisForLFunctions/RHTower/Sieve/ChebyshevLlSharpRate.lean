import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlTransfer

/-!
# The sharp Chebyshev sum at Littlewood strength

Adding the bracket's discrepancy and the sharp transfer's cost to the contour bound, and removing
the scalar `2π` that Perron carries, gives

```text
‖ ψ(⌊N⌋) - (mass of the cutoff) ‖ ≤ B · Z · exp( -√(c·log Z·log log Z) / 48 ) .
```

Both corrections are of the contour's own order; only the polynomial `log Z` has to be absorbed,
and `log Z ≤ ½·c·log Z·log log Z` puts it under the square of the saving's argument, so one
halving of the exponent suffices.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 1000000 in
/-- **The sharp Chebyshev sum against the cutoff's mass, at Littlewood strength.** -/
theorem exists_norm_sum_vonMangoldt_sub_mass_ll_rate :
    ∃ c B : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthLl c N) x : ℝ) : ℂ)) 1‖
        ≤ B * (N + chebWidthLl c N + 1)
            * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 48)) := by
  obtain ⟨c, B₁, hc0, hchalf, hB₁, hrate⟩ := exists_norm_tsum_vonMangoldt_ll_rate
  refine ⟨c, B₁ + 2 + 9216, hc0, hchalf, by linarith, ?_⟩
  filter_upwards [hrate, eventually_cheb_ll_conditions c 0 hc0 (by linarith),
    eventually_ge_atTop (3 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)]
    with N hcap hcond hN3 hlogN
  obtain ⟨hN0, hN1, hH1, hHN, hlogZ0, hQ256, hQ2, hdepth, -⟩ := hcond
  set H : ℝ := chebWidthLl c N with hHdef
  have hH0 : (0 : ℝ) < H := by linarith
  have hZ0 : (0 : ℝ) < N + H + 1 := by linarith
  have hY1 : (1 : ℝ) ≤ N + H := by linarith
  set s : ℝ := Real.sqrt (chebQuadLl c (N + H + 1)) with hsdef
  have hs0 : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ (2 : ℕ) = chebQuadLl c (N + H + 1) := Real.sq_sqrt (by linarith)
  have hE1248 : Real.exp (-(s / 12)) ≤ Real.exp (-(s / 48)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hE2448 : Real.exp (-(s / 24)) ≤ Real.exp (-(s / 48)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hE480 : (0 : ℝ) < Real.exp (-(s / 48)) := Real.exp_pos _
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  -- the contour bound, with the scalar written multiplicatively
  have hcap' : ‖((2 * Real.pi : ℝ) : ℂ)
        * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      - mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1
        * (((2 * Real.arctan (chebHeightLl c (N + H + 1)
                / (chebRightTwo (chebHeightLl c (N + H + 1)) - 1))
              - 2 * Real.arctan (chebHeightLl c (N + H + 1)
                / (chebLeftLl c (chebHeightLl c (N + H + 1)) - 1)) : ℝ)) : ℂ)‖
      ≤ B₁ * (N + H + 1) * Real.exp (-(s / 12)) := by
    rwa [← Complex.real_smul]
  -- the main term's discrepancy
  have hmain := cheb_ll_main_term_error_le hc0 hchalf hN0 hH0 hQ256
  have hmain2 : ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1
        * (((2 * Real.arctan (chebHeightLl c (N + H + 1)
                / (chebRightTwo (chebHeightLl c (N + H + 1)) - 1))
              - 2 * Real.arctan (chebHeightLl c (N + H + 1)
                / (chebLeftLl c (chebHeightLl c (N + H + 1)) - 1)) : ℝ)) : ℂ)
      - mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1
        * (((2 * Real.pi : ℝ)) : ℂ)‖
      ≤ 2 * ((N + H + 1) * Real.exp (-(s / 24))) := by
    rw [norm_mul_sub_mul_ofReal]
    exact hmain
  -- the scalar and the bracket come off
  have hAM := norm_sub_le_of_scaled hπ1 hcap' hmain2
  -- the sharp transfer
  have htr := norm_tsum_vonMangoldt_smoothWeight_sub_sum_le hN0 hH0 hY1
  have hcost := cheb_ll_sharp_transfer_cost_le (c := c) hc0.le (by linarith) hN3 hlogN
  have hswap : ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
      - ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
      = ‖(∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)‖ := norm_sub_rev _ _
  -- the triangle inequality
  have htri : ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
      - mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖
      ≤ ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
          - ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
        + ‖(∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖ := by
    have h := norm_add_le
      ((∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
        - ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      ((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1)
    rwa [sub_add_sub_cancel] at h
  -- the polynomial is absorbed by half the saving
  have habsorb : Real.log (N + H + 1) * Real.exp (-(s / 24)) ≤ 4608 * Real.exp (-(s / 48)) := by
    have hkey := sq_mul_exp_neg_le_gen (r := (1 : ℝ) / 48) (s := s) (by norm_num) hs0
    have hkeq : -((1 : ℝ) / 48 * s) = -(s / 48) := by ring
    rw [hkeq] at hkey
    have hval : (4 : ℝ) / ((1 : ℝ) / 48) ^ (2 : ℕ) = 9216 := by norm_num
    rw [hval] at hkey
    have hsplit : Real.exp (-(s / 24)) = Real.exp (-(s / 48)) * Real.exp (-(s / 48)) := by
      rw [← Real.exp_add]; ring_nf
    have hlogle : Real.log (N + H + 1) ≤ s ^ (2 : ℕ) / 2 := by rw [hs2]; linarith
    rw [hsplit]
    have hstep : Real.log (N + H + 1) * (Real.exp (-(s / 48)) * Real.exp (-(s / 48)))
        ≤ s ^ (2 : ℕ) / 2 * (Real.exp (-(s / 48)) * Real.exp (-(s / 48))) := by
      refine mul_le_mul_of_nonneg_right hlogle ?_
      positivity
    have hmul : s ^ (2 : ℕ) * Real.exp (-(s / 48)) * Real.exp (-(s / 48))
        ≤ 9216 * Real.exp (-(s / 48)) := mul_le_mul_of_nonneg_right hkey hE480.le
    have hhalf : s ^ (2 : ℕ) / 2 * (Real.exp (-(s / 48)) * Real.exp (-(s / 48)))
        = (s ^ (2 : ℕ) * Real.exp (-(s / 48)) * Real.exp (-(s / 48))) / 2 := by ring
    linarith [hstep, hmul, hhalf.le, hhalf.ge]
  -- collect
  have hZ0' : (0 : ℝ) ≤ N + H + 1 := by linarith
  have hpoly : 2 * (Real.log (N + H + 1) * ((N + H + 1) * Real.exp (-(s / 24))))
      ≤ 9216 * ((N + H + 1) * Real.exp (-(s / 48))) := by
    have h := mul_le_mul_of_nonneg_left habsorb (by linarith : (0 : ℝ) ≤ 2 * (N + H + 1))
    linarith [h]
  have hlin : B₁ * (N + H + 1) * Real.exp (-(s / 12))
      + 2 * ((N + H + 1) * Real.exp (-(s / 24)))
      ≤ (B₁ + 2) * ((N + H + 1) * Real.exp (-(s / 48))) := by
    have h1 : B₁ * (N + H + 1) * Real.exp (-(s / 12))
        ≤ B₁ * (N + H + 1) * Real.exp (-(s / 48)) :=
      mul_le_mul_of_nonneg_left hE1248 (mul_nonneg hB₁ hZ0')
    have h2 : 2 * ((N + H + 1) * Real.exp (-(s / 24)))
        ≤ 2 * ((N + H + 1) * Real.exp (-(s / 48))) := by
      have := mul_le_mul_of_nonneg_left hE2448 hZ0'
      linarith
    linarith [h1, h2]
  linarith [htri, hswap, htr, hcost, hAM, hpoly, hlin]

end RHTower.Sieve
