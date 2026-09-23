import GaloisForLFunctions.RHTower.Sieve.ChebyshevSharpRateOne

/-!
# The sharp Chebyshev sum against the cutoff's mass

Adding the main term's discrepancy and the sharp transfer's cost to the contour bound, and removing
the scalar `2π` that Perron carries, gives

```text
‖ ψ(⌊N⌋) - (mass of the cutoff) ‖ ≤ B · Z · exp( -√(log Z) / 960000 ),      Z = N + H + 1.
```

Both corrections are of the contour's own order — the bracket costs `Z·exp(-√(log Z)/480000)` and
the transfer `log Z · Z · exp(-√(log Z)/480000)` — so only the polynomial `log Z` has to be
absorbed, halving the exponent one final time.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The sharp Chebyshev sum against the cutoff's mass, with an explicit saving of exponent
`1/2`.** -/
theorem exists_norm_sum_vonMangoldt_sub_mass_kappa_one_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1‖
        ≤ B * (N + chebWidthOne N + 1)
            * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000)) := by
  obtain ⟨B₁, hB₁, hrate⟩ := exists_norm_tsum_vonMangoldt_kappa_one_rate
  refine ⟨(B₁ + 2) + 8 * 960000 ^ (2 : ℕ), by nlinarith [hB₁], ?_⟩
  filter_upwards [hrate, eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (16 : ℝ)] with N hcap hN3 hlogN
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) ≤ chebWidthOne N := chebWidthOne_nonneg hN0.le
  have hH1 : (1 : ℝ) ≤ chebWidthOne N := one_le_chebWidthOne hN0 (by linarith)
  have hZ0 : (0 : ℝ) < N + chebWidthOne N + 1 := by linarith
  have hlogZ : (16 : ℝ) ≤ Real.log (N + chebWidthOne N + 1) :=
    le_trans hlogN (Real.log_le_log hN0 (by linarith))
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log (N + chebWidthOne N + 1)) := Real.sqrt_nonneg _
  have hE0 : (0 : ℝ) < Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) :=
    Real.exp_pos _
  have hF0 : (0 : ℝ) < Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000)) :=
    Real.exp_pos _
  have hEF : Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000))
      ≤ Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  -- the contour bound, with the scalar written multiplicatively
  have hcap' : ‖((2 * Real.pi : ℝ) : ℂ)
        * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) (n : ℝ) : ℝ) : ℂ))
      - mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1
        * (((2 * Real.arctan (chebHeightOne (N + chebWidthOne N + 1)
                / (chebRightTwo (chebHeightOne (N + chebWidthOne N + 1)) - 1))
              - 2 * Real.arctan (chebHeightOne (N + chebWidthOne N + 1)
                / (chebLeftTwo (chebHeightOne (N + chebWidthOne N + 1)) - 1)) : ℝ)) : ℂ)‖
      ≤ B₁ * (N + chebWidthOne N + 1)
          * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) := by
    rwa [← Complex.real_smul]
  -- the main term's discrepancy
  have hmain := cheb_main_term_error_le hN0 (by linarith) hlogZ
  have hmain2 : ‖mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1
        * (((2 * Real.arctan (chebHeightOne (N + chebWidthOne N + 1)
                / (chebRightTwo (chebHeightOne (N + chebWidthOne N + 1)) - 1))
              - 2 * Real.arctan (chebHeightOne (N + chebWidthOne N + 1)
                / (chebLeftTwo (chebHeightOne (N + chebWidthOne N + 1)) - 1)) : ℝ)) : ℂ)
      - mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1
        * (((2 * Real.pi : ℝ)) : ℂ)‖
      ≤ 2 * ((N + chebWidthOne N + 1)
          * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000))) := by
    rw [norm_mul_sub_mul_ofReal]
    exact hmain
  -- the scalar and the bracket come off
  have hAM := norm_sub_le_of_scaled hπ1 hcap' hmain2
  -- the sharp transfer
  have htr := norm_tsum_vonMangoldt_smoothWeight_sub_sum_le hN0 (by linarith)
    (by linarith : (1 : ℝ) ≤ N + chebWidthOne N)
  have hcost := cheb_sharp_transfer_cost_le hN3 hlogN
  have hswap : ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
      - ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) (n : ℝ) : ℝ) : ℂ)‖
      = ‖(∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)‖ := norm_sub_rev _ _
  -- the triangle inequality
  have htri : ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
      - mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1‖
      ≤ ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
          - ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) (n : ℝ) : ℝ) : ℂ)‖
        + ‖(∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) (n : ℝ) : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1‖ := by
    have h := norm_add_le
      ((∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
        - ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) (n : ℝ) : ℝ) : ℂ))
      ((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1)
    rwa [sub_add_sub_cancel] at h
  -- absorb the polynomial
  have habs := sq_mul_exp_neg_le' hs0
  have hZE : (0 : ℝ) ≤ N + chebWidthOne N + 1 := by linarith
  have hkey : 2 * (Real.sqrt (Real.log (N + chebWidthOne N + 1)) ^ (2 : ℕ)
        * ((N + chebWidthOne N + 1)
            * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000))))
      ≤ 8 * 960000 ^ (2 : ℕ) * ((N + chebWidthOne N + 1)
          * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000))) := by
    have h := mul_le_mul_of_nonneg_left habs
      (by linarith : (0 : ℝ) ≤ 2 * (N + chebWidthOne N + 1))
    nlinarith [h]
  have hEZ : B₁ * (N + chebWidthOne N + 1)
        * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000))
      + 2 * ((N + chebWidthOne N + 1)
          * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)))
      ≤ (B₁ + 2) * ((N + chebWidthOne N + 1)
          * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000))) := by
    have hc0 : (0 : ℝ) ≤ (B₁ + 2) * (N + chebWidthOne N + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have h := mul_le_mul_of_nonneg_left hEF hc0
    nlinarith [h]
  linarith [htri, hswap, htr, hcost, hAM, hkey, hEZ]

end RHTower.Sieve
