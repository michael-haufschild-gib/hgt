import GaloisForLFunctions.RHTower.ResidueClassRecipSeries

/-!
# The digamma value at three quarters, and the remaining quarter-progression sums

`DigammaQuarter` proves `ψ(1/4) = −γ − π/2 − 3log 2` from Legendre duplication and reflection, and along the
way the two relations

`ψ(1/4) + ψ(3/4) = 2ψ(1/2) − 2log 2`,  `ψ(1/4) − ψ(3/4) = −π`.

Either one gives the companion value:

**`digamma_three_quarter` — `ψ(3/4) = −γ − 3log 2 + π/2`.**

With it, `ResidueClassRecipSeries.hasSum_residueClass_recip` evaluates the two remaining reciprocal sums over
progressions mod `4`:

* **`hasSum_quarter_recip_two` — `∑_{k≥0} 1/((4k+2)(4k+3)) = (π/2 − log 2)/4`;**
* **`hasSum_quarter_recip_three` — `∑_{k≥0} 1/((4k+3)(4k+4)) = (3log 2 − π/2)/4`.**

Together with `hasSum_quarter_recip_one` (`(log 2 + π/2)/4`) these are the three constants `T₁, T₂, T₃` that
the `q = 4` Báez-Duarte Gram entry is built from: `(n mod 4)² = (n mod 4) + 2·[n≡2] + 6·[n≡3]`, so
`∑ (n mod 4)²/(n(n+1)) = log 4 + 2T₂ + 6T₃ = 6log 2 − π/2`, predicting
`bdGram (1/4) (1/4) = (3log 2)/8 − π/32`.  Assembling that still needs the residue-class decomposition of `ℕ`
as a `HasSum`; the constants themselves are now all proved.

As a check on their signs: `T₂ = (π/2 − log 2)/4 > 0` and `T₃ = (3log 2 − π/2)/4 > 0`, both established below.
-/

open Complex

noncomputable section

namespace RHTower

/-- **The digamma value at three quarters.** -/
theorem digamma_three_quarter :
    Complex.digamma (3 / 4 : ℂ)
      = -(((3 * Real.log 2 + Real.eulerMascheroniConstant - Real.pi / 2 : ℝ)) : ℂ) := by
  have hdiff := GaloisForLFunctions.RHTower.digamma_quarter_sub_three_quarter
  have hq := GaloisForLFunctions.RHTower.digamma_quarter
  rw [hq] at hdiff
  push_cast at hdiff ⊢
  linear_combination -hdiff

/-- `∑_{k≥0} 1/((4k+2)(4k+3)) = (π/2 − log 2)/4`. -/
theorem hasSum_quarter_recip_two :
    HasSum (fun k : ℕ => 1 / ((((4 * k + 2 : ℕ)) : ℂ) * (((4 * k + 2 + 1 : ℕ)) : ℂ)))
      ((((Real.pi / 2 - Real.log 2) / 4 : ℝ)) : ℂ) := by
  have h := hasSum_residueClass_recip (q := 4) (j := 2) (by norm_num) (by norm_num)
  have harg1 : (((2 : ℕ) : ℂ) + 1) / ((4 : ℕ) : ℂ) = 3 / 4 := by norm_num
  have harg2 : (((2 : ℕ) : ℂ)) / ((4 : ℕ) : ℂ) = 1 / 2 := by norm_num
  rw [harg1, harg2, Complex.digamma_one_half, digamma_three_quarter] at h
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num]
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog] at h
  convert h using 1
  push_cast
  ring

/-- `∑_{k≥0} 1/((4k+3)(4k+4)) = (3 log 2 − π/2)/4`. -/
theorem hasSum_quarter_recip_three :
    HasSum (fun k : ℕ => 1 / ((((4 * k + 3 : ℕ)) : ℂ) * (((4 * k + 3 + 1 : ℕ)) : ℂ)))
      ((((3 * Real.log 2 - Real.pi / 2) / 4 : ℝ)) : ℂ) := by
  have h := hasSum_residueClass_recip (q := 4) (j := 3) (by norm_num) (by norm_num)
  have harg1 : (((3 : ℕ) : ℂ) + 1) / ((4 : ℕ) : ℂ) = 1 := by norm_num
  have harg2 : (((3 : ℕ) : ℂ)) / ((4 : ℕ) : ℂ) = 3 / 4 := by norm_num
  rw [harg1, harg2, Complex.digamma_one, digamma_three_quarter] at h
  convert h using 1
  push_cast
  ring

/-- The two constants are positive: `log 2 < π/2 < 3 log 2`. -/
theorem quarter_recip_constants_pos :
    0 < (Real.pi / 2 - Real.log 2) / 4 ∧ 0 < (3 * Real.log 2 - Real.pi / 2) / 4 := by
  have h1 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h3 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h4 : Real.pi < 3.15 := Real.pi_lt_d2
  constructor
  · nlinarith
  · nlinarith

end RHTower

end
