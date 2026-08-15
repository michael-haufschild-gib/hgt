import GaloisForLFunctions.RHTower.Sieve.InghamDetectorLogMoment
import Mathlib.Analysis.Complex.Hadamard

open Complex Set

namespace RHTower.Sieve

noncomputable section

/-- Fixed coefficient-three scalar-family core. Once a scalar analytic family has the two Hölder
edge bounds and represents the center moment, Hadamard three-lines gives Gabriel's exact
`237/364` moment inequality. -/
theorem inghamFixedGabriel_of_scalarFamily
    {H : ℂ → ℂ} {L R I : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hI : 0 < I)
    (hd : DiffContOnCl ℂ H
      (Complex.HadamardThreeLines.verticalStrip (1 / 2) inghamPowerSavingRightEdge))
    (hB : BddAbove ((norm ∘ H) ''
      Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) inghamPowerSavingRightEdge))
    (hleft : ∀ z ∈ Complex.re ⁻¹' {(1 / 2 : ℝ)},
      ‖H z‖ ≤ L ^ (3 / 4 : ℝ) * I ^ (1 / 4 : ℝ))
    (hright : ∀ z ∈ Complex.re ⁻¹' {inghamPowerSavingRightEdge},
      ‖H z‖ ≤ R ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ))
    (hcenter : ‖H (inghamFixedGabrielSigma : ℂ)‖ = I) :
    I ^ (237 / 364 : ℝ) ≤
      L ^ (165 / 364 : ℝ) * R ^ (72 / 364 : ℝ) := by
  have hstrip : (inghamFixedGabrielSigma : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge := by
    constructor <;> norm_num [inghamFixedGabrielSigma, inghamPowerSavingRightEdge]
  have hthree :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := H) (z := (inghamFixedGabrielSigma : ℂ))
      (a := L ^ (3 / 4 : ℝ) * I ^ (1 / 4 : ℝ))
      (b := R ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ))
      (l := (1 / 2 : ℝ)) (u := inghamPowerSavingRightEdge)
      (by norm_num [inghamPowerSavingRightEdge]) hstrip hd hB hleft hright
  have hweights :
      1 - (inghamFixedGabrielSigma - (1 / 2 : ℝ)) /
          (inghamPowerSavingRightEdge - (1 / 2 : ℝ)) = 55 / 91 ∧
      (inghamFixedGabrielSigma - (1 / 2 : ℝ)) /
          (inghamPowerSavingRightEdge - (1 / 2 : ℝ)) = 36 / 91 := by
    constructor <;> norm_num [inghamFixedGabrielSigma, inghamPowerSavingRightEdge]
  rw [hcenter] at hthree
  simp only [ofReal_re] at hthree
  rw [hweights.1, hweights.2] at hthree
  have hfactor :
      (L ^ (3 / 4 : ℝ) * I ^ (1 / 4 : ℝ)) ^ (55 / 91 : ℝ) *
          (R ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ)) ^ (36 / 91 : ℝ) =
        (L ^ (165 / 364 : ℝ) * R ^ (72 / 364 : ℝ)) *
          I ^ (127 / 364 : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hI.le _),
      Real.mul_rpow (Real.rpow_nonneg hR.le _) (Real.rpow_nonneg hI.le _)]
    rw [← Real.rpow_mul hL.le, ← Real.rpow_mul hI.le,
      ← Real.rpow_mul hR.le, ← Real.rpow_mul hI.le]
    rw [show (3 / 4 : ℝ) * (55 / 91) = 165 / 364 by norm_num,
      show (1 / 4 : ℝ) * (55 / 91) = 55 / 364 by norm_num,
      show (1 / 2 : ℝ) * (36 / 91) = 72 / 364 by norm_num]
    calc
      L ^ (165 / 364 : ℝ) * I ^ (55 / 364 : ℝ) *
          (R ^ (72 / 364 : ℝ) * I ^ (72 / 364 : ℝ)) =
        (L ^ (165 / 364 : ℝ) * R ^ (72 / 364 : ℝ)) *
          (I ^ (55 / 364 : ℝ) * I ^ (72 / 364 : ℝ)) := by ring
      _ = (L ^ (165 / 364 : ℝ) * R ^ (72 / 364 : ℝ)) *
          I ^ (127 / 364 : ℝ) := by
        rw [← Real.rpow_add hI]
        congr 2
        norm_num
  rw [hfactor] at hthree
  have hIq : 0 < I ^ (127 / 364 : ℝ) := Real.rpow_pos_of_pos hI _
  apply le_of_mul_le_mul_right _ hIq
  calc
    I ^ (237 / 364 : ℝ) * I ^ (127 / 364 : ℝ) = I := by
      rw [← Real.rpow_add hI, show (237 / 364 : ℝ) + 127 / 364 = 1 by norm_num,
        Real.rpow_one]
    _ ≤ (L ^ (165 / 364 : ℝ) * R ^ (72 / 364 : ℝ)) *
        I ^ (127 / 364 : ℝ) := hthree

end

end RHTower.Sieve
