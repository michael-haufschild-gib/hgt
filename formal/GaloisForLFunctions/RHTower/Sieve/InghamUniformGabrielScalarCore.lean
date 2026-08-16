import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielInterpolationBudget
import Mathlib.Analysis.Complex.Hadamard

open Complex Set

namespace RHTower.Sieve

noncomputable section

/-- Variable-strip scalar-family core. Hadamard three-lines and exact cancellation leave the
reciprocal moving moment power on the center integral. -/
theorem inghamUniformGabriel_of_scalarFamily
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {H : ℂ → ℂ} {L R I : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hI : 0 < I)
    (hd : DiffContOnCl ℂ H
      (Complex.HadamardThreeLines.verticalStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hB : BddAbove ((norm ∘ H) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hleft : ∀ z ∈ Complex.re ⁻¹' {(1 / 2 : ℝ)},
      ‖H z‖ ≤ L ^ (3 / 4 : ℝ) * I ^ (1 / 4 : ℝ))
    (hright : ∀ z ∈ Complex.re ⁻¹' {inghamUniformGabrielRightEdge sigma},
      ‖H z‖ ≤ R ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ))
    (hcenter : ‖H (inghamUniformGabrielCenter sigma : ℂ)‖ = I) :
    I ^ inghamUniformGabrielReciprocalPower sigma ≤
      L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma) := by
  have hstrip := inghamUniformGabrielCenter_mem_closedStrip hsigma0 hsigma1
  have hthree :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := H) (z := (inghamUniformGabrielCenter sigma : ℂ))
      (a := L ^ (3 / 4 : ℝ) * I ^ (1 / 4 : ℝ))
      (b := R ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ))
      (l := (1 / 2 : ℝ)) (u := inghamUniformGabrielRightEdge sigma)
      (inghamUniformGabrielRightEdge_gt_half hsigma1) hstrip hd hB hleft hright
  have hweights :
      1 - (inghamUniformGabrielCenter sigma - (1 / 2 : ℝ)) /
          (inghamUniformGabrielRightEdge sigma - (1 / 2 : ℝ)) =
            inghamUniformGabrielLeftWeight sigma ∧
      (inghamUniformGabrielCenter sigma - (1 / 2 : ℝ)) /
          (inghamUniformGabrielRightEdge sigma - (1 / 2 : ℝ)) =
            inghamUniformGabrielRightWeight sigma := by
    constructor
    · have hsum := inghamUniformGabriel_weights_sum hsigma1
      unfold inghamUniformGabrielRightWeight at hsum
      linarith
    · rfl
  rw [hcenter] at hthree
  simp only [ofReal_re] at hthree
  rw [hweights.1, hweights.2] at hthree
  have hfactor :
      (L ^ (3 / 4 : ℝ) * I ^ (1 / 4 : ℝ)) ^
          inghamUniformGabrielLeftWeight sigma *
        (R ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ)) ^
          inghamUniformGabrielRightWeight sigma =
      (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
      I ^ (1 - inghamUniformGabrielReciprocalPower sigma) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hI.le _),
      Real.mul_rpow (Real.rpow_nonneg hR.le _) (Real.rpow_nonneg hI.le _)]
    rw [← Real.rpow_mul hL.le, ← Real.rpow_mul hI.le,
      ← Real.rpow_mul hR.le, ← Real.rpow_mul hI.le]
    calc
      L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          I ^ ((1 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        (R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma) *
          I ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) =
        (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
        (I ^ ((1 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          I ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) := by ring
      _ = (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
        I ^ (((1 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) +
          ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) := by
        rw [← Real.rpow_add hI]
      _ = (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
        I ^ (1 - inghamUniformGabrielReciprocalPower sigma) := by
        congr 2
        unfold inghamUniformGabrielReciprocalPower
        ring
  rw [hfactor] at hthree
  have hIq : 0 < I ^ (1 - inghamUniformGabrielReciprocalPower sigma) :=
    Real.rpow_pos_of_pos hI _
  apply le_of_mul_le_mul_right _ hIq
  calc
    I ^ inghamUniformGabrielReciprocalPower sigma *
        I ^ (1 - inghamUniformGabrielReciprocalPower sigma) = I := by
      rw [← Real.rpow_add hI]
      convert Real.rpow_one I using 2
      all_goals ring
    _ ≤ (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
      I ^ (1 - inghamUniformGabrielReciprocalPower sigma) := hthree

end

end RHTower.Sieve
