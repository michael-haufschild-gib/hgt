/-
# Gaussian sharp-cell estimate for separated A₆ blocks

The perturbation-stable exact-curve estimate specializes to literal
unit-coefficient A₆ blocks.  Under its explicit frequency condition, one
translated osculating cell has the sharp physical size
`N^10 M^(2+ε)`, with no additive Taylor loss.
-/
import GaloisForLFunctions.RHTower.BourgainExactOsculatingCellDecoupling
import GaloisForLFunctions.RHTower.BourgainA6BlockLocalization

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact translated-cell estimate for literal A₆ blocks, before applying
the reciprocal determinant bound. -/
theorem setLIntegral_bourgainA6PhysicalBlockSum_translatedCell_gaussian
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M q₁ q₂ : ℕ) (hN : 0 < N) (hM : 0 < M)
        (hq₁ : 0 < q₁) (hq : q₁ < q₂),
      let a : ℝ := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
      let b : ℝ := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
      let hscale : (M : ℝ) / (N : ℝ) ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hM.ne')
          (Nat.cast_ne_zero.mpr hN.ne')
      let E :=
        bourgainScaledOsculatingPhaseContinuousLinearEquiv
          hscale (sqrt_natCast_div_pos hN hq₁)
            (sqrt_natCast_div_lt hN hq)
      let X := bourgainIndependentParabolaNaturalScale M
      let δ :=
        bourgainOsculatingFrequencyPerturbationSize X
          ‖(E.symm :
            BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖
          a b ((M : ℝ) / (N : ℝ))
      δ ≤ 1 / 24 →
      ∀ y : BourgainPhaseSpace,
        (∫⁻ z in bourgainTranslatedOsculatingFundamentalCell
            M ((M : ℝ) / (N : ℝ)) a b y,
          ENNReal.ofReal
            (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) z‖ ^
                  (6 : ℕ) *
              ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) z‖ ^
                (6 : ℕ))) ≤
          ENNReal.ofReal
              |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| *
            ENNReal.ofReal ((M : ℝ) ^ (6 : ℕ)) *
            ENNReal.ofReal
              (C * (M : ℝ) ^ ε * (M : ℝ) ^ (3 : ℕ) *
                (M : ℝ) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hcell⟩ :=
    setLIntegral_bourgainSquareRootExactLocalSum_translatedCell_gaussian
      hε
  refine ⟨C, hC, ?_⟩
  intro N M q₁ q₂ hN hM hq₁ hq
  dsimp only
  intro hsmall y
  have hbound :=
    hcell M hM
      (show (0 : ℝ) < N by exact_mod_cast hN)
      (sqrt_natCast_div_pos hN hq₁)
      (sqrt_natCast_div_lt hN hq)
      hsmall
      (fun _ : Fin M => (1 : ℂ))
      (fun _ : Fin M => (1 : ℂ)) y
  simpa only [bourgainA6PhysicalBlockSum_eq_exactLocalSum,
    bourgainA6BlockPhaseDeterminant, norm_one, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using hbound

/-- Real power arithmetic for the sharp Gaussian cell main term. -/
theorem bourgainA6GaussianSharpCellMainTerm_le
    {N M q₁ q₂ : ℕ} {C ε : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hC : 0 ≤ C)
    (hq₁ : 0 < q₁) (hq : q₁ + M ≤ q₂) (hq₂N : q₂ ≤ N) :
    |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| *
        (M : ℝ) ^ (6 : ℕ) *
        (C * (M : ℝ) ^ ε * (M : ℝ) ^ (3 : ℕ) *
          (M : ℝ) ^ (3 : ℕ)) ≤
      (512 / 3 : ℝ) * C *
        (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (2 + ε) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hJ :=
    abs_inv_bourgainA6BlockPhaseDeterminant_le
      hN hM hq₁ hq hq₂N
  have hmass :
      0 ≤ (M : ℝ) ^ (6 : ℕ) *
        (C * (M : ℝ) ^ ε * (M : ℝ) ^ (3 : ℕ) *
          (M : ℝ) ^ (3 : ℕ)) := by
    positivity
  have hpow :
      (M : ℝ) ^ (2 + ε) =
        (M : ℝ) ^ (2 : ℕ) * (M : ℝ) ^ ε := by
    rw [Real.rpow_add hMr, Real.rpow_two]
  calc
    |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| *
        (M : ℝ) ^ (6 : ℕ) *
        (C * (M : ℝ) ^ ε * (M : ℝ) ^ (3 : ℕ) *
          (M : ℝ) ^ (3 : ℕ)) =
      |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| *
        ((M : ℝ) ^ (6 : ℕ) *
          (C * (M : ℝ) ^ ε * (M : ℝ) ^ (3 : ℕ) *
            (M : ℝ) ^ (3 : ℕ))) := by ring
    _ ≤ ((512 / 3 : ℝ) * ((N : ℝ) / (M : ℝ)) ^ (10 : ℕ)) *
        ((M : ℝ) ^ (6 : ℕ) *
          (C * (M : ℝ) ^ ε * (M : ℝ) ^ (3 : ℕ) *
            (M : ℝ) ^ (3 : ℕ))) :=
      mul_le_mul_of_nonneg_right hJ hmass
    _ = (512 / 3 : ℝ) * C *
        (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (2 + ε) := by
      rw [hpow]
      field_simp

/-- Clean sharp translated-cell bound for separated unit A₆ blocks. -/
theorem setLIntegral_bourgainA6PhysicalBlockSum_translatedCell_gaussian_power
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M q₁ q₂ : ℕ) (hN : 0 < N) (hM : 0 < M)
        (hq₁ : 0 < q₁) (hq : q₁ + M ≤ q₂) (hq₂N : q₂ ≤ N),
      let a : ℝ := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
      let b : ℝ := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
      let hq' : q₁ < q₂ := by omega
      let hscale : (M : ℝ) / (N : ℝ) ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hM.ne')
          (Nat.cast_ne_zero.mpr hN.ne')
      let E :=
        bourgainScaledOsculatingPhaseContinuousLinearEquiv
          hscale (sqrt_natCast_div_pos hN hq₁)
            (sqrt_natCast_div_lt hN hq')
      let X := bourgainIndependentParabolaNaturalScale M
      let δ :=
        bourgainOsculatingFrequencyPerturbationSize X
          ‖(E.symm :
            BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖
          a b ((M : ℝ) / (N : ℝ))
      δ ≤ 1 / 24 →
      ∀ y : BourgainPhaseSpace,
        (∫⁻ z in bourgainTranslatedOsculatingFundamentalCell
            M ((M : ℝ) / (N : ℝ)) a b y,
          ENNReal.ofReal
            (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) z‖ ^
                  (6 : ℕ) *
              ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) z‖ ^
                (6 : ℕ))) ≤
          ENNReal.ofReal
            (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (2 + ε)) := by
  obtain ⟨C₀, hC₀, hcell⟩ :=
    setLIntegral_bourgainA6PhysicalBlockSum_translatedCell_gaussian hε
  refine ⟨(512 / 3 : ℝ) * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro N M q₁ q₂ hN hM hq₁ hq hq₂N
  dsimp only
  intro hsmall y
  have hq' : q₁ < q₂ := by omega
  have hraw := hcell N M q₁ q₂ hN hM hq₁ hq' hsmall y
  calc
    (∫⁻ z in bourgainTranslatedOsculatingFundamentalCell
        M ((M : ℝ) / (N : ℝ))
          (Real.sqrt ((q₁ : ℝ) / (N : ℝ)))
          (Real.sqrt ((q₂ : ℝ) / (N : ℝ))) y,
      ENNReal.ofReal
        (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) z‖ ^
              (6 : ℕ) *
          ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) z‖ ^
            (6 : ℕ))) ≤
      ENNReal.ofReal
          |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| *
        ENNReal.ofReal ((M : ℝ) ^ (6 : ℕ)) *
        ENNReal.ofReal
          (C₀ * (M : ℝ) ^ ε * (M : ℝ) ^ (3 : ℕ) *
            (M : ℝ) ^ (3 : ℕ)) := hraw
    _ = ENNReal.ofReal
        (|(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| *
          (M : ℝ) ^ (6 : ℕ) *
          (C₀ * (M : ℝ) ^ ε * (M : ℝ) ^ (3 : ℕ) *
            (M : ℝ) ^ (3 : ℕ))) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal
        (((512 / 3 : ℝ) * C₀) *
          (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (2 + ε)) := by
      apply ENNReal.ofReal_le_ofReal
      exact bourgainA6GaussianSharpCellMainTerm_le
        hN hM hC₀.le hq₁ hq hq₂N

end

end RHTower
