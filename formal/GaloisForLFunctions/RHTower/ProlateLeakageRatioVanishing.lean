import GaloisForLFunctions.RHTower.ProlateCentreRatioTransfer
import GaloisForLFunctions.RHTower.ProlateSharpMassRatio

/-!
# The leakage ratio of two rungs vanishes

The sharp two-sided leakage estimate has absolute constants on both sides,

```text
F/1728/L_k / (sqrt c · R_k(0)²)  ≤  d_k  ≤  4M/L_k / (sqrt c · R_k(0)²) ,
```

so the leakage quotient of two rungs is the quotient of their squared centre amplitudes, up to
constants depending only on the two indices.  With the centre comparison `R_n(0)² ≤ C/sqrt c · R_m(0)²`
this gives

```text
d_m  ≤  (leakage ratio constant) / sqrt c · d_n ,
```

so the ratio vanishes for *adjacent* corpus indices, not only for the Fourier-even step.
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The constant of the vanishing leakage ratio. -/
def leakageRatioConst (m n : ℕ) : ℝ :=
  4 * radialProlateExteriorMassConstant * centreRatioConst m n * 1728 * sharpInteriorLimit n
    / (sharpInteriorLimit m * besselEnergyFloor)

theorem leakageRatioConst_nonneg (m n : ℕ) : 0 ≤ leakageRatioConst m n := by
  have hM : (0 : ℝ) ≤ radialProlateExteriorMassConstant := radialProlateExteriorMassConstant_nonneg
  have hC : 0 ≤ centreRatioConst m n := centreRatioConst_nonneg m n
  have hLn : 0 < sharpInteriorLimit n := sharpInteriorLimit_pos n
  have hLm : 0 < sharpInteriorLimit m := sharpInteriorLimit_pos m
  have hF : 0 < besselEnergyFloor := besselEnergyFloor_pos
  rw [leakageRatioConst]
  positivity

/-- **The leakage of the lower rung is `O(c^{-1/2})` times that of the higher one.** -/
theorem eventually_signedLeakage_le_div_sqrt (m n : ℕ) (hmn : m < n) :
    ∀ᶠ a : ℝ in atTop,
      evenProlateSignedLeakage a m
        ≤ leakageRatioConst m n / prolateRatioScale a
          * evenProlateSignedLeakage a n := by
  have hM : (0 : ℝ) ≤ radialProlateExteriorMassConstant := radialProlateExteriorMassConstant_nonneg
  have hLn : 0 < sharpInteriorLimit n := sharpInteriorLimit_pos n
  have hLm : 0 < sharpInteriorLimit m := sharpInteriorLimit_pos m
  have hF : 0 < besselEnergyFloor := besselEnergyFloor_pos
  filter_upwards [eventually_signedLeakage_sharp_two_sided m,
    eventually_signedLeakage_sharp_two_sided n,
    eventually_centre_sq_ratio_le_div_sqrt m n hmn,
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ)]
    with a hm hn hcentre hc1
  obtain ⟨hRm0, _, hmup⟩ := hm
  obtain ⟨hRn0, hnlow, _⟩ := hn
  have hc0 : (0 : ℝ) < signedModeRadialBandwidth a := by linarith
  set sc : ℝ := Real.sqrt (signedModeRadialBandwidth a) with hscdef
  have hsc : 0 < sc := Real.sqrt_pos.2 hc0
  set S : ℝ := prolateRatioScale a with hSdef
  have hS : 0 < S := prolateRatioScale_pos hc0
  set Rm : ℝ := (signedModeRadialData a m).R 0 with hRm
  set Rn : ℝ := (signedModeRadialData a n).R 0 with hRn
  have hRm2 : 0 < Rm ^ 2 := by positivity
  have hRn2 : 0 < Rn ^ 2 := by positivity
  have hCnn : 0 ≤ centreRatioConst m n := centreRatioConst_nonneg m n
  -- the centre comparison, in reciprocal form
  have hrecip : 1 / Rm ^ 2 ≤ centreRatioConst m n / S / Rn ^ 2 := by
    rcases eq_or_lt_of_le hCnn with hC0 | hCpos
    · exfalso
      rw [← hC0] at hcentre
      simp only [zero_div, zero_mul] at hcentre
      linarith [hRn2, hcentre]
    · rw [div_le_div_iff₀ hRm2 (by positivity)]
      have hstep : Rn ^ 2 * 1 ≤ centreRatioConst m n / S * Rm ^ 2 := by simpa using hcentre
      nlinarith [hstep]
  -- the leakage of the higher rung, from below
  have hinv : 1 / (sc * Rn ^ 2)
      ≤ 1728 * sharpInteriorLimit n / besselEnergyFloor * evenProlateSignedLeakage a n := by
    have hval : besselEnergyFloor / 1728 / sharpInteriorLimit n / (sc * Rn ^ 2)
        = besselEnergyFloor / (1728 * sharpInteriorLimit n) * (1 / (sc * Rn ^ 2)) := by
      field_simp
    rw [hval] at hnlow
    have hcoef : (0 : ℝ) < besselEnergyFloor / (1728 * sharpInteriorLimit n) := by positivity
    rw [← le_div_iff₀' hcoef] at hnlow
    calc 1 / (sc * Rn ^ 2)
        ≤ evenProlateSignedLeakage a n / (besselEnergyFloor / (1728 * sharpInteriorLimit n)) :=
          hnlow
      _ = 1728 * sharpInteriorLimit n / besselEnergyFloor * evenProlateSignedLeakage a n := by
          field_simp
  -- chain the three estimates
  have hmup' : evenProlateSignedLeakage a m
      ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m
        * (1 / sc) * (1 / Rm ^ 2) := by
    refine le_trans hmup (le_of_eq ?_)
    field_simp
  have hcoefm : (0 : ℝ) ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m
      * (1 / sc) := by positivity
  have hstep1 : evenProlateSignedLeakage a m
      ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m * (1 / sc)
        * (centreRatioConst m n / S / Rn ^ 2) :=
    le_trans hmup' (mul_le_mul_of_nonneg_left hrecip hcoefm)
  have hstep2 : 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m * (1 / sc)
        * (centreRatioConst m n / S / Rn ^ 2)
      = 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m * centreRatioConst m n
        * (1 / S) * (1 / (sc * Rn ^ 2)) := by
    field_simp
  have hcoef2 : (0 : ℝ) ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m
      * centreRatioConst m n * (1 / S) := by positivity
  have hstep3 : evenProlateSignedLeakage a m
      ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m * centreRatioConst m n
        * (1 / S)
        * (1728 * sharpInteriorLimit n / besselEnergyFloor * evenProlateSignedLeakage a n) := by
    rw [hstep2] at hstep1
    exact le_trans hstep1 (mul_le_mul_of_nonneg_left hinv hcoef2)
  refine le_trans hstep3 (le_of_eq ?_)
  rw [leakageRatioConst]
  field_simp

end RHTower

end
