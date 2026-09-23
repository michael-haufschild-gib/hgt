import GaloisForLFunctions.RHTower.XiShiftedHardEdgeNyquistNullForm

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem routeUHardEdgeAliasPeriod_fineIndex (k : ℕ) :
    routeUHardEdgeAliasPeriod (routeUDyadicFineIndex k : ℝ) =
      2 * routeUHardEdgeAliasPeriod (k : ℝ) := by
  rw [routeUHardEdgeAliasPeriod, routeUHardEdgeAliasPeriod,
    routeUHardEdgeMass_fineIndex]
  ring

theorem routeUComplexHardEdgePeriodizationAt_add_aliasPeriod
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ) :
    routeUComplexHardEdgePeriodizationAt n f r
        (z + (routeUHardEdgeAliasPeriod r : ℂ)) =
      routeUComplexHardEdgePeriodizationAt n f r z := by
  have h := routeUComplexHardEdgePeriodizationAt_sub_aliasPeriod
    n f r (z + (routeUHardEdgeAliasPeriod r : ℂ))
  simpa only [add_sub_cancel_right] using h.symm

theorem routeUXiComplexHardEdgeSample_eq_periodizationAt
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) :
    routeUXiComplexHardEdgeSample n f r q =
      routeUComplexHardEdgePeriodizationAt n f r
        (routeUComplexHardEdgePhase r (xiSpectralPoint q)) := by
  rfl

theorem routeUDyadicXiNyquistCurrent_eq_fine_mul_complementaryAlias
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) :
    routeUDyadicXiNyquistCurrent n f k q =
      routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q *
        (routeUComplexHardEdgePeriodizationAt n f (k : ℝ)
            (routeUDyadicFinePhase k (xiSpectralPoint q)) -
          routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q) := by
  rw [routeUDyadicXiNyquistCurrent, routeUDyadicOddSample,
    routeUDyadicEvenSample]
  ring

theorem norm_routeUComplexHardEdgePeriodizationAt_le_uniform
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ)
    (hzIm : |z.im| ≤ 1)
    (hzRe : |z.re| ≤ routeUHardEdgeAliasPeriod r / 2) :
    ‖routeUComplexHardEdgePeriodizationAt n f r z‖ ≤
      routeUComplexTiltUniformDecay n f 0 +
        routeUComplexHardEdgeUniformAliasTailConstant n f 1 := by
  let B : ℝ := routeUComplexTiltUniformDecay n f 0
  let D : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 1
  let L : ℝ := routeUHardEdgeAliasPeriod r
  have hB : 0 ≤ B := routeUComplexTiltUniformDecay_nonneg n f 0
  have hD : 0 ≤ D := routeUComplexHardEdgeUniformAliasTailConstant_nonneg n f 1
  have hL : 1 ≤ L := one_le_routeUHardEdgeAliasPeriod r
  have hcentral : ‖routeUComplexPositiveFourierExtension n f z‖ ≤ B := by
    simpa only [B, pow_zero, Nat.mul_zero, one_mul] using
      routeUComplexPositiveFourierExtension_uniform_decay n f hzIm 0
  have htail : ‖routeUComplexHardEdgeAliasTail n f r z‖ ≤ D / L ^ (4 : ℕ) := by
    simpa only [D, L,
      GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent] using
      norm_routeUComplexHardEdgeAliasTail_uniform_le n f r z hzIm hzRe 1
  rw [routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail n f r z hzRe]
  calc
    ‖routeUComplexPositiveFourierExtension n f z +
        routeUComplexHardEdgeAliasTail n f r z‖ ≤
        ‖routeUComplexPositiveFourierExtension n f z‖ +
          ‖routeUComplexHardEdgeAliasTail n f r z‖ := norm_add_le _ _
    _ ≤ B + D / L ^ (4 : ℕ) := add_le_add hcentral htail
    _ ≤ B + D := by
      gcongr
      exact div_le_self hD (one_le_pow₀ hL)
    _ = routeUComplexTiltUniformDecay n f 0 +
        routeUComplexHardEdgeUniformAliasTailConstant n f 1 := rfl

theorem norm_routeUComplexPositiveFourierExtension_outer_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ)
    (hzIm : |z.im| ≤ 1)
    (hzOuter : routeUHardEdgeAliasPeriod r / 2 ≤ |z.re|) :
    ‖routeUComplexPositiveFourierExtension n f z‖ ≤
      routeUComplexTiltUniformDecay n f 2 * (4 * Real.pi) ^ (4 : ℕ) /
        routeUHardEdgeAliasPeriod r ^ (4 : ℕ) := by
  let C : ℝ := routeUComplexTiltUniformDecay n f 2
  let L : ℝ := routeUHardEdgeAliasPeriod r
  let w : ℝ := -z.re / (2 * Real.pi)
  have hC : 0 ≤ C := routeUComplexTiltUniformDecay_nonneg n f 2
  have hL : 0 < L := routeUHardEdgeAliasPeriod_pos r
  have hwabs : |w| = |z.re| / (2 * Real.pi) := by
    dsimp only [w]
    rw [abs_div, abs_neg, abs_of_pos (mul_pos two_pos Real.pi_pos)]
  have hfreqLower : L / (4 * Real.pi) ≤ |w| := by
    rw [hwabs]
    calc
      L / (4 * Real.pi) = (L / 2) / (2 * Real.pi) := by ring
      _ ≤ |z.re| / (2 * Real.pi) := by gcongr
  have hkgLower : L / (4 * Real.pi) ≤ kgFreq w :=
    hfreqLower.trans (abs_le_kgFreq_real w)
  have hdecay :
      kgFreq w ^ (4 : ℕ) * ‖routeUComplexPositiveFourierExtension n f z‖ ≤ C := by
    simpa only [w, C] using
      routeUComplexPositiveFourierExtension_uniform_decay n f hzIm 2
  have hnorm :
      ‖routeUComplexPositiveFourierExtension n f z‖ ≤ C / kgFreq w ^ (4 : ℕ) := by
    apply (le_div_iff₀ (pow_pos (kgFreq_pos w) 4)).2
    simpa only [mul_comm] using hdecay
  have hden : C / kgFreq w ^ (4 : ℕ) ≤ C / (L / (4 * Real.pi)) ^ (4 : ℕ) := by
    gcongr
  calc
    ‖routeUComplexPositiveFourierExtension n f z‖ ≤ C / kgFreq w ^ (4 : ℕ) := hnorm
    _ ≤ C / (L / (4 * Real.pi)) ^ (4 : ℕ) := hden
    _ = C * (4 * Real.pi) ^ (4 : ℕ) / L ^ (4 : ℕ) := by
      field_simp [hL.ne', Real.pi_ne_zero]
    _ = routeUComplexTiltUniformDecay n f 2 * (4 * Real.pi) ^ (4 : ℕ) /
        routeUHardEdgeAliasPeriod r ^ (4 : ℕ) := rfl

/-- Divisor-independent constant controlling the complementary dyadic alias current. -/
def routeUDyadicXiNyquistUniformConstant
    (n : ℕ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  2 *
    (routeUComplexTiltUniformDecay n f 0 +
      routeUComplexHardEdgeUniformAliasTailConstant n f 1) *
    (routeUComplexHardEdgeUniformAliasTailConstant n f 1 +
      routeUComplexTiltUniformDecay n f 2 * (4 * Real.pi) ^ (4 : ℕ))

theorem routeUDyadicXiNyquistUniformConstant_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    0 ≤ routeUDyadicXiNyquistUniformConstant n f := by
  rw [routeUDyadicXiNyquistUniformConstant]
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (add_nonneg
        (routeUComplexTiltUniformDecay_nonneg n f 0)
        (routeUComplexHardEdgeUniformAliasTailConstant_nonneg n f 1)))
    (add_nonneg
      (routeUComplexHardEdgeUniformAliasTailConstant_nonneg n f 1)
      (mul_nonneg (routeUComplexTiltUniformDecay_nonneg n f 2)
        (pow_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) 4)))

theorem norm_routeUXiComplexHardEdgeSample_fine_le_uniform
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) :
    ‖routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q‖ ≤
      routeUComplexTiltUniformDecay n f 0 +
        routeUComplexHardEdgeUniformAliasTailConstant n f 1 := by
  rw [routeUXiComplexHardEdgeSample_eq_periodizationAt]
  exact norm_routeUComplexHardEdgePeriodizationAt_le_uniform n f
    (routeUDyadicFineIndex k : ℝ)
    (routeUDyadicFinePhase k (xiSpectralPoint q))
    (by
      simpa only [routeUDyadicFinePhase] using
        (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one
          (routeUDyadicFineIndex k : ℝ) q).le)
    (by
      simpa only [routeUDyadicFinePhase] using
        abs_routeUComplexHardEdgePhase_re_le_half_aliasPeriod
          (routeUDyadicFineIndex k : ℝ) (xiSpectralPoint q))

theorem norm_routeUXiComplexHardEdgeSample_fine_outer_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy)
    (hOuter : routeUHardEdgeAliasPeriod (k : ℝ) / 2 ≤
      |(routeUDyadicFinePhase k (xiSpectralPoint q)).re|) :
    ‖routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q‖ ≤
      (routeUComplexHardEdgeUniformAliasTailConstant n f 1 +
        routeUComplexTiltUniformDecay n f 2 * (4 * Real.pi) ^ (4 : ℕ)) /
          routeUHardEdgeAliasPeriod (k : ℝ) ^ (4 : ℕ) := by
  let z : ℂ := routeUDyadicFinePhase k (xiSpectralPoint q)
  let L : ℝ := routeUHardEdgeAliasPeriod (k : ℝ)
  let D : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 1
  let C : ℝ := routeUComplexTiltUniformDecay n f 2
  have hzIm : |z.im| ≤ 1 := by
    simpa only [z, routeUDyadicFinePhase] using
      (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one
        (routeUDyadicFineIndex k : ℝ) q).le
  have hzFine : |z.re| ≤
      routeUHardEdgeAliasPeriod (routeUDyadicFineIndex k : ℝ) / 2 := by
    simpa only [z, routeUDyadicFinePhase] using
      abs_routeUComplexHardEdgePhase_re_le_half_aliasPeriod
        (routeUDyadicFineIndex k : ℝ) (xiSpectralPoint q)
  have hD : 0 ≤ D := routeUComplexHardEdgeUniformAliasTailConstant_nonneg n f 1
  have hL : 0 < L := routeUHardEdgeAliasPeriod_pos (k : ℝ)
  have hcentral : ‖routeUComplexPositiveFourierExtension n f z‖ ≤
      C * (4 * Real.pi) ^ (4 : ℕ) / L ^ (4 : ℕ) := by
    simpa only [C, L, z] using
      norm_routeUComplexPositiveFourierExtension_outer_le n f (k : ℝ) z hzIm
        (by simpa only [L, z] using hOuter)
  have htailRaw :
      ‖routeUComplexHardEdgeAliasTail n f (routeUDyadicFineIndex k : ℝ) z‖ ≤
        D / routeUHardEdgeAliasPeriod (routeUDyadicFineIndex k : ℝ) ^ (4 : ℕ) := by
    simpa only [D,
      GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent] using
      norm_routeUComplexHardEdgeAliasTail_uniform_le n f
        (routeUDyadicFineIndex k : ℝ) z hzIm hzFine 1
  have htail :
      ‖routeUComplexHardEdgeAliasTail n f (routeUDyadicFineIndex k : ℝ) z‖ ≤
        D / L ^ (4 : ℕ) := by
    refine htailRaw.trans ?_
    rw [routeUHardEdgeAliasPeriod_fineIndex]
    gcongr
    nlinarith
  rw [routeUXiComplexHardEdgeSample_eq_periodizationAt]
  change ‖routeUComplexHardEdgePeriodizationAt n f
      (routeUDyadicFineIndex k : ℝ) z‖ ≤ (D + C * (4 * Real.pi) ^ (4 : ℕ)) / L ^ (4 : ℕ)
  rw [routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail
    n f (routeUDyadicFineIndex k : ℝ) z hzFine]
  calc
    ‖routeUComplexPositiveFourierExtension n f z +
        routeUComplexHardEdgeAliasTail n f (routeUDyadicFineIndex k : ℝ) z‖ ≤
      ‖routeUComplexPositiveFourierExtension n f z‖ +
        ‖routeUComplexHardEdgeAliasTail n f (routeUDyadicFineIndex k : ℝ) z‖ :=
          norm_add_le _ _
    _ ≤ C * (4 * Real.pi) ^ (4 : ℕ) / L ^ (4 : ℕ) + D / L ^ (4 : ℕ) :=
      add_le_add hcentral htail
    _ = (D + C * (4 * Real.pi) ^ (4 : ℕ)) / L ^ (4 : ℕ) := by ring

theorem norm_routeUDyadicXiComplementaryAlias_inner_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy)
    (hInner : |(routeUDyadicFinePhase k (xiSpectralPoint q)).re| ≤
      routeUHardEdgeAliasPeriod (k : ℝ) / 2) :
    ‖routeUComplexHardEdgePeriodizationAt n f (k : ℝ)
          (routeUDyadicFinePhase k (xiSpectralPoint q)) -
        routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q‖ ≤
      2 * routeUComplexHardEdgeUniformAliasTailConstant n f 1 /
        routeUHardEdgeAliasPeriod (k : ℝ) ^ (4 : ℕ) := by
  let z : ℂ := routeUDyadicFinePhase k (xiSpectralPoint q)
  let L : ℝ := routeUHardEdgeAliasPeriod (k : ℝ)
  let D : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 1
  let Tcoarse : ℂ := routeUComplexHardEdgeAliasTail n f (k : ℝ) z
  let Tfine : ℂ :=
    routeUComplexHardEdgeAliasTail n f (routeUDyadicFineIndex k : ℝ) z
  have hzIm : |z.im| ≤ 1 := by
    simpa only [z, routeUDyadicFinePhase] using
      (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one
        (routeUDyadicFineIndex k : ℝ) q).le
  have hzFine : |z.re| ≤
      routeUHardEdgeAliasPeriod (routeUDyadicFineIndex k : ℝ) / 2 := by
    simpa only [z, routeUDyadicFinePhase] using
      abs_routeUComplexHardEdgePhase_re_le_half_aliasPeriod
        (routeUDyadicFineIndex k : ℝ) (xiSpectralPoint q)
  have hD : 0 ≤ D := routeUComplexHardEdgeUniformAliasTailConstant_nonneg n f 1
  have hL : 0 < L := routeUHardEdgeAliasPeriod_pos (k : ℝ)
  have hTcoarse : ‖Tcoarse‖ ≤ D / L ^ (4 : ℕ) := by
    simpa only [Tcoarse, D, L,
      GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent,
      z] using
      norm_routeUComplexHardEdgeAliasTail_uniform_le n f (k : ℝ) z hzIm
        (by simpa only [z, L] using hInner) 1
  have hTfineRaw : ‖Tfine‖ ≤
      D / routeUHardEdgeAliasPeriod (routeUDyadicFineIndex k : ℝ) ^ (4 : ℕ) := by
    simpa only [Tfine, D,
      GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent] using
      norm_routeUComplexHardEdgeAliasTail_uniform_le n f
        (routeUDyadicFineIndex k : ℝ) z hzIm hzFine 1
  have hTfine : ‖Tfine‖ ≤ D / L ^ (4 : ℕ) := by
    refine hTfineRaw.trans ?_
    rw [routeUHardEdgeAliasPeriod_fineIndex]
    gcongr
    nlinarith
  rw [routeUXiComplexHardEdgeSample_eq_periodizationAt]
  change ‖routeUComplexHardEdgePeriodizationAt n f (k : ℝ) z -
      routeUComplexHardEdgePeriodizationAt n f
        (routeUDyadicFineIndex k : ℝ) z‖ ≤ 2 * D / L ^ (4 : ℕ)
  rw [routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail
      n f (k : ℝ) z (by simpa only [z, L] using hInner),
    routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail
      n f (routeUDyadicFineIndex k : ℝ) z hzFine]
  change ‖(routeUComplexPositiveFourierExtension n f z + Tcoarse) -
      (routeUComplexPositiveFourierExtension n f z + Tfine)‖ ≤ 2 * D / L ^ (4 : ℕ)
  rw [show (routeUComplexPositiveFourierExtension n f z + Tcoarse) -
      (routeUComplexPositiveFourierExtension n f z + Tfine) =
        Tcoarse - Tfine by ring]
  calc
    ‖Tcoarse - Tfine‖ ≤ ‖Tcoarse‖ + ‖Tfine‖ := norm_sub_le _ _
    _ ≤ D / L ^ (4 : ℕ) + D / L ^ (4 : ℕ) := add_le_add hTcoarse hTfine
    _ = 2 * D / L ^ (4 : ℕ) := by ring

theorem norm_routeUComplexHardEdgePeriodizationAt_coarse_le_uniform
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) :
    ‖routeUComplexHardEdgePeriodizationAt n f (k : ℝ)
        (routeUDyadicFinePhase k (xiSpectralPoint q))‖ ≤
      routeUComplexTiltUniformDecay n f 0 +
        routeUComplexHardEdgeUniformAliasTailConstant n f 1 := by
  let z : ℂ := routeUDyadicFinePhase k (xiSpectralPoint q)
  let L : ℝ := routeUHardEdgeAliasPeriod (k : ℝ)
  have hzIm : |z.im| ≤ 1 := by
    simpa only [z, routeUDyadicFinePhase] using
      (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one
        (routeUDyadicFineIndex k : ℝ) q).le
  have hzFine : |z.re| ≤
      routeUHardEdgeAliasPeriod (routeUDyadicFineIndex k : ℝ) / 2 := by
    simpa only [z, routeUDyadicFinePhase] using
      abs_routeUComplexHardEdgePhase_re_le_half_aliasPeriod
        (routeUDyadicFineIndex k : ℝ) (xiSpectralPoint q)
  have hL : 0 < L := routeUHardEdgeAliasPeriod_pos (k : ℝ)
  have hzL : |z.re| ≤ L := by
    rw [routeUHardEdgeAliasPeriod_fineIndex] at hzFine
    nlinarith [hzFine]
  by_cases hInner : |z.re| ≤ L / 2
  · exact norm_routeUComplexHardEdgePeriodizationAt_le_uniform n f (k : ℝ) z
      hzIm (by simpa only [L] using hInner)
  · have hOuter : L / 2 ≤ |z.re| := le_of_not_ge hInner
    by_cases hz0 : 0 ≤ z.re
    · have hzLower : L / 2 ≤ z.re := by
        simpa only [abs_of_nonneg hz0] using hOuter
      have hzFold : |(z - (L : ℂ)).re| ≤ L / 2 := by
        rw [abs_le]
        constructor
        · rw [Complex.sub_re, Complex.ofReal_re]
          linarith
        · rw [Complex.sub_re, Complex.ofReal_re]
          have hzUpper : z.re ≤ L := by simpa [abs_of_nonneg hz0] using hzL
          linarith
      rw [← routeUComplexHardEdgePeriodizationAt_sub_aliasPeriod n f (k : ℝ) z]
      exact norm_routeUComplexHardEdgePeriodizationAt_le_uniform n f (k : ℝ)
        (z - (L : ℂ)) (by simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero])
        (by simpa only [L] using hzFold)
    · have hzneg : z.re < 0 := lt_of_not_ge hz0
      have hzUpper : z.re ≤ -(L / 2) := by
        have habs : |z.re| = -z.re := abs_of_nonpos hzneg.le
        rw [habs] at hOuter
        linarith
      have hzFold : |(z + (L : ℂ)).re| ≤ L / 2 := by
        rw [abs_le]
        constructor
        · rw [Complex.add_re, Complex.ofReal_re]
          have hzLower : -L ≤ z.re := (abs_le.mp hzL).1
          linarith
        · rw [Complex.add_re, Complex.ofReal_re]
          linarith
      rw [← routeUComplexHardEdgePeriodizationAt_add_aliasPeriod n f (k : ℝ) z]
      exact norm_routeUComplexHardEdgePeriodizationAt_le_uniform n f (k : ℝ)
        (z + (L : ℂ)) (by simpa only [Complex.add_im, Complex.ofReal_im, add_zero])
        (by simpa only [L] using hzFold)

/-- Uniform `L⁻⁴` bound for the signed complementary dyadic alias current at every Xi divisor. -/
theorem norm_routeUDyadicXiNyquistCurrent_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) :
    ‖routeUDyadicXiNyquistCurrent n f k q‖ ≤
      routeUDyadicXiNyquistUniformConstant n f /
        routeUHardEdgeAliasPeriod (k : ℝ) ^ (4 : ℕ) := by
  let z : ℂ := routeUDyadicFinePhase k (xiSpectralPoint q)
  let L : ℝ := routeUHardEdgeAliasPeriod (k : ℝ)
  let B : ℝ := routeUComplexTiltUniformDecay n f 0
  let D : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 1
  let C : ℝ := routeUComplexTiltUniformDecay n f 2 * (4 * Real.pi) ^ (4 : ℕ)
  have hB : 0 ≤ B := routeUComplexTiltUniformDecay_nonneg n f 0
  have hD : 0 ≤ D := routeUComplexHardEdgeUniformAliasTailConstant_nonneg n f 1
  have hC : 0 ≤ C := mul_nonneg
    (routeUComplexTiltUniformDecay_nonneg n f 2)
    (pow_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) 4)
  rw [routeUDyadicXiNyquistCurrent_eq_fine_mul_complementaryAlias, norm_mul]
  by_cases hInner : |z.re| ≤ L / 2
  · have hFine := norm_routeUXiComplexHardEdgeSample_fine_le_uniform n f k q
    have hDefect := norm_routeUDyadicXiComplementaryAlias_inner_le
      n f k q (by simpa only [z, L] using hInner)
    change ‖routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q‖ *
        ‖routeUComplexHardEdgePeriodizationAt n f (k : ℝ) z -
          routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q‖ ≤
      routeUDyadicXiNyquistUniformConstant n f / L ^ (4 : ℕ)
    calc
      _ ≤ (B + D) * (2 * D / L ^ (4 : ℕ)) := by
        exact mul_le_mul (by simpa only [B, D] using hFine)
          (by simpa only [z, L, D] using hDefect)
          (norm_nonneg _) (add_nonneg hB hD)
      _ ≤ 2 * (B + D) * (D + C) / L ^ (4 : ℕ) := by
        have hBD : 0 ≤ B + D := add_nonneg hB hD
        have hDC : D ≤ D + C := le_add_of_nonneg_right hC
        calc
          (B + D) * (2 * D / L ^ (4 : ℕ)) =
              (2 * (B + D) * D) / L ^ (4 : ℕ) := by ring
          _ ≤ (2 * (B + D) * (D + C)) / L ^ (4 : ℕ) := by gcongr
      _ = routeUDyadicXiNyquistUniformConstant n f / L ^ (4 : ℕ) := by
        rw [routeUDyadicXiNyquistUniformConstant]
  · have hOuter : L / 2 ≤ |z.re| := le_of_not_ge hInner
    have hFineOuter := norm_routeUXiComplexHardEdgeSample_fine_outer_le
      n f k q (by simpa only [z, L] using hOuter)
    have hCoarse := norm_routeUComplexHardEdgePeriodizationAt_coarse_le_uniform
      n f k q
    have hFineUniform := norm_routeUXiComplexHardEdgeSample_fine_le_uniform n f k q
    have hDefect :
        ‖routeUComplexHardEdgePeriodizationAt n f (k : ℝ) z -
          routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q‖ ≤
        2 * (B + D) := by
      calc
        _ ≤ ‖routeUComplexHardEdgePeriodizationAt n f (k : ℝ) z‖ +
            ‖routeUXiComplexHardEdgeSample n f
              (routeUDyadicFineIndex k : ℝ) q‖ := norm_sub_le _ _
        _ ≤ (B + D) + (B + D) :=
          add_le_add (by simpa only [z, B, D] using hCoarse)
            (by simpa only [B, D] using hFineUniform)
        _ = 2 * (B + D) := by ring
    change ‖routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q‖ *
        ‖routeUComplexHardEdgePeriodizationAt n f (k : ℝ) z -
          routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q‖ ≤
      routeUDyadicXiNyquistUniformConstant n f / L ^ (4 : ℕ)
    calc
      _ ≤ ((D + C) / L ^ (4 : ℕ)) * (2 * (B + D)) := by
        exact mul_le_mul (by simpa only [z, L, D, C, add_comm] using hFineOuter)
          hDefect (norm_nonneg _) (by positivity)
      _ = 2 * (B + D) * (D + C) / L ^ (4 : ℕ) := by ring
      _ = routeUDyadicXiNyquistUniformConstant n f / L ^ (4 : ℕ) := by
        rw [routeUDyadicXiNyquistUniformConstant]

/-- Native shifted-resolvent weighting of the signed dyadic Nyquist current. -/
def routeUDyadicXiWeightedNyquistCurrent
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) : ℂ :=
  routeUXiHardEdgeResolventWeight (routeUDyadicFineIndex k : ℝ) q *
    routeUDyadicXiNyquistCurrent n f k q

/-- Divisor-independent reciprocal-square coefficient for the weighted current. -/
def routeUDyadicXiWeightedNyquistMajorantCoefficient
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) : ℝ :=
  routeUHardEdgeMass (routeUDyadicFineIndex k : ℝ) ^ (2 : ℕ) *
      routeUDyadicXiNyquistUniformConstant n f /
    routeUHardEdgeAliasPeriod (k : ℝ) ^ (4 : ℕ)

theorem routeUDyadicXiWeightedNyquistMajorantCoefficient_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) :
    0 ≤ routeUDyadicXiWeightedNyquistMajorantCoefficient n f k := by
  rw [routeUDyadicXiWeightedNyquistMajorantCoefficient]
  exact div_nonneg
    (mul_nonneg (sq_nonneg _)
      (routeUDyadicXiNyquistUniformConstant_nonneg n f))
    (pow_nonneg (routeUHardEdgeAliasPeriod_pos (k : ℝ)).le 4)

theorem norm_routeUDyadicXiWeightedNyquistCurrent_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) :
    ‖routeUDyadicXiWeightedNyquistCurrent n f k q‖ ≤
      routeUDyadicXiWeightedNyquistMajorantCoefficient n f k *
        ‖xiZeroCopyReciprocalSquare q‖ := by
  rw [routeUDyadicXiWeightedNyquistCurrent, norm_mul]
  calc
    ‖routeUXiHardEdgeResolventWeight (routeUDyadicFineIndex k : ℝ) q‖ *
        ‖routeUDyadicXiNyquistCurrent n f k q‖ ≤
      (routeUHardEdgeMass (routeUDyadicFineIndex k : ℝ) ^ (2 : ℕ) *
          ‖xiZeroCopyReciprocalSquare q‖) *
        (routeUDyadicXiNyquistUniformConstant n f /
          routeUHardEdgeAliasPeriod (k : ℝ) ^ (4 : ℕ)) := by
      exact mul_le_mul
        (norm_routeUXiHardEdgeResolventWeight_le
          (routeUDyadicFineIndex k : ℝ) q)
        (norm_routeUDyadicXiNyquistCurrent_le n f k q)
        (norm_nonneg _) (by positivity)
    _ = routeUDyadicXiWeightedNyquistMajorantCoefficient n f k *
        ‖xiZeroCopyReciprocalSquare q‖ := by
      rw [routeUDyadicXiWeightedNyquistMajorantCoefficient]
      ring

theorem summable_routeUDyadicXiWeightedNyquistCurrent
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) :
    Summable (routeUDyadicXiWeightedNyquistCurrent n f k) := by
  apply Summable.of_norm_bounded
    ((summable_xiZeroCopyReciprocalSquare_pow 0).norm.mul_left
      (routeUDyadicXiWeightedNyquistMajorantCoefficient n f k))
  intro q
  simpa using norm_routeUDyadicXiWeightedNyquistCurrent_le n f k q

theorem norm_tsum_routeUDyadicXiWeightedNyquistCurrent_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) :
    ‖∑' q : XiZeroCopy, routeUDyadicXiWeightedNyquistCurrent n f k q‖ ≤
      routeUDyadicXiWeightedNyquistMajorantCoefficient n f k *
        ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ := by
  let A : ℝ := routeUDyadicXiWeightedNyquistMajorantCoefficient n f k
  have hCurrent := summable_routeUDyadicXiWeightedNyquistCurrent n f k
  have hBase : Summable (fun q : XiZeroCopy =>
      ‖xiZeroCopyReciprocalSquare q‖) := by
    simpa using (summable_xiZeroCopyReciprocalSquare_pow 0).norm
  have hMajor : Summable (fun q : XiZeroCopy =>
      A * ‖xiZeroCopyReciprocalSquare q‖) := hBase.mul_left A
  calc
    ‖∑' q : XiZeroCopy, routeUDyadicXiWeightedNyquistCurrent n f k q‖ ≤
        ∑' q : XiZeroCopy, ‖routeUDyadicXiWeightedNyquistCurrent n f k q‖ :=
      norm_tsum_le_tsum_norm hCurrent.norm
    _ ≤ ∑' q : XiZeroCopy, A * ‖xiZeroCopyReciprocalSquare q‖ :=
      hCurrent.norm.tsum_le_tsum
        (fun q => norm_routeUDyadicXiWeightedNyquistCurrent_le n f k q) hMajor
    _ = A * ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ := tsum_mul_left

theorem tendsto_routeUDyadicXiWeightedNyquistMajorantCoefficient_zero
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    Tendsto (routeUDyadicXiWeightedNyquistMajorantCoefficient n f)
      atTop (nhds 0) := by
  let K : ℝ := routeUDyadicXiNyquistUniformConstant n f
  have hmass : Tendsto (fun k : ℕ => 1 + (k : ℝ)) atTop atTop := by
    simpa only [add_comm] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hmassSq : Tendsto (fun k : ℕ => (1 + (k : ℝ)) ^ (2 : ℕ)) atTop atTop := by
    simpa only [pow_two] using hmass.atTop_mul_atTop₀ hmass
  have hden : Tendsto
      (fun k : ℕ => Real.pi ^ (4 : ℕ) * (1 + (k : ℝ)) ^ (2 : ℕ)) atTop atTop :=
    Tendsto.const_mul_atTop (pow_pos Real.pi_pos 4) hmassSq
  have hlim : Tendsto
      (fun k : ℕ => (4 * K) / (Real.pi ^ (4 : ℕ) * (1 + (k : ℝ)) ^ (2 : ℕ)))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  apply hlim.congr'
  filter_upwards with k
  rw [routeUDyadicXiWeightedNyquistMajorantCoefficient,
    routeUHardEdgeMass_fineIndex, routeUHardEdgeAliasPeriod,
    routeUHardEdgeMass]
  simp only [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
  change (4 * K) / (Real.pi ^ (4 : ℕ) * (1 + (k : ℝ)) ^ (2 : ℕ)) =
    (2 * (1 + (k : ℝ))) ^ (2 : ℕ) * K /
      (Real.pi * (1 + (k : ℝ))) ^ (4 : ℕ)
  field_simp [Real.pi_ne_zero, show (1 + (k : ℝ)) ≠ 0 by positivity]
  ring

/-- **Premise-free global Nyquist-current exchange.**

The complete Xi-divisor sum of the native shifted-resolvent-weighted complementary dyadic alias
current tends to zero.  No Riemann--von Mangoldt asymptotic or zero-location hypothesis is used. -/
theorem tendsto_tsum_routeUDyadicXiWeightedNyquistCurrent_zero
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    Tendsto
      (fun k : ℕ =>
        ∑' q : XiZeroCopy,
          routeUXiHardEdgeResolventWeight (routeUDyadicFineIndex k : ℝ) q *
            routeUDyadicXiNyquistCurrent n f k q)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let S : ℝ := ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖
  have hright : Tendsto
      (fun k : ℕ => routeUDyadicXiWeightedNyquistMajorantCoefficient n f k * S)
      atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_routeUDyadicXiWeightedNyquistMajorantCoefficient_zero n f).mul
        (tendsto_const_nhds (x := S))
  refine squeeze_zero'
    (Eventually.of_forall fun k => norm_nonneg _)
    (Eventually.of_forall fun k => ?_) hright
  simpa only [routeUDyadicXiWeightedNyquistCurrent, S] using
    norm_tsum_routeUDyadicXiWeightedNyquistCurrent_le n f k

end RHTower
