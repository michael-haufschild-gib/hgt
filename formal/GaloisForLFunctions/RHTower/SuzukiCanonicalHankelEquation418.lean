import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelEquation414

/-!
# Suzuki (2012), equation (4.18): pole-cleared canonical system

The derivation is performed on the entire pole-cleared numerators.  It therefore remains valid at
zeros of the completed Xi factor, where multiplying a totalized meromorphic quotient by its
denominator would lose information.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Entire positive pole-cleared mode. -/
def suzukiHankelTildeAClearedModeRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  (suzukiCanonicalE omega z *
      suzukiHankelPositiveModeRight omega homega z a +
    suzukiCanonicalE omega (-z) *
      suzukiHankelPositiveModeRight omega homega (-z) a) / 2

/-- Entire negative pole-cleared mode. -/
def suzukiHankelTildeBClearedModeRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  (-suzukiCanonicalE omega z *
      suzukiHankelNegativeModeRight omega homega z a +
    suzukiCanonicalE omega (-z) *
      suzukiHankelNegativeModeRight omega homega (-z) a) / (2 * I)

/-- Exact pole-cleared mode formula for `tilde A`, including zeros of `E^omega`. -/
theorem suzukiHankelTildeACleared_eq_mode
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeACleared omega a homega ha z =
      suzukiHankelTildeAClearedModeRight omega homega z a := by
  rw [suzukiHankelTildeACleared, suzukiHankelTildeECleared,
    suzukiHankelTildeEStarCleared, suzukiHankelTildeERegularPart,
    suzukiHankelTildeEThetaPart, suzukiHankelTildeAClearedModeRight,
    suzukiHankelPositiveModeRight_of_one_lt homega ha z,
    suzukiHankelPositiveModeRight_of_one_lt homega ha (-z),
    suzukiCompactL2Fourier_hankelPhiSumLog_eq_compactMellin_sum
      homega ha z,
    suzukiCompactL2Fourier_hankelPhiSumLog_eq_compactMellin_sum
      homega ha (-z),
    suzukiCompactL2Fourier_hankelPhiSumHankelLog_eq_compactMellin_difference
      homega ha z,
    suzukiCompactL2Fourier_hankelPhiSumHankelLog_eq_compactMellin_difference
      homega ha (-z)]
  ring

/-- Exact pole-cleared mode formula for `tilde B`, including zeros of `E^omega`. -/
theorem suzukiHankelTildeBCleared_eq_mode
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeBCleared omega a homega ha z =
      suzukiHankelTildeBClearedModeRight omega homega z a := by
  rw [suzukiHankelTildeBCleared, suzukiHankelTildeECleared,
    suzukiHankelTildeEStarCleared, suzukiHankelTildeERegularPart,
    suzukiHankelTildeEThetaPart, suzukiHankelTildeBClearedModeRight,
    suzukiHankelNegativeModeRight_of_one_lt homega ha z,
    suzukiHankelNegativeModeRight_of_one_lt homega ha (-z),
    suzukiCompactL2Fourier_hankelPhiSumLog_eq_compactMellin_sum
      homega ha z,
    suzukiCompactL2Fourier_hankelPhiSumLog_eq_compactMellin_sum
      homega ha (-z),
    suzukiCompactL2Fourier_hankelPhiSumHankelLog_eq_compactMellin_difference
      homega ha z,
    suzukiCompactL2Fourier_hankelPhiSumHankelLog_eq_compactMellin_difference
      homega ha (-z)]
  ring

/-- First pole-cleared form of equation (4.14). -/
theorem hasDerivAt_suzukiHankelTildeAClearedModeRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelTildeAClearedModeRight omega homega z)
      ((z * suzukiHankelTildeBClearedModeRight omega homega z a -
          suzukiHankelMu omega a homega ha *
            suzukiHankelTildeAClearedModeRight omega homega z a) / (a : ℂ)) a := by
  have hp := (hasDerivAt_suzukiHankelPositiveModeRight homega ha z).const_mul
    (suzukiCanonicalE omega z)
  have hpn := (hasDerivAt_suzukiHankelPositiveModeRight homega ha (-z)).const_mul
    (suzukiCanonicalE omega (-z))
  have h := hp.add hpn |>.div_const 2
  change HasDerivAt
    (fun b : ℝ =>
      (suzukiCanonicalE omega z *
          suzukiHankelPositiveModeRight omega homega z b +
        suzukiCanonicalE omega (-z) *
          suzukiHankelPositiveModeRight omega homega (-z) b) / 2) _ a
  apply h.congr_deriv
  rw [suzukiHankelTildeAClearedModeRight,
    suzukiHankelTildeBClearedModeRight]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  field_simp [haC, Complex.I_ne_zero]
  ring_nf
  simp only [I_sq]
  ring

/-- Second pole-cleared form of equation (4.14). -/
theorem hasDerivAt_suzukiHankelTildeBClearedModeRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelTildeBClearedModeRight omega homega z)
      ((suzukiHankelMu omega a homega ha *
          suzukiHankelTildeBClearedModeRight omega homega z a -
        z * suzukiHankelTildeAClearedModeRight omega homega z a) / (a : ℂ)) a := by
  have hm := (hasDerivAt_suzukiHankelNegativeModeRight homega ha z).const_mul
    (-suzukiCanonicalE omega z)
  have hmn := (hasDerivAt_suzukiHankelNegativeModeRight homega ha (-z)).const_mul
    (suzukiCanonicalE omega (-z))
  have h := hm.add hmn |>.div_const (2 * I)
  change HasDerivAt
    (fun b : ℝ =>
      (-suzukiCanonicalE omega z *
          suzukiHankelNegativeModeRight omega homega z b +
        suzukiCanonicalE omega (-z) *
          suzukiHankelNegativeModeRight omega homega (-z) b) / (2 * I)) _ a
  apply h.congr_deriv
  rw [suzukiHankelTildeAClearedModeRight,
    suzukiHankelTildeBClearedModeRight]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  field_simp [haC, Complex.I_ne_zero]
  ring_nf

/-- Pole-cleared mode product for Suzuki's completed `A` coordinate. -/
def suzukiHankelCompletedAClearedModeRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  (suzukiHankelM omega homega a : ℂ) *
    suzukiHankelTildeAClearedModeRight omega homega z a

/-- Pole-cleared mode product for Suzuki's completed `B` coordinate. -/
def suzukiHankelCompletedBClearedModeRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  (suzukiHankelM omega homega a : ℂ)⁻¹ *
    suzukiHankelTildeBClearedModeRight omega homega z a

/-- On a supercritical aperture, the existing total `A` continuation is the pole-cleared mode
product. -/
theorem suzukiHankelCompletedARight_eq_clearedMode_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelCompletedARight omega homega a z =
      suzukiHankelCompletedAClearedModeRight omega homega z a := by
  rw [congrFun (suzukiHankelCompletedARight_of_one_lt homega ha) z,
    suzukiHankelCompletedA, suzukiHankelCompletedAClearedModeRight,
    suzukiHankelTildeACleared_eq_mode homega ha z]

/-- On a supercritical aperture, the existing total `B` continuation is the pole-cleared mode
product. -/
theorem suzukiHankelCompletedBRight_eq_clearedMode_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelCompletedBRight omega homega a z =
      suzukiHankelCompletedBClearedModeRight omega homega z a := by
  rw [congrFun (suzukiHankelCompletedBRight_of_one_lt homega ha) z,
    suzukiHankelCompletedB, suzukiHankelCompletedBClearedModeRight,
    suzukiHankelTildeBCleared_eq_mode homega ha z]

/-! ## Exterior branch `0 < a ≤ 1` -/

/-- Pole-cleared `A` coordinate prescribed by Suzuki's equation (4.15). -/
def suzukiHankelCompletedAExterior
    (omega : ℝ) (z : ℂ) (a : ℝ) : ℂ :=
  (suzukiCanonicalE omega z * suzukiHankelAiz a z +
    suzukiCanonicalE omega (-z) * suzukiHankelAiz a (-z)) / 2

/-- Pole-cleared `B` coordinate prescribed by Suzuki's equation (4.15). -/
def suzukiHankelCompletedBExterior
    (omega : ℝ) (z : ℂ) (a : ℝ) : ℂ :=
  (-suzukiCanonicalE omega z * suzukiHankelAiz a z +
    suzukiCanonicalE omega (-z) * suzukiHankelAiz a (-z)) / (2 * I)

/-- The total completed `A` continuation is exactly Suzuki's exterior branch on `a ≤ 1`. -/
theorem suzukiHankelCompletedARight_eq_exterior_of_le_one
    {omega a : ℝ} (homega : 1 < omega) (ha : a ≤ 1) (z : ℂ) :
    suzukiHankelCompletedARight omega homega a z =
      suzukiHankelCompletedAExterior omega z a := by
  have hna : ¬ 1 < a := not_lt.mpr ha
  simp [suzukiHankelCompletedARight, suzukiHankelTildeEClearedRight,
    suzukiHankelTildeEStarClearedRight, suzukiHankelPhiSumFourierRight,
    suzukiHankelPhiSumHankelFourierRight,
    suzukiHankelM_eq_one_of_le_one homega ha, hna,
    suzukiHankelCompletedAExterior]

/-- The total completed `B` continuation is exactly Suzuki's exterior branch on `a ≤ 1`. -/
theorem suzukiHankelCompletedBRight_eq_exterior_of_le_one
    {omega a : ℝ} (homega : 1 < omega) (ha : a ≤ 1) (z : ℂ) :
    suzukiHankelCompletedBRight omega homega a z =
      suzukiHankelCompletedBExterior omega z a := by
  have hna : ¬ 1 < a := not_lt.mpr ha
  simp [suzukiHankelCompletedBRight, suzukiHankelTildeEClearedRight,
    suzukiHankelTildeEStarClearedRight, suzukiHankelPhiSumFourierRight,
    suzukiHankelPhiSumHankelFourierRight,
    suzukiHankelM_eq_one_of_le_one homega ha, hna,
    suzukiHankelCompletedBExterior]
  ring

/-- Exterior `A` meets the canonical source value at the seam. -/
theorem suzukiHankelCompletedAExterior_one
    (omega : ℝ) (z : ℂ) :
    suzukiHankelCompletedAExterior omega z 1 = suzukiCanonicalA omega z := by
  rw [suzukiHankelCompletedAExterior,
    suzukiCanonicalA_eq_E_ESharp_average,
    suzukiCanonicalESharp_eq_E_neg]
  simp [suzukiHankelAiz]

/-- Exterior `B` meets the canonical source value at the seam. -/
theorem suzukiHankelCompletedBExterior_one
    (omega : ℝ) (z : ℂ) :
    suzukiHankelCompletedBExterior omega z 1 = suzukiCanonicalB omega z := by
  rw [suzukiHankelCompletedBExterior,
    suzukiCanonicalB_eq_E_ESharp_difference,
    suzukiCanonicalESharp_eq_E_neg]
  simp [suzukiHankelAiz]
  field_simp [Complex.I_ne_zero]
  simp only [I_sq]
  ring

/-- First exterior differential equation, in strong derivative form. -/
theorem hasDerivAt_suzukiHankelCompletedAExterior
    {omega a : ℝ} (ha : 0 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelCompletedAExterior omega z)
      (z * suzukiHankelCompletedBExterior omega z a / (a : ℂ)) a := by
  have hp := (hasDerivAt_suzukiHankelAiz_aperture ha z).const_mul
    (suzukiCanonicalE omega z)
  have hn := (hasDerivAt_suzukiHankelAiz_aperture ha (-z)).const_mul
    (suzukiCanonicalE omega (-z))
  have h := hp.add hn |>.div_const 2
  change HasDerivAt
    (fun b : ℝ =>
      (suzukiCanonicalE omega z * suzukiHankelAiz b z +
        suzukiCanonicalE omega (-z) * suzukiHankelAiz b (-z)) / 2) _ a
  apply h.congr_deriv
  rw [suzukiHankelCompletedBExterior]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [haC, Complex.I_ne_zero]
  ring_nf
  simp only [I_sq]
  ring

/-- Second exterior differential equation, in strong derivative form. -/
theorem hasDerivAt_suzukiHankelCompletedBExterior
    {omega a : ℝ} (ha : 0 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelCompletedBExterior omega z)
      (-z * suzukiHankelCompletedAExterior omega z a / (a : ℂ)) a := by
  have hp := (hasDerivAt_suzukiHankelAiz_aperture ha z).const_mul
    (-suzukiCanonicalE omega z)
  have hn := (hasDerivAt_suzukiHankelAiz_aperture ha (-z)).const_mul
    (suzukiCanonicalE omega (-z))
  have h := hp.add hn |>.div_const (2 * I)
  change HasDerivAt
    (fun b : ℝ =>
      (-suzukiCanonicalE omega z * suzukiHankelAiz b z +
        suzukiCanonicalE omega (-z) * suzukiHankelAiz b (-z)) / (2 * I)) _ a
  apply h.congr_deriv
  rw [suzukiHankelCompletedAExterior]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [haC, Complex.I_ne_zero]
  ring_nf

/-- Equation (4.18), first row, on every subcritical positive aperture. -/
theorem hasDerivAt_suzukiHankelCompletedARight_of_lt_one
    {omega a : ℝ} (homega : 1 < omega) (ha0 : 0 < a) (ha : a < 1) (z : ℂ) :
    HasDerivAt (fun b : ℝ => suzukiHankelCompletedARight omega homega b z)
      (z * (suzukiHankelM omega homega a : ℂ) ^ 2 *
        suzukiHankelCompletedBRight omega homega a z / (a : ℂ)) a := by
  have hext := hasDerivAt_suzukiHankelCompletedAExterior (omega := omega) ha0 z
  have heq : (fun b : ℝ => suzukiHankelCompletedARight omega homega b z) =ᶠ[𝓝 a]
      suzukiHankelCompletedAExterior omega z := by
    filter_upwards [Iio_mem_nhds ha] with b hb
    exact suzukiHankelCompletedARight_eq_exterior_of_le_one homega hb.le z
  have h := hext.congr_of_eventuallyEq heq
  rw [suzukiHankelM_eq_one_of_le_one homega ha.le,
    suzukiHankelCompletedBRight_eq_exterior_of_le_one homega ha.le z]
  norm_num
  exact h

/-- Equation (4.18), second row, on every subcritical positive aperture. -/
theorem hasDerivAt_suzukiHankelCompletedBRight_of_lt_one
    {omega a : ℝ} (homega : 1 < omega) (ha0 : 0 < a) (ha : a < 1) (z : ℂ) :
    HasDerivAt (fun b : ℝ => suzukiHankelCompletedBRight omega homega b z)
      (-z * (suzukiHankelM omega homega a : ℂ)⁻¹ ^ 2 *
        suzukiHankelCompletedARight omega homega a z / (a : ℂ)) a := by
  have hext := hasDerivAt_suzukiHankelCompletedBExterior (omega := omega) ha0 z
  have heq : (fun b : ℝ => suzukiHankelCompletedBRight omega homega b z) =ᶠ[𝓝 a]
      suzukiHankelCompletedBExterior omega z := by
    filter_upwards [Iio_mem_nhds ha] with b hb
    exact suzukiHankelCompletedBRight_eq_exterior_of_le_one homega hb.le z
  have h := hext.congr_of_eventuallyEq heq
  rw [suzukiHankelM_eq_one_of_le_one homega ha.le,
    suzukiHankelCompletedARight_eq_exterior_of_le_one homega ha.le z]
  norm_num
  simpa only [neg_mul] using h

/-- Mode-product form of equation (4.18), first row, on every supercritical aperture. -/
theorem hasDerivAt_suzukiHankelCompletedAClearedModeRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelCompletedAClearedModeRight omega homega z)
      (z * (suzukiHankelM omega homega a : ℂ) ^ 2 *
        suzukiHankelCompletedBClearedModeRight omega homega z a / (a : ℂ)) a := by
  have hmR := hasDerivAt_suzukiHankelM (a := a) homega
  have hmC := hmR.ofReal_comp
  have hA := hasDerivAt_suzukiHankelTildeAClearedModeRight homega ha z
  have h := hmC.mul hA
  change HasDerivAt
    (fun b : ℝ => (suzukiHankelM omega homega b : ℂ) *
      suzukiHankelTildeAClearedModeRight omega homega z b) _ a
  apply h.congr_deriv
  rw [suzukiHankelCompletedBClearedModeRight]
  push_cast
  rw [ofReal_suzukiHankelMuScalar_eq homega a,
    suzukiHankelMuReal_of_one_lt homega ha]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  have hm0 : (suzukiHankelM omega homega a : ℂ) ≠ 0 := by
    exact_mod_cast suzukiHankelM_ne_zero homega a
  field_simp [haC, hm0]
  ring

/-- Mode-product form of equation (4.18), second row, on every supercritical aperture. -/
theorem hasDerivAt_suzukiHankelCompletedBClearedModeRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelCompletedBClearedModeRight omega homega z)
      (-z * (suzukiHankelM omega homega a : ℂ)⁻¹ ^ 2 *
        suzukiHankelCompletedAClearedModeRight omega homega z a / (a : ℂ)) a := by
  have hmR := hasDerivAt_suzukiHankelM (a := a) homega
  have hmC := hmR.ofReal_comp
  have hminv := hmC.inv (by
    exact_mod_cast suzukiHankelM_ne_zero homega a)
  have hB := hasDerivAt_suzukiHankelTildeBClearedModeRight homega ha z
  have h := hminv.mul hB
  change HasDerivAt
    (fun b : ℝ => (suzukiHankelM omega homega b : ℂ)⁻¹ *
      suzukiHankelTildeBClearedModeRight omega homega z b) _ a
  apply h.congr_deriv
  rw [suzukiHankelCompletedAClearedModeRight]
  push_cast
  rw [ofReal_suzukiHankelMuScalar_eq homega a,
    suzukiHankelMuReal_of_one_lt homega ha]
  simp only [Pi.inv_apply]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  have hm0 : (suzukiHankelM omega homega a : ℂ) ≠ 0 := by
    exact_mod_cast suzukiHankelM_ne_zero homega a
  field_simp [haC, hm0]
  ring

/-- Equation (4.18), first row, in strong derivative form on every supercritical aperture.  No
spectral regular-locus hypothesis is present. -/
theorem hasDerivAt_suzukiHankelCompletedARight_equation418
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (fun b : ℝ => suzukiHankelCompletedARight omega homega b z)
      (z * (suzukiHankelM omega homega a : ℂ) ^ 2 *
        suzukiHankelCompletedBRight omega homega a z / (a : ℂ)) a := by
  have hmode := hasDerivAt_suzukiHankelCompletedAClearedModeRight homega ha z
  have heq : (fun b : ℝ => suzukiHankelCompletedARight omega homega b z) =ᶠ[𝓝 a]
      suzukiHankelCompletedAClearedModeRight omega homega z := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact suzukiHankelCompletedARight_eq_clearedMode_of_one_lt homega hb z
  have h := hmode.congr_of_eventuallyEq heq
  rw [suzukiHankelCompletedBRight_eq_clearedMode_of_one_lt homega ha z]
  exact h

/-- Equation (4.18), second row, in strong derivative form on every supercritical aperture. -/
theorem hasDerivAt_suzukiHankelCompletedBRight_equation418
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (fun b : ℝ => suzukiHankelCompletedBRight omega homega b z)
      (-z * (suzukiHankelM omega homega a : ℂ)⁻¹ ^ 2 *
        suzukiHankelCompletedARight omega homega a z / (a : ℂ)) a := by
  have hmode := hasDerivAt_suzukiHankelCompletedBClearedModeRight homega ha z
  have heq : (fun b : ℝ => suzukiHankelCompletedBRight omega homega b z) =ᶠ[𝓝 a]
      suzukiHankelCompletedBClearedModeRight omega homega z := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact suzukiHankelCompletedBRight_eq_clearedMode_of_one_lt homega hb z
  have h := hmode.congr_of_eventuallyEq heq
  rw [suzukiHankelCompletedARight_eq_clearedMode_of_one_lt homega ha z]
  exact h

/-! ## The seam `a = 1` -/

/-- Pointwise right limit for the completed `A` coordinate, extracted from the compact-uniform
form of Suzuki's Lemma 4.10. -/
theorem tendsto_suzukiHankelCompletedARight_right_one
    {omega : ℝ} (homega : 1 < omega) (z : ℂ) :
    Tendsto (fun a : ℝ => suzukiHankelCompletedARight omega homega a z)
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (suzukiCanonicalA omega z)) := by
  have h := tendstoUniformlyOn_suzukiHankelCompletedARight homega
    (isCompact_singleton : IsCompact ({z} : Set ℂ))
  exact h.tendsto_at (by simp)

/-- Pointwise right limit for the completed `B` coordinate, extracted from the compact-uniform
form of Suzuki's Lemma 4.10. -/
theorem tendsto_suzukiHankelCompletedBRight_right_one
    {omega : ℝ} (homega : 1 < omega) (z : ℂ) :
    Tendsto (fun a : ℝ => suzukiHankelCompletedBRight omega homega a z)
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (suzukiCanonicalB omega z)) := by
  have h := tendstoUniformlyOn_suzukiHankelCompletedBRight homega
    (isCompact_singleton : IsCompact ({z} : Set ℂ))
  exact h.tendsto_at (by simp)

/-- The first completed coordinate is differentiable at the Fredholm seam.  Right
differentiability is obtained from the supercritical ODE and Lemma 4.10; left differentiability
comes from the exact exterior formula.  The two derivatives coincide. -/
theorem hasDerivAt_suzukiHankelCompletedARight_one
    {omega : ℝ} (homega : 1 < omega) (z : ℂ) :
    HasDerivAt (fun b : ℝ => suzukiHankelCompletedARight omega homega b z)
      (z * suzukiCanonicalB omega z) 1 := by
  let fA : ℝ → ℂ := fun b => suzukiHankelCompletedARight omega homega b z
  let fB : ℝ → ℂ := fun b => suzukiHankelCompletedBRight omega homega b z
  have hleftExt : HasDerivWithinAt (suzukiHankelCompletedAExterior omega z)
      (z * suzukiCanonicalB omega z) (Iic (1 : ℝ)) 1 := by
    simpa [suzukiHankelCompletedBExterior_one] using
      (hasDerivAt_suzukiHankelCompletedAExterior
        (omega := omega) (a := (1 : ℝ)) zero_lt_one z).hasDerivWithinAt
  have hleft : HasDerivWithinAt fA (z * suzukiCanonicalB omega z)
      (Iic (1 : ℝ)) 1 := by
    refine hleftExt.congr_of_mem ?_ (by simp)
    intro b hb
    exact suzukiHankelCompletedARight_eq_exterior_of_le_one homega hb z
  have hdiff : DifferentiableOn ℝ fA (Ioi (1 : ℝ)) := by
    intro b hb
    exact (hasDerivAt_suzukiHankelCompletedARight_equation418 homega hb z).differentiableAt
      |>.differentiableWithinAt
  have hcont : ContinuousWithinAt fA (Ioi (1 : ℝ)) 1 := by
    show Tendsto fA (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (fA 1))
    have hval : fA 1 = suzukiCanonicalA omega z := by
      dsimp [fA]
      rw [suzukiHankelCompletedARight_eq_exterior_of_le_one homega le_rfl z,
        suzukiHankelCompletedAExterior_one]
    rw [hval]
    exact tendsto_suzukiHankelCompletedARight_right_one homega z
  have hmR : Tendsto (suzukiHankelM omega homega)
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 1) := tendsto_suzukiHankelM_right_one homega
  have hmC : Tendsto (fun b : ℝ => (suzukiHankelM omega homega b : ℂ))
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hmR
  have hB : Tendsto fB (𝓝[Ioi (1 : ℝ)] 1)
      (𝓝 (suzukiCanonicalB omega z)) := by
    exact tendsto_suzukiHankelCompletedBRight_right_one homega z
  have haR : Tendsto (fun b : ℝ => b) (𝓝[Ioi (1 : ℝ)] 1) (𝓝 1) :=
    tendsto_id.mono_left inf_le_left
  have haC : Tendsto (fun b : ℝ => (b : ℂ)) (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp haR
  have hz : Tendsto (fun _ : ℝ => z) (𝓝[Ioi (1 : ℝ)] 1) (𝓝 z) :=
    tendsto_const_nhds
  have hraw : Tendsto
      ((fun b : ℝ => z * (suzukiHankelM omega homega b : ℂ) ^ 2 * fB b) /
        fun b : ℝ => (b : ℂ))
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (z * suzukiCanonicalB omega z)) := by
    simpa only [one_pow, mul_one, div_one] using
      (((hz.mul (hmC.pow 2)).mul hB).div haC (by norm_num : (1 : ℂ) ≠ 0))
  have hformula : Tendsto
      (fun b : ℝ => z * (suzukiHankelM omega homega b : ℂ) ^ 2 * fB b / (b : ℂ))
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (z * suzukiCanonicalB omega z)) := by
    refine hraw.congr' (Filter.Eventually.of_forall ?_)
    intro b
    rfl
  have hderivEq :
      (fun b : ℝ => z * (suzukiHankelM omega homega b : ℂ) ^ 2 * fB b / (b : ℂ))
        =ᶠ[𝓝[Ioi (1 : ℝ)] 1] (fun b => deriv fA b) := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (hasDerivAt_suzukiHankelCompletedARight_equation418 homega hb z).deriv.symm
  have hderiv : Tendsto (fun b => deriv fA b) (𝓝[Ioi (1 : ℝ)] 1)
      (𝓝 (z * suzukiCanonicalB omega z)) := hformula.congr' hderivEq
  have hright : HasDerivWithinAt fA (z * suzukiCanonicalB omega z)
      (Ici (1 : ℝ)) 1 :=
    hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont self_mem_nhdsWithin hderiv
  have hall := hleft.union hright
  rw [Iic_union_Ici] at hall
  exact hasDerivWithinAt_univ.mp hall

/-- The second completed coordinate is differentiable at the Fredholm seam, with matching left
and right derivatives. -/
theorem hasDerivAt_suzukiHankelCompletedBRight_one
    {omega : ℝ} (homega : 1 < omega) (z : ℂ) :
    HasDerivAt (fun b : ℝ => suzukiHankelCompletedBRight omega homega b z)
      (-z * suzukiCanonicalA omega z) 1 := by
  let fA : ℝ → ℂ := fun b => suzukiHankelCompletedARight omega homega b z
  let fB : ℝ → ℂ := fun b => suzukiHankelCompletedBRight omega homega b z
  have hleftExt : HasDerivWithinAt (suzukiHankelCompletedBExterior omega z)
      (-z * suzukiCanonicalA omega z) (Iic (1 : ℝ)) 1 := by
    simpa [suzukiHankelCompletedAExterior_one] using
      (hasDerivAt_suzukiHankelCompletedBExterior
        (omega := omega) (a := (1 : ℝ)) zero_lt_one z).hasDerivWithinAt
  have hleft : HasDerivWithinAt fB (-z * suzukiCanonicalA omega z)
      (Iic (1 : ℝ)) 1 := by
    refine hleftExt.congr_of_mem ?_ (by simp)
    intro b hb
    exact suzukiHankelCompletedBRight_eq_exterior_of_le_one homega hb z
  have hdiff : DifferentiableOn ℝ fB (Ioi (1 : ℝ)) := by
    intro b hb
    exact (hasDerivAt_suzukiHankelCompletedBRight_equation418 homega hb z).differentiableAt
      |>.differentiableWithinAt
  have hcont : ContinuousWithinAt fB (Ioi (1 : ℝ)) 1 := by
    show Tendsto fB (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (fB 1))
    have hval : fB 1 = suzukiCanonicalB omega z := by
      dsimp [fB]
      rw [suzukiHankelCompletedBRight_eq_exterior_of_le_one homega le_rfl z,
        suzukiHankelCompletedBExterior_one]
    rw [hval]
    exact tendsto_suzukiHankelCompletedBRight_right_one homega z
  have hmR : Tendsto (suzukiHankelM omega homega)
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 1) := tendsto_suzukiHankelM_right_one homega
  have hmC : Tendsto (fun b : ℝ => (suzukiHankelM omega homega b : ℂ))
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hmR
  have hmInv : Tendsto (fun b : ℝ => (suzukiHankelM omega homega b : ℂ)⁻¹)
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (1 : ℂ)) := by
    simpa using hmC.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hA : Tendsto fA (𝓝[Ioi (1 : ℝ)] 1)
      (𝓝 (suzukiCanonicalA omega z)) := by
    exact tendsto_suzukiHankelCompletedARight_right_one homega z
  have haR : Tendsto (fun b : ℝ => b) (𝓝[Ioi (1 : ℝ)] 1) (𝓝 1) :=
    tendsto_id.mono_left inf_le_left
  have haC : Tendsto (fun b : ℝ => (b : ℂ)) (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp haR
  have hz : Tendsto (fun _ : ℝ => (-z : ℂ)) (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (-z)) :=
    tendsto_const_nhds
  have hraw : Tendsto
      ((fun b : ℝ => -z * (suzukiHankelM omega homega b : ℂ)⁻¹ ^ 2 * fA b) /
        fun b : ℝ => (b : ℂ))
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (-z * suzukiCanonicalA omega z)) := by
    simpa only [one_pow, mul_one, div_one] using
      (((hz.mul (hmInv.pow 2)).mul hA).div haC (by norm_num : (1 : ℂ) ≠ 0))
  have hformula : Tendsto
      (fun b : ℝ => -z * (suzukiHankelM omega homega b : ℂ)⁻¹ ^ 2 * fA b / (b : ℂ))
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 (-z * suzukiCanonicalA omega z)) := by
    refine hraw.congr' (Filter.Eventually.of_forall ?_)
    intro b
    rfl
  have hderivEq :
      (fun b : ℝ => -z * (suzukiHankelM omega homega b : ℂ)⁻¹ ^ 2 * fA b / (b : ℂ))
        =ᶠ[𝓝[Ioi (1 : ℝ)] 1] (fun b => deriv fB b) := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (hasDerivAt_suzukiHankelCompletedBRight_equation418 homega hb z).deriv.symm
  have hderiv : Tendsto (fun b => deriv fB b) (𝓝[Ioi (1 : ℝ)] 1)
      (𝓝 (-z * suzukiCanonicalA omega z)) := hformula.congr' hderivEq
  have hright : HasDerivWithinAt fB (-z * suzukiCanonicalA omega z)
      (Ici (1 : ℝ)) 1 :=
    hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont self_mem_nhdsWithin hderiv
  have hall := hleft.union hright
  rw [Iic_union_Ici] at hall
  exact hasDerivWithinAt_univ.mp hall

/-! ## Equation (4.18) on the full positive aperture axis -/

/-- First row of equation (4.18), in strong derivative form, for every `a > 0`. -/
theorem hasDerivAt_suzukiHankelCompletedARight_all_positive
    {omega a : ℝ} (homega : 1 < omega) (ha0 : 0 < a) (z : ℂ) :
    HasDerivAt (fun b : ℝ => suzukiHankelCompletedARight omega homega b z)
      (z * (suzukiHankelM omega homega a : ℂ) ^ 2 *
        suzukiHankelCompletedBRight omega homega a z / (a : ℂ)) a := by
  rcases lt_trichotomy a 1 with ha | rfl | ha
  · exact hasDerivAt_suzukiHankelCompletedARight_of_lt_one homega ha0 ha z
  · rw [suzukiHankelM_eq_one_of_le_one homega le_rfl,
      suzukiHankelCompletedBRight_eq_exterior_of_le_one homega le_rfl z,
      suzukiHankelCompletedBExterior_one]
    norm_num
    exact hasDerivAt_suzukiHankelCompletedARight_one homega z
  · exact hasDerivAt_suzukiHankelCompletedARight_equation418 homega ha z

/-- Second row of equation (4.18), in strong derivative form, for every `a > 0`. -/
theorem hasDerivAt_suzukiHankelCompletedBRight_all_positive
    {omega a : ℝ} (homega : 1 < omega) (ha0 : 0 < a) (z : ℂ) :
    HasDerivAt (fun b : ℝ => suzukiHankelCompletedBRight omega homega b z)
      (-z * (suzukiHankelM omega homega a : ℂ)⁻¹ ^ 2 *
        suzukiHankelCompletedARight omega homega a z / (a : ℂ)) a := by
  rcases lt_trichotomy a 1 with ha | rfl | ha
  · exact hasDerivAt_suzukiHankelCompletedBRight_of_lt_one homega ha0 ha z
  · rw [suzukiHankelM_eq_one_of_le_one homega le_rfl,
      suzukiHankelCompletedARight_eq_exterior_of_le_one homega le_rfl z,
      suzukiHankelCompletedAExterior_one]
    norm_num
    simpa only [neg_mul] using hasDerivAt_suzukiHankelCompletedBRight_one homega z
  · exact hasDerivAt_suzukiHankelCompletedBRight_equation418 homega ha z

/-- Supercritical specialization of the literal first scalar row of equation (4.18). -/
theorem suzuki2012_equation_four_one_eight_first_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    -(a : ℂ) * deriv (fun b : ℝ =>
      suzukiHankelCompletedARight omega homega b z) a =
      -z * (suzukiHankelM omega homega a : ℂ) ^ 2 *
        suzukiHankelCompletedB omega a homega ha z := by
  rw [(hasDerivAt_suzukiHankelCompletedARight_equation418 homega ha z).deriv,
    congrFun (suzukiHankelCompletedBRight_of_one_lt homega ha) z]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  field_simp [haC]

/-- Supercritical specialization of the literal second scalar row of equation (4.18). -/
theorem suzuki2012_equation_four_one_eight_second_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    -(a : ℂ) * deriv (fun b : ℝ =>
      suzukiHankelCompletedBRight omega homega b z) a =
      z * (suzukiHankelM omega homega a : ℂ)⁻¹ ^ 2 *
        suzukiHankelCompletedA omega a homega ha z := by
  rw [(hasDerivAt_suzukiHankelCompletedBRight_equation418 homega ha z).deriv,
    congrFun (suzukiHankelCompletedARight_of_one_lt homega ha) z]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  field_simp [haC]

/-- Literal first scalar row of Suzuki's equation (4.18), on every positive aperture and at every
spectral point. -/
theorem suzuki2012_equation_four_one_eight_first
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    -(a : ℂ) * deriv (fun b : ℝ =>
      suzukiHankelCompletedARight omega homega b z) a =
      -z * (suzukiHankelM omega homega a : ℂ) ^ 2 *
        suzukiHankelCompletedBRight omega homega a z := by
  rw [(hasDerivAt_suzukiHankelCompletedARight_all_positive homega ha z).deriv]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [haC]

/-- Literal second scalar row of Suzuki's equation (4.18), on every positive aperture and at every
spectral point. -/
theorem suzuki2012_equation_four_one_eight_second
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    -(a : ℂ) * deriv (fun b : ℝ =>
      suzukiHankelCompletedBRight omega homega b z) a =
      z * (suzukiHankelM omega homega a : ℂ)⁻¹ ^ 2 *
        suzukiHankelCompletedARight omega homega a z := by
  rw [(hasDerivAt_suzukiHankelCompletedBRight_all_positive homega ha z).deriv]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [haC]

/-- **Suzuki (2012), equation (4.18), closed theorem.**  Both rows hold on the entire printed
domain `0 < a < ∞`; no regular-locus, nonvanishing, or endpoint differentiability premise is
assumed. -/
theorem suzuki2012_equation_four_one_eight :
    ∀ (omega : ℝ) (homega : 1 < omega) (a : ℝ), 0 < a → ∀ (z : ℂ),
      (-(a : ℂ) * deriv (fun b : ℝ =>
          suzukiHankelCompletedARight omega homega b z) a =
        -z * (suzukiHankelM omega homega a : ℂ) ^ 2 *
          suzukiHankelCompletedBRight omega homega a z) ∧
      (-(a : ℂ) * deriv (fun b : ℝ =>
          suzukiHankelCompletedBRight omega homega b z) a =
        z * (suzukiHankelM omega homega a : ℂ)⁻¹ ^ 2 *
          suzukiHankelCompletedARight omega homega a z) := by
  intro omega homega a ha z
  exact ⟨suzuki2012_equation_four_one_eight_first homega ha z,
    suzuki2012_equation_four_one_eight_second homega ha z⟩

end RHTower
