import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleParityWallTransgression

open Set MeasureTheory Filter
open scoped Topology
noncomputable section
namespace RHTower

/-- The covariant Gamma/polar wall charge. -/
def ccmGammaPoleWallInvariant (s : ℝ) : ℝ :=
  Real.cosh s * ccmGammaPoleSelfBoundarySlope s -
    Real.sinh s * ccmGammaPoleSelfBoundaryPrimitive s -
      2 * ccmGammaPoleBoundaryLog (2 * s)

private theorem ccmGammaPoleWallInvariant_forcing {s : ℝ} (hs : 0 < s) :
    -Real.cosh s *
        (4 * Real.exp (-s) * (1 + Real.exp (4 * s)) / (Real.exp (4 * s) - 1)) +
      4 / (Real.exp (2 * s) - 1) = -2 + 2 * Real.exp (-2 * s) := by
  have h2 : Real.exp (2 * s) - 1 ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith)))
  have h4 : Real.exp (4 * s) - 1 ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith)))
  have hneg : Real.exp (-s) = (Real.exp s)⁻¹ := by rw [Real.exp_neg]
  have hneg2 : Real.exp (-2 * s) = (Real.exp s)⁻¹ ^ (2 : ℕ) := by
    rw [show -2 * s = (-s) + (-s) by ring, Real.exp_add, hneg]
    ring
  rw [Real.cosh_eq, hneg, hneg2]
  rw [show 4 * s = (2 * s) + (2 * s) by ring] at h4 ⊢
  rw [show 2 * s = s + s by ring] at h2 h4 ⊢
  simp only [Real.exp_add] at h2 h4 ⊢
  ring_nf at h2 h4 ⊢
  field_simp [h2, h4]
  ring

/-- Exact first derivative of the Gamma/polar wall charge. -/
theorem hasDerivAt_ccmGammaPoleWallInvariant (a : SuzukiPositiveAperture) :
    HasDerivAt ccmGammaPoleWallInvariant (-2 + 2 * Real.exp (-2 * a.1)) a.1 := by
  unfold ccmGammaPoleWallInvariant
  have hlog : HasDerivAt (fun y => 2 * ccmGammaPoleBoundaryLog (2 * y))
      (-4 / (Real.exp (2 * a.1) - 1)) a.1 := by
    have h := ((hasDerivAt_ccmGammaPoleBoundaryLog
      (mul_pos (by norm_num) a.2)).comp a.1
      ((hasDerivAt_id a.1).const_mul 2)).const_mul 2
    convert! h using 1
    ring
  convert! (((Real.hasDerivAt_cosh a.1).mul (hasDerivAt_ccmGammaPoleSelfBoundarySlope a.2)).sub
    ((Real.hasDerivAt_sinh a.1).mul (hasDerivAt_ccmGammaPoleSelfBoundaryPrimitive a.2))).sub hlog using 1
  symm
  rw [show Real.sinh a.1 * ccmGammaPoleSelfBoundarySlope a.1 +
        Real.cosh a.1 *
          (ccmGammaPoleSelfBoundaryPrimitive a.1 -
            4 * Real.exp (-a.1) * (1 + Real.exp (4 * a.1)) /
              (Real.exp (4 * a.1) - 1)) -
        (Real.cosh a.1 * ccmGammaPoleSelfBoundaryPrimitive a.1 +
          Real.sinh a.1 * ccmGammaPoleSelfBoundarySlope a.1) -
        -4 / (Real.exp (2 * a.1) - 1) =
      -Real.cosh a.1 *
        (4 * Real.exp (-a.1) * (1 + Real.exp (4 * a.1)) /
          (Real.exp (4 * a.1) - 1)) +
        4 / (Real.exp (2 * a.1) - 1) by ring]
  exact ccmGammaPoleWallInvariant_forcing a.2

/-- Smooth forcing remaining after the literal finite-head wall transgression. -/
def ccmWeilParitySmoothWallForcing (s : ℝ) : ℝ :=
  -4 * ccmWeilPoleCrossSmoothSlope s +
    4 * Real.cosh s * ccmWeilPoleDiagonalSmoothSlope s -
      4 * Real.sinh s * ccmWeilPoleDiagonalSmooth s

/-- Exact reduction of the smooth wall forcing to the Gamma/polar invariant. -/
theorem ccmWeilParitySmoothWallForcing_eq_gammaInvariant (s : ℝ) :
    ccmWeilParitySmoothWallForcing s =
      4 * (-1 + 2 * s + Real.exp (-2 * s) + ccmGammaPoleWallInvariant s) := by
  unfold ccmWeilParitySmoothWallForcing ccmWeilPoleCrossSmoothSlope
    ccmWeilPoleDiagonalSmoothSlope ccmWeilPoleDiagonalSmooth
    ccmGammaPoleWallInvariant
  rw [Real.cosh_eq, Real.sinh_eq]
  have he : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have hneg2 : Real.exp (-2 * s) = (Real.exp s)⁻¹ ^ (2 : ℕ) := by
    rw [show -2 * s = (-s) + (-s) by ring, Real.exp_add, Real.exp_neg]
    ring
  rw [hneg2, Real.exp_neg]
  field_simp [he]
  ring

/-- Completed polar--Gamma forcing is conserved on every positive aperture. -/
theorem hasDerivAt_ccmWeilParitySmoothWallForcing (a : SuzukiPositiveAperture) :
    HasDerivAt ccmWeilParitySmoothWallForcing 0 a.1 := by
  have hf : ccmWeilParitySmoothWallForcing = fun s =>
      4 * (-1 + 2 * s + Real.exp (-2 * s) + ccmGammaPoleWallInvariant s) := by
    funext s
    exact ccmWeilParitySmoothWallForcing_eq_gammaInvariant s
  rw [hf]
  convert! ((((hasDerivAt_const a.1 (-1)).add ((hasDerivAt_id a.1).const_mul 2)).add
    (((hasDerivAt_id a.1).const_mul (-2)).exp)).add
    (hasDerivAt_ccmGammaPoleWallInvariant a)).const_mul 4 using 1
  simp only [id_eq]
  ring_nf

end RHTower
