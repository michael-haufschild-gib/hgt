import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurKernel

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal upper-half-plane Schur defect kernel. -/
def upperHalfPlaneSchurKernel (theta : ℂ → ℂ) (z w : ℂ) : ℂ :=
  I / (z - (starRingEnd ℂ) w) *
    (1 - theta z * (starRingEnd ℂ) (theta w))

/-- Disk Schur defect kernel at four scalar values. -/
def diskSchurValueKernel (fz fw z w : ℂ) : ℂ :=
  (1 - fz * (starRingEnd ℂ) fw) /
    (1 - z * (starRingEnd ℂ) w)

/-- Disk generalized-Schur numerator kernel at scalar values. -/
def diskGeneralizedSchurValueKernel
    (bz bw fz fw z w : ℂ) : ℂ :=
  (bz * (starRingEnd ℂ) bw - fz * (starRingEnd ℂ) fw) /
    (1 - z * (starRingEnd ℂ) w)

/-- Standard upper-half-plane-to-disk Cayley map. -/
def upperToDiskCayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- Exact norm defect of the upper-half-plane Cayley transform. -/
theorem one_sub_norm_upperToDiskCayley_sq
    {z : ℂ} (hden : z + I ≠ 0) :
    1 - ‖upperToDiskCayley z‖ ^ 2 = 4 * z.im / ‖z + I‖ ^ 2 := by
  have hminus : ‖z - I‖ ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, I_re, I_im]
    ring
  have hplus : ‖z + I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, add_im, I_re, I_im]
    ring
  have hplusNe : z.re ^ 2 + (z.im + 1) ^ 2 ≠ 0 := by
    rw [← hplus]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hden)
  rw [upperToDiskCayley, norm_div, div_pow, hminus, hplus]
  field_simp [hplusNe]
  ring

/-- Nonzero diagonal weight relating upper-half-plane and disk Schur kernels. -/
def upperToDiskKernelWeight (z : ℂ) : ℂ :=
  (Real.sqrt 2 : ℂ) / (z + I)

/-- Exact denominator transport under the upper-half-plane Cayley map. -/
theorem one_sub_upperToDiskCayley_mul_conj
    {z w : ℂ} (hz : z + I ≠ 0)
    (hw : (starRingEnd ℂ) w - I ≠ 0) :
    1 - upperToDiskCayley z *
        (starRingEnd ℂ) (upperToDiskCayley w) =
      (-2 * I * (z - (starRingEnd ℂ) w)) /
        ((z + I) * ((starRingEnd ℂ) w - I)) := by
  have hconj :
      (starRingEnd ℂ) (upperToDiskCayley w) =
        ((starRingEnd ℂ) w + I) / ((starRingEnd ℂ) w - I) := by
    rw [upperToDiskCayley, map_div₀, map_sub, map_add]
    simp
    ring_nf
  rw [upperToDiskCayley, hconj]
  field_simp [hz, hw]
  ring

/-- Cayley conjugacy is an exact diagonal congruence of Schur kernels. -/
theorem upperHalfPlaneSchurKernel_eq_cayley_congruence
    (theta : ℂ → ℂ) {z w : ℂ}
    (hz : z + I ≠ 0) (hw : (starRingEnd ℂ) w - I ≠ 0)
    (hzw : z - (starRingEnd ℂ) w ≠ 0) :
    upperHalfPlaneSchurKernel theta z w =
      upperToDiskKernelWeight z *
        diskSchurValueKernel (theta z) (theta w)
          (upperToDiskCayley z) (upperToDiskCayley w) *
        (starRingEnd ℂ) (upperToDiskKernelWeight w) := by
  have hsqrtR : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtC : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast hsqrtR
  have hsqrtPow : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    simpa only [pow_two] using hsqrtC
  have hcayleyDen :
      1 - upperToDiskCayley z *
          (starRingEnd ℂ) (upperToDiskCayley w) ≠ 0 := by
    rw [one_sub_upperToDiskCayley_mul_conj hz hw]
    exact div_ne_zero
      (mul_ne_zero (by norm_num) hzw)
      (mul_ne_zero hz hw)
  have hweightConj :
      (starRingEnd ℂ) (upperToDiskKernelWeight w) =
        (Real.sqrt 2 : ℂ) / ((starRingEnd ℂ) w - I) := by
    rw [upperToDiskKernelWeight, map_div₀, map_add]
    simp
    ring_nf
  rw [upperHalfPlaneSchurKernel, diskSchurValueKernel,
    upperToDiskKernelWeight, hweightConj,
    one_sub_upperToDiskCayley_mul_conj hz hw]
  field_simp [hz, hw, hzw, hcayleyDen]
  rw [hsqrtPow]
  norm_num [pow_two, I_mul_I]
  ring

/-- Passing from `F/B` to the generalized numerator kernel is diagonal congruence. -/
theorem diskSchurValueKernel_div_eq_generalized_congruence
    {bz bw fz fw z w : ℂ} (hbz : bz ≠ 0) (hbw : bw ≠ 0)
    (hzw : 1 - z * (starRingEnd ℂ) w ≠ 0) :
    diskSchurValueKernel (fz / bz) (fw / bw) z w =
      bz⁻¹ * diskGeneralizedSchurValueKernel bz bw fz fw z w *
        (starRingEnd ℂ) (bw⁻¹) := by
  rw [diskSchurValueKernel, diskGeneralizedSchurValueKernel]
  simp only [map_div₀, map_inv₀]
  field_simp [hbz, hbw, hzw, (map_ne_zero (starRingEnd ℂ)).mpr hbw]

end

end GaloisForLFunctions.HTGeometry
