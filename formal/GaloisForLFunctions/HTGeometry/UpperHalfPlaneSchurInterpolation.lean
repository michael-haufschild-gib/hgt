import GaloisForLFunctions.HTGeometry.CaratheodoryNevanlinnaPick
import GaloisForLFunctions.HTGeometry.CayleyGeneralizedSchurCongruence

/-!
# Upper-half-plane Schur interpolation from a positive sampled kernel

The disk Nevanlinna--Pick theorem transfers through Cayley congruence to
arbitrary upper-half-plane sampling sets.  This will detect unavoidable
negative finite-prime Pick data from an uncancelled pole in the completion.
-/

open Complex Set Metric
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem upperToDiskCayley_norm_lt_one {z : ℂ} (hz : 0 < z.im) :
    ‖upperToDiskCayley z‖ < 1 := by
  have hden : z + I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, I_im, Complex.zero_im] at hi
    linarith
  have hnorm : 0 < ‖z + I‖ ^ (2 : ℕ) := by positivity
  have h := one_sub_norm_upperToDiskCayley_sq hden
  have hpos : 0 < 4 * z.im / ‖z + I‖ ^ (2 : ℕ) := by positivity
  nlinarith [norm_nonneg (upperToDiskCayley z)]

/-- Positive Schur kernel on any upper-half-plane sampling set yields a single
bounded holomorphic interpolant on the whole upper half-plane. -/
theorem exists_upperHalfPlane_schur_interpolant
    (V : Set ℂ) (hV : V ⊆ {z : ℂ | 0 < z.im}) (theta : ℂ → ℂ)
    (hK : IsPSDKernel (fun z w : V => upperHalfPlaneSchurKernel theta z.1 w.1)) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ 1) ∧
      (∀ z ∈ V, F z = theta z) := by
  let p : V → ℂ := fun z => upperToDiskCayley z.1
  let hval : V → ℂ := fun z => theta z.1
  let w : V → ℂ := fun z => upperToDiskKernelWeight z.1
  have hp : ∀ z : V, ‖p z‖ < 1 := fun z =>
    upperToDiskCayley_norm_lt_one (hV z.2)
  have hzden (z : V) : z.1 + I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, I_im, Complex.zero_im] at hi
    have hz := hV z.2
    change 0 < z.1.im at hz
    linarith
  have hwden (z : V) : (starRingEnd ℂ) z.1 - I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, I_im, Complex.zero_im] at hi
    have hz := hV z.2
    change 0 < z.1.im at hz
    linarith
  have hzw (z w : V) : z.1 - (starRingEnd ℂ) w.1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hi
    have hz := hV z.2
    have hw := hV w.2
    change 0 < z.1.im at hz
    change 0 < w.1.im at hw
    linarith
  have hwne (z : V) : w z ≠ 0 := by
    dsimp [w, upperToDiskKernelWeight]
    exact div_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne')
      (hzden z)
  have hKdisk : IsPSDKernel
      (fun z w : V =>
        (1 - hval z * (starRingEnd ℂ) (hval w)) /
          (1 - p z * (starRingEnd ℂ) (p w))) := by
    refine (hK.mul_diag (fun z => (w z)⁻¹)).congr (fun z y => ?_)
    change (w z)⁻¹ * (starRingEnd ℂ) ((w y)⁻¹) *
        upperHalfPlaneSchurKernel theta z.1 y.1 =
      diskSchurValueKernel (theta z.1) (theta y.1)
        (upperToDiskCayley z.1) (upperToDiskCayley y.1)
    rw [upperHalfPlaneSchurKernel_eq_cayley_congruence theta
      (hzden z) (hwden y) (hzw z y)]
    change (w z)⁻¹ * (starRingEnd ℂ) ((w y)⁻¹) *
        (w z * diskSchurValueKernel (theta z.1) (theta y.1)
          (upperToDiskCayley z.1) (upperToDiskCayley y.1) *
          (starRingEnd ℂ) (w y)) = _
    rw [map_inv₀]
    field_simp [hwne z, hwne y, (map_ne_zero (starRingEnd ℂ)).mpr (hwne y)]
  obtain ⟨G, hGdiff, hGnorm, hGval⟩ :=
    exists_schur_interpolant_of_pickKernel hp hKdisk
  refine ⟨fun z => G (upperToDiskCayley z), ?_, ?_, ?_⟩
  · intro z hz
    have hden : z + I ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp only [Complex.add_im, I_im, Complex.zero_im] at hi
      change 0 < z.im at hz
      linarith
    have hC : AnalyticAt ℂ upperToDiskCayley z := by
      unfold upperToDiskCayley
      exact (analyticAt_id.sub analyticAt_const).div
        (analyticAt_id.add analyticAt_const) hden
    have hball : upperToDiskCayley z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using upperToDiskCayley_norm_lt_one hz
    have hGat : AnalyticAt ℂ G (upperToDiskCayley z) :=
      (hGdiff.analyticOnNhd isOpen_ball) _ hball
    exact hGat.comp hC
  · intro z hz
    exact hGnorm _ (upperToDiskCayley_norm_lt_one hz)
  · intro z hz
    exact hGval ⟨z, hz⟩

end

end GaloisForLFunctions.HTGeometry
