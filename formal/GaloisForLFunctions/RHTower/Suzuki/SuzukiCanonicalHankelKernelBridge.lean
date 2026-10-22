import GaloisForLFunctions.RHTower.MellinQuadraticStripDecay
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalArithmeticMellin
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelContourIntegrand
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelOperator

/-!
# Suzuki's literal-kernel to spectral-Hankel bridge

Suzuki (2012), Lemma 4.1 identifies the integral operator with literal arithmetic kernel
`h_omega(xy)` and the spectral involution

`F_{1/2}(H_omega f)(z) = Theta_omega(z) F_{1/2}(f)(-z)`.

The spectral unitary and the exact Mellin transform of `h_omega` are already formalized.  This file
builds the missing analytic bridge.  Its first ingredient is the source-faithful contour shift for
the exact product `Theta_omega(z) M_g(-iz) exp(-izr)`.  Meromorphic-innerness supplies the sharp
unit bound for `Theta_omega`; compact-smooth Mellin decay supplies an integrable quadratic bound.

No proxy kernel, assumed transform identity, RH premise, or numerical computation occurs.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

theorem norm_suzukiCanonicalTheta_le_one_of_im_nonneg
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    {z : ℂ} (hz0 : 0 ≤ z.im) :
    ‖suzukiCanonicalTheta omega z‖ ≤ 1 := by
  rcases hz0.eq_or_lt with hzero | hpos
  · have hz : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hzero]
    rw [hz, hinner.2.2.2 z.re]
  · exact (hinner.2.2.1 z hpos).le

theorem differentiableAt_suzukiCanonicalTheta_of_im_nonneg
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    {z : ℂ} (hz0 : 0 ≤ z.im) :
    DifferentiableAt ℂ (suzukiCanonicalTheta omega) z := by
  rcases hz0.eq_or_lt with hzero | hpos
  · have hz : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hzero]
    rw [hz]
    exact differentiableAt_suzukiCanonicalTheta_boundary hinner z.re
  · exact (hinner.2.1 z hpos).differentiableAt

/-- Suzuki's inverse-Mellin contour may be shifted from any nonnegative height to the real axis.
The theorem uses the exact shifted-Xi quotient and exact logarithmic Mellin transform. -/
theorem integral_suzukiCanonicalHankelContourIntegrand_shift
    {omega c : ℝ} (hc : 0 ≤ c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    (∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
        ((u : ℂ) + (c : ℂ) * Complex.I)) =
      ∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r (u : ℂ) := by
  let C : ℝ :=
    ((∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t) +
      ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t) *
        Real.exp (c * |r|)
  apply integral_horizontal_shift_of_upper_inv_one_add_sq_decay (C := C) hc
  · intro z hz0 _hzc
    apply DifferentiableAt.mul
    apply DifferentiableAt.mul
    · exact differentiableAt_suzukiCanonicalTheta_of_im_nonneg hinner hz0
    · exact (differentiable_deningerMeyerStrongLogMellin g.property (-I * z)).comp z
        (by fun_prop)
    · fun_prop
  · intro z hz0 hzc
    have htheta := norm_suzukiCanonicalTheta_le_one_of_im_nonneg hinner hz0
    have hM := norm_deningerMeyerStrongLogMellin_le_inv_one_add_sq
      g hc hz0 hzc (-z.re)
    have hrot : -Complex.I * z =
        ((z.im : ℂ) + ((-z.re : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    have hM' : ‖deningerMeyerStrongLogMellin g (-Complex.I * z)‖ ≤
        ((∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t) +
          ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t) *
            (1 + z.re ^ (2 : ℕ))⁻¹ := by
      rw [hrot]
      simpa only [neg_sq] using hM
    rw [suzukiCanonicalHankelContourIntegrand]
    have hexp : ‖Complex.exp (-Complex.I * z * (r : ℂ))‖ ≤
        Real.exp (c * |r|) := by
      have hre : (-Complex.I * z * (r : ℂ)).re = z.im * r := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [Complex.norm_exp, hre]
      apply Real.exp_le_exp.mpr
      calc
        z.im * r ≤ |z.im * r| := le_abs_self _
        _ = z.im * |r| := by rw [abs_mul, abs_of_nonneg hz0]
        _ ≤ c * |r| := mul_le_mul_of_nonneg_right hzc (abs_nonneg r)
    have hmajorant : 0 ≤
        (∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t) +
          ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t := by
      apply add_nonneg <;> apply integral_nonneg <;> intro t <;>
        simp only [deningerMeyerQuadraticStripMajorant0,
          deningerMeyerQuadraticStripMajorant2] <;> positivity
    have hright : 0 ≤
        ((∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t) +
          ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t) *
            (1 + z.re ^ (2 : ℕ))⁻¹ :=
      mul_nonneg hmajorant (by positivity)
    rw [norm_mul, norm_mul]
    calc
      ‖suzukiCanonicalTheta omega z‖ *
          ‖deningerMeyerStrongLogMellin g (-Complex.I * z)‖ *
          ‖Complex.exp (-Complex.I * z * (r : ℂ))‖ ≤
        1 * (((∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t) +
          ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t) *
            (1 + z.re ^ (2 : ℕ))⁻¹) * Real.exp (c * |r|) := by
              gcongr
      _ = C * (1 + z.re ^ (2 : ℕ))⁻¹ := by
        dsimp only [C]
        ring

end

end RHTower
