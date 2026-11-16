import GaloisForLFunctions.FamilyContinuationTheory.HarmonicGaussianPoissonGivesGrossencharacterContinuation
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.EulerCoordinates

/-!
# Harmonic Gaussians in the Eisenstein trace Fourier normalization

Transport the planar harmonic-Gaussian transform through the complex coordinate
isometry. For even angular weights the orientation of the Eisenstein embedding
cancels, leaving the positive radial scale `2π/√3` and the conjugate angular power.
-/

noncomputable section
open Complex MeasureTheory
open scoped Classical SchwartzMap FourierTransform ComplexConjugate

namespace GaloisForLFunctions.FamilyContinuationTheory
open HTGeometry.IntegerLatticePoisson
open MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
open MetaplecticMobiusDescent.CubicEisenstein.ProbeRadialMellin

private def holomorphicPlane : ℂ ≃ₗᵢ[ℝ] Plane2 :=
  Complex.conjLIE.trans {
    toLinearEquiv := complexPlaneLinearEquiv
    norm_map' := norm_complexPlaneLinearEquiv }

private theorem conjPlane_holomorphicPlane (z : ℂ) : conjPlane (holomorphicPlane z) = z := by
  change conjPlane (complexPlaneLinearEquiv (conj z)) = z
  rw [conjPlane_complexPlaneLinearEquiv]
  exact star_star z

private theorem harmonicGaussian_holomorphicPlane (m : ℕ) (t : ℝ) (z : ℂ) :
    harmonicGaussian m t (holomorphicPlane z) =
      z ^ m * Complex.exp (-((Real.pi * t : ℝ) : ℂ) * ‖z‖ ^ 2) := by
  rw [harmonicGaussian, conjPlane_holomorphicPlane, gaussianKernel,
    holomorphicPlane.norm_map]

theorem fourier_holomorphic_gaussian (m : ℕ) (t : ℝ) (ht : 0 < t) (u : ℂ) :
    (𝓕 (fun z : ℂ => z ^ m * Complex.exp (-((Real.pi * t : ℝ) : ℂ) * ‖z‖ ^ 2))) u =
      ((1 / t : ℝ) : ℂ) * (-Complex.I / (t : ℂ)) ^ m *
        (u ^ m * Complex.exp (-((Real.pi * (1 / t) : ℝ) : ℂ) * ‖u‖ ^ 2)) := by
  have h := Real.fourier_comp_linearIsometry holomorphicPlane (harmonicGaussian m t) u
  rw [fourier_harmonicGaussian m ht] at h
  simpa only [Function.comp_def, harmonicGaussian_holomorphicPlane] using h

theorem integrable_holomorphic_gaussian (m : ℕ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun z : ℂ => z ^ m * Complex.exp (-((Real.pi * t : ℝ) : ℂ) * ‖z‖ ^ 2)) := by
  have h := (holomorphicPlane.measurePreserving.integrable_comp_emb
    holomorphicPlane.toHomeomorph.measurableEmbedding).mpr (integrable_harmonicGaussian m ht)
  simpa only [Function.comp_def, harmonicGaussian_holomorphicPlane] using h

private theorem paperFrequency_sq (u : ℂ) :
    paperFrequency u ^ 2 = -(4 / 3 : ℂ) * conj u ^ 2 := by
  rw [paperFrequency, mul_pow, ← map_pow, div_pow, ringComplex_traceLambda_sq]
  simp only [map_div₀, map_neg, map_ofNat, map_pow]
  ring

/-- Even harmonic Gaussians acquire the opposite angular character under trace Fourier
transform. The even weight removes the choice of complex embedding orientation. -/
theorem paperFourier_even_harmonic_gaussian (n : ℕ) (t : ℝ) (ht : 0 < t) (u : ℂ) :
    paperFourier (fun z : ℂ => z ^ (2 * n) * Complex.exp (-(t : ℂ) * ‖z‖ ^ 2)) u =
      ((paperConstant / t : ℝ) : ℂ) ^ (2 * n + 1) * conj u ^ (2 * n) *
        Complex.exp (-((paperConstant ^ 2 / t : ℝ) : ℂ) * ‖u‖ ^ 2) := by
  have hq : 0 < t / Real.pi := div_pos ht Real.pi_pos
  have hqt : Real.pi * (t / Real.pi) = t := by field_simp
  have hF := fourier_holomorphic_gaussian (2 * n) (t / Real.pi) hq (paperFrequency u)
  rw [hqt] at hF
  have hC : (paperConstant : ℂ) ^ 2 = 4 * (Real.pi : ℂ) ^ 2 / 3 := by
    exact_mod_cast paperConstant_sq
  have hbase : ((-Complex.I / ((t / Real.pi : ℝ) : ℂ)) * paperFrequency u) ^ 2 =
      (((paperConstant / t : ℝ) : ℂ) ^ 2) * conj u ^ 2 := by
    rw [mul_pow, div_pow, neg_sq, Complex.I_sq, paperFrequency_sq]
    simp only [Complex.ofReal_div, div_pow]
    rw [hC]
    field_simp
  have hp : (-Complex.I / ((t / Real.pi : ℝ) : ℂ)) ^ (2 * n) *
      paperFrequency u ^ (2 * n) =
      ((paperConstant / t : ℝ) : ℂ) ^ (2 * n) * conj u ^ (2 * n) := by
    rw [← mul_pow, pow_mul, hbase, mul_pow, ← pow_mul, ← pow_mul]
  have hn : (‖paperFrequency u‖ : ℂ) ^ 2 =
      (4 / 3 : ℂ) * (‖u‖ : ℂ) ^ 2 := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat] using congrArg Complex.ofReal (paperFrequency_norm_sq u)
  have he : -((Real.pi * (1 / (t / Real.pi)) : ℝ) : ℂ) *
      ((4 / 3 : ℂ) * (‖u‖ : ℂ) ^ 2) =
      -((paperConstant ^ 2 / t : ℝ) : ℂ) * (‖u‖ : ℂ) ^ 2 := by
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_pow]
    rw [hC]
    field_simp
  have hs : ((2 / Real.sqrt 3 : ℝ) : ℂ) * ((1 / (t / Real.pi) : ℝ) : ℂ) =
      ((paperConstant / t : ℝ) : ℂ) := by
    unfold paperConstant
    push_cast
    field_simp
  rw [paperFourier_eq_standard, hF, hn, he, Complex.real_smul]
  calc
    _ = (((2 / Real.sqrt 3 : ℝ) : ℂ) * ((1 / (t / Real.pi) : ℝ) : ℂ)) *
        ((-Complex.I / ((t / Real.pi : ℝ) : ℂ)) ^ (2 * n) * paperFrequency u ^ (2 * n)) *
        Complex.exp (-((paperConstant ^ 2 / t : ℝ) : ℂ) * ‖u‖ ^ 2) := by ring
    _ = _ := by rw [hs, hp, pow_succ]; ring

end GaloisForLFunctions.FamilyContinuationTheory
