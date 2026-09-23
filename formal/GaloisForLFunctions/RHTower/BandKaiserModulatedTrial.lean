import GaloisForLFunctions.RHTower.BandKaiserContinuity
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation

/-!
# Frequency-shifted Kaiser--Bessel trials

Fixed-depth concentration needs several independent trials with the same `exp (-2*c)` leakage
clock as the ground Kaiser vector.  Cosine modulation supplies them without disturbing compact
support.  This module establishes the exact modulation formula and a quadratic spectral-density
bound reducing every modulated packet to two translates of the already controlled Kaiser density.

Later finite-depth estimates only need to control the thin translated edge strips and the Gram
conditioning of finitely many such packets; no new oscillatory transform calculation is required.
-/

open MeasureTheory Set intervalIntegral FourierTransform

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Kaiser--Bessel trial modulated by a Fourier-frequency cosine. -/
def kaiserCosTrial (c w x : ℝ) : ℝ :=
  kaiserTrial c x * Real.cos (2 * Real.pi * w * x)

theorem continuous_kaiserCosTrial (c w : ℝ) : Continuous (kaiserCosTrial c w) := by
  exact (continuous_kaiserTrial c).mul (Real.continuous_cos.comp (by fun_prop))

theorem kaiserCosTrial_even (c w : ℝ) : Function.Even (kaiserCosTrial c w) := by
  intro x
  rw [kaiserCosTrial, kaiserCosTrial, kaiserTrial_even]
  congr 1
  rw [show 2 * Real.pi * w * -x = -(2 * Real.pi * w * x) by ring, Real.cos_neg]

/-- Truncation commutes exactly with cosine modulation. -/
theorem bandTrunc_kaiserCosTrial (c w : ℝ) :
    bandTrunc (kaiserCosTrial c w) = fun x : ℝ =>
      bandTrunc (kaiserTrial c) x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) := by
  funext x
  simp only [bandTrunc, kaiserCosTrial, Set.indicator_apply]
  split_ifs <;> simp

/-- Exact Fourier transform of a modulated Kaiser packet: the average of two translated base
transforms. -/
theorem fourier_bandTrunc_kaiserCosTrial (c w ξ : ℝ) :
    𝓕 (bandTrunc (kaiserCosTrial c w)) ξ =
      (2 : ℂ)⁻¹ * 𝓕 (bandTrunc (kaiserTrial c)) (ξ - w) +
        (2 : ℂ)⁻¹ * 𝓕 (bandTrunc (kaiserTrial c)) (ξ + w) := by
  rw [bandTrunc_kaiserCosTrial]
  exact GaloisForLFunctions.HTGeometry.fourierIntegral_mul_cos
    (integrable_bandTrunc (continuous_kaiserTrial c)) w ξ

/-- The modulated spectral density is bounded by the arithmetic mean of the two shifted base
densities. -/
theorem norm_sq_fourier_bandTrunc_kaiserCosTrial_le (c w ξ : ℝ) :
    ‖𝓕 (bandTrunc (kaiserCosTrial c w)) ξ‖ ^ (2 : ℕ) ≤
      (‖𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)‖ ^ (2 : ℕ) +
        ‖𝓕 (bandTrunc (kaiserTrial c)) (ξ + w)‖ ^ (2 : ℕ)) / 2 := by
  let z := 𝓕 (bandTrunc (kaiserTrial c)) (ξ - w)
  let u := 𝓕 (bandTrunc (kaiserTrial c)) (ξ + w)
  rw [fourier_bandTrunc_kaiserCosTrial]
  have heq : (2 : ℂ)⁻¹ * z + (2 : ℂ)⁻¹ * u = (z + u) / 2 := by ring
  rw [show 𝓕 (bandTrunc (kaiserTrial c)) (ξ - w) = z from rfl,
    show 𝓕 (bandTrunc (kaiserTrial c)) (ξ + w) = u from rfl, heq]
  have hnorm : ‖(z + u) / (2 : ℂ)‖ ≤ (‖z‖ + ‖u‖) / 2 := by
    rw [norm_div]
    norm_num
    exact div_le_div_of_nonneg_right (norm_add_le z u) (by norm_num)
  have hsq := pow_le_pow_left₀ (norm_nonneg ((z + u) / (2 : ℂ))) hnorm 2
  calc
    ‖(z + u) / (2 : ℂ)‖ ^ (2 : ℕ) ≤ ((‖z‖ + ‖u‖) / 2) ^ (2 : ℕ) := hsq
    _ ≤ (‖z‖ ^ (2 : ℕ) + ‖u‖ ^ (2 : ℕ)) / 2 := by
      nlinarith [sq_nonneg (‖z‖ - ‖u‖)]

/-! ## Uniform control on the thin inner edge strip -/

/-- Aperture-independent bound for the Kaiser transform whenever its squared distance inside the
band edge is at most two. -/
def kaiserEdgeTransformBound : ℝ :=
  ∑' m : ℕ, 2 * (2 : ℝ) ^ m / (Nat.factorial (2 * m + 1) : ℝ)

theorem kaiserEdgeTransformBound_nonneg : 0 ≤ kaiserEdgeTransformBound := by
  rw [kaiserEdgeTransformBound]
  exact tsum_nonneg fun _ => by positivity

/-- The exact odd-factorial transform series is uniformly bounded on the inner edge strip
`0 ≤ c²-omega² ≤ 2`. -/
theorem abs_integral_kaiserTrial_cos_le_edgeBound {c omega : ℝ}
    (hinner : 0 ≤ c ^ (2 : ℕ) - omega ^ (2 : ℕ)) (hedge : c ^ (2 : ℕ) - omega ^ (2 : ℕ) ≤ 2) :
    |∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (omega * x)| ≤
      kaiserEdgeTransformBound := by
  rw [integral_kaiserTrial_cos, abs_of_nonneg]
  · exact tsum_oddFactorial_mono hinner hedge
  · exact tsum_nonneg fun _ => by positivity

/-- Corresponding uniform spectral-density bound on the thin inner edge strip. -/
theorem norm_sq_fourier_bandTrunc_kaiser_le_edgeBound {c ξ : ℝ}
    (hinner : 0 ≤ c ^ (2 : ℕ) - (2 * Real.pi * ξ) ^ (2 : ℕ))
    (hedge : c ^ (2 : ℕ) - (2 * Real.pi * ξ) ^ (2 : ℕ) ≤ 2) :
    ‖𝓕 (bandTrunc (kaiserTrial c)) ξ‖ ^ (2 : ℕ) ≤ kaiserEdgeTransformBound ^ (2 : ℕ) := by
  rw [norm_sq_fourier_bandTrunc_of_even (continuous_kaiserTrial c) (kaiserTrial_even c) ξ]
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_integral_kaiserTrial_cos_le_edgeBound hinner hedge) 2

end GaloisForLFunctions.RHTower

end
