import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.GaussianSchwartzScale
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Gaussian Fourier tails controlled by four derivatives

Integration by parts bounds each Fourier monomial by the integrals of the
physical derivatives up to that order. The fourth-order estimate and the
zeroth-order estimate combine into an integrable planar envelope. Its
punctured lattice mass is uniformly bounded, giving the explicit constant
`1632` in terms of the five derivative integrals through order four.
-/

noncomputable section
open Complex MeasureTheory Finset
open scoped Classical SchwartzMap FourierTransform

namespace GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson

/-- Total absolute mass of the physical derivatives through a specified order. -/
def derivativeMass (N : ℕ) (f : 𝓢(ℂ, ℂ)) : ℝ :=
  ∑ j ∈ range (N + 1), ∫ z : ℂ, ‖iteratedFDeriv ℝ j (f : ℂ → ℂ) z‖

/-- Derivative mass is nonnegative. -/
theorem derivativeMass_nonneg (N : ℕ) (f : 𝓢(ℂ, ℂ)) : 0 ≤ derivativeMass N f :=
  sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))

/-- Repeated Fourier integration by parts has no unproved integrability premise. -/
theorem norm_pow_fourier_le_derivativeMass (n : ℕ) (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    ‖z‖ ^ n * ‖(𝓕 f) z‖ ≤ 2 ^ n * derivativeMass n f := by
  rw [congrFun (SchwartzMap.fourier_coe f) z]
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f.smooth ⊤)
    (fun k j _ _ => SchwartzMap.integrable_pow_mul_iteratedFDeriv volume f k j)
    (k := 0) (n := n) le_top le_top z
  simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero,
    zero_add, derivativeMass, sum_product, range_one, sum_singleton] using h

private theorem derivativeMass_zero_le_four (f : 𝓢(ℂ, ℂ)) : derivativeMass 0 f ≤ derivativeMass 4 f := by
  apply sum_le_sum_of_subset_of_nonneg (range_mono (show 0 + 1 ≤ 4 + 1 by omega))
  intro j _ _
  exact integral_nonneg (fun _ => norm_nonneg _)

/-- Five derivative integrals supply the complete fourth-order Fourier envelope. -/
theorem one_add_fourier_fourth_le (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    (1 + ‖z‖) ^ 4 * ‖(𝓕 f) z‖ ≤ 136 * derivativeMass 4 f := by
  have hzero := norm_pow_fourier_le_derivativeMass 0 f z
  simp only [pow_zero, one_mul] at hzero
  have h0 := hzero.trans (derivativeMass_zero_le_four f)
  have h4 := norm_pow_fourier_le_derivativeMass 4 f z
  norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at h4
  have hpoly : (1 + ‖z‖) ^ 4 ≤ 8 * (1 + ‖z‖ ^ 4) := by
    have hq : 0 ≤ 7 * ‖z‖ ^ 2 + 10 * ‖z‖ + 7 := by positivity
    nlinarith only [mul_nonneg (sq_nonneg (‖z‖ - 1)) hq]
  calc
    _ ≤ 8 * (1 + ‖z‖ ^ 4) * ‖(𝓕 f) z‖ :=
      mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
    _ = 8 * (‖(𝓕 f) z‖ + ‖z‖ ^ 4 * ‖(𝓕 f) z‖) := by ring
    _ ≤ 8 * (derivativeMass 4 f + 16 * derivativeMass 4 f) :=
      mul_le_mul_of_nonneg_left (add_le_add h0 h4) (by norm_num)
    _ = _ := by ring

private theorem norm_fourier_tail_le (f : 𝓢(ℂ, ℂ)) (s : PositiveScale) (a : ℂ) (z : GaussianInt) :
    ‖schwartzLatticeTail (𝓕 f) s a z‖ ≤ 136 * derivativeMass 4 f * gaussianTail s z := by
  by_cases hz : z = 0
  · simp [schwartzLatticeTail, gaussianTail, hz]
  · rw [schwartzLatticeTail, if_neg hz, norm_mul, norm_gaussianPhase, one_mul,
      gaussianTail, if_neg hz]
    have h := one_add_fourier_fourth_le f ((s.val : ℂ) * (z : ℂ))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg s.property.le] at h
    have hd : 0 < (1 + s.val * ‖(z : ℂ)‖) ^ 4 := by
      have hs : 0 < s.val := s.property
      positivity
    rw [mul_one_div, le_div_iff₀ hd]
    simpa only [mul_comm] using h

/-- Absolute Fourier tail mass is controlled by physical derivatives through order four. -/
theorem scaled_fourier_tail_mass_le_derivativeMass (f : 𝓢(ℂ, ℂ)) (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * (∑' z : GaussianInt, ‖schwartzLatticeTail (𝓕 f) s a z‖) ≤
      1632 * derivativeMass 4 f := by
  have hm := (summable_gaussianTail s).mul_left (136 * derivativeMass 4 f)
  have hsum := Summable.tsum_le_tsum (norm_fourier_tail_le f s a)
    (summable_norm_schwartzLatticeTail (𝓕 f) s a) hm
  rw [tsum_mul_left] at hsum
  have hC : 0 ≤ 136 * derivativeMass 4 f := mul_nonneg (by norm_num) (derivativeMass_nonneg 4 f)
  calc
    _ ≤ s.val ^ 2 * (136 * derivativeMass 4 f * ∑' z : GaussianInt, gaussianTail s z) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg s.val)
    _ = (136 * derivativeMass 4 f) * (s.val ^ 2 * ∑' z : GaussianInt, gaussianTail s z) := by ring
    _ ≤ (136 * derivativeMass 4 f) * 12 :=
      mul_le_mul_of_nonneg_left (scaled_gaussianTail_le s) hC
    _ = _ := by ring

/-- The zero Fourier mode is the sole term excluded from the derivative estimate. -/
theorem scaled_fourier_mass_sub_zero_le_derivativeMass
    (f : 𝓢(ℂ, ℂ)) (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * ((∑' z : GaussianInt,
      ‖gaussianPhase a z * (𝓕 f) ((s.val : ℂ) * (z : ℂ))‖) - ‖(𝓕 f) 0‖) ≤
      1632 * derivativeMass 4 f := by
  rw [schwartzLattice_mass_eq, add_sub_cancel_left]
  exact scaled_fourier_tail_mass_le_derivativeMass f s a

end GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
