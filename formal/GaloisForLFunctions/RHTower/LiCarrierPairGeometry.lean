import GaloisForLFunctions.RHTower.LiRemoteQuartetProfile
import GaloisForLFunctions.HTGeometry.CirclePowerEstimates

/-!
# Critical-line Li pair geometry

This module isolates the elementary contribution of one critical-line Schwarz pair.  Its Li
Möbius coordinate lies on the unit circle, so the paired contribution is both the usual real-part
expression and a squared chord length.  The unit-circle power Lipschitz estimate then gives the
exact quadratic reciprocal-height majorant used in the reflected-Gamma carrier sum.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Li Möbius coordinate of the upper critical-line point `1/2 + i gamma`. -/
def liCarrierCoordinate (gamma : ℝ) : ℂ :=
  liMobiusCoordinate (((1 / 2 : ℝ) : ℂ) + (gamma : ℂ) * Complex.I)

/-- Squared-chord contribution of the critical-line pair `1/2 ± i gamma`. -/
def liCarrierPairContribution (n : ℕ) (gamma : ℝ) : ℝ :=
  ‖1 - (liCarrierCoordinate gamma) ^ n‖ ^ (2 : ℕ)

/-- The critical-line Li coordinate has squared norm one. -/
theorem normSq_liCarrierCoordinate {gamma : ℝ} (hgamma : gamma ≠ 0) :
    Complex.normSq (liCarrierCoordinate gamma) = 1 := by
  rw [liCarrierCoordinate,
    normSq_liMobiusCoordinate_realPart_height (beta := (1 / 2 : ℝ)) hgamma]
  have hden : gamma ^ (2 : ℕ) + 1 / 4 ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- The critical-line Li coordinate lies on the unit circle. -/
theorem norm_liCarrierCoordinate {gamma : ℝ} (hgamma : gamma ≠ 0) :
    ‖liCarrierCoordinate gamma‖ = 1 := by
  have hsq : ‖liCarrierCoordinate gamma‖ ^ (2 : ℕ) = 1 := by
    rw [Complex.sq_norm, normSq_liCarrierCoordinate hgamma]
  nlinarith [norm_nonneg (liCarrierCoordinate gamma)]

/-- Exact reciprocal-height length of the first Li chord. -/
theorem norm_one_sub_liCarrierCoordinate_sq {gamma : ℝ} (hgamma : gamma ≠ 0) :
    ‖1 - liCarrierCoordinate gamma‖ ^ (2 : ℕ) = 1 / (gamma ^ (2 : ℕ) + 1 / 4) := by
  let rho : ℂ := ((1 / 2 : ℝ) : ℂ) + (gamma : ℂ) * Complex.I
  have hrho : rho ≠ 0 := by
    intro h
    have hi : rho.im = 0 := by rw [h]; simp
    simp [rho] at hi
    exact hgamma hi
  have hsub : (1 : ℂ) - liCarrierCoordinate gamma = rho⁻¹ := by
    rw [liCarrierCoordinate, liMobiusCoordinate]
    simp [rho]
  rw [hsub, norm_inv, inv_pow]
  have hnormsq : ‖rho‖ ^ (2 : ℕ) = gamma ^ (2 : ℕ) + 1 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [rho]
    ring
  rw [hnormsq]
  simp only [one_div]

/-- Card equation `(18)`: squared chord length equals the paired real-part contribution. -/
theorem liCarrierPairContribution_eq_two_sub_two_re {n : ℕ} {gamma : ℝ}
    (hgamma : gamma ≠ 0) :
    liCarrierPairContribution n gamma =
      2 - 2 * ((liCarrierCoordinate gamma) ^ n).re := by
  have hnorm : ‖(liCarrierCoordinate gamma) ^ n‖ = 1 := by
    rw [norm_pow, norm_liCarrierCoordinate hgamma, one_pow]
  have hsq : ((liCarrierCoordinate gamma) ^ n).re ^ (2 : ℕ) +
      ((liCarrierCoordinate gamma) ^ n).im ^ (2 : ℕ) = 1 := by
    have h := Complex.sq_norm ((liCarrierCoordinate gamma) ^ n)
    rw [hnorm, one_pow, Complex.normSq_apply] at h
    nlinarith
  rw [liCarrierPairContribution, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    zero_sub]
  nlinarith

/-- Every critical-line pair contribution is nonnegative. -/
theorem liCarrierPairContribution_nonneg (n : ℕ) (gamma : ℝ) :
    0 ≤ liCarrierPairContribution n gamma := by
  exact sq_nonneg _

/-- Uniform chord bound for one critical-line pair. -/
theorem liCarrierPairContribution_le_four {n : ℕ} {gamma : ℝ}
    (hgamma : gamma ≠ 0) :
    liCarrierPairContribution n gamma ≤ 4 := by
  have hnormpow : ‖(liCarrierCoordinate gamma) ^ n‖ = 1 := by
    rw [norm_pow, norm_liCarrierCoordinate hgamma, one_pow]
  have hnorm : ‖(1 : ℂ) - (liCarrierCoordinate gamma) ^ n‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) - (liCarrierCoordinate gamma) ^ n‖
          ≤ ‖(1 : ℂ)‖ + ‖(liCarrierCoordinate gamma) ^ n‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, hnormpow]; norm_num
  rw [liCarrierPairContribution]
  nlinarith [norm_nonneg ((1 : ℂ) - (liCarrierCoordinate gamma) ^ n)]

/-- Power-Lipschitz quadratic reciprocal-height bound for one critical-line pair. -/
theorem liCarrierPairContribution_le_quadratic {n : ℕ} {gamma : ℝ}
    (hgamma : gamma ≠ 0) :
    liCarrierPairContribution n gamma ≤
      (n : ℝ) ^ (2 : ℕ) / (gamma ^ (2 : ℕ) + 1 / 4) := by
  have hpow := GaloisForLFunctions.norm_pow_sub_pow_le_of_norm_one
    (z := (1 : ℂ)) (w := liCarrierCoordinate gamma) (by simp)
    (norm_liCarrierCoordinate hgamma) n
  simp only [one_pow] at hpow
  have hbase := norm_one_sub_liCarrierCoordinate_sq hgamma
  rw [liCarrierPairContribution]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnorm : 0 ≤ ‖(1 : ℂ) - (liCarrierCoordinate gamma) ^ n‖ := norm_nonneg _
  calc
    ‖(1 : ℂ) - (liCarrierCoordinate gamma) ^ n‖ ^ (2 : ℕ)
        ≤ ((n : ℝ) * ‖(1 : ℂ) - liCarrierCoordinate gamma‖) ^ (2 : ℕ) := by nlinarith
    _ = (n : ℝ) ^ (2 : ℕ) / (gamma ^ (2 : ℕ) + 1 / 4) := by
      rw [mul_pow, hbase]
      ring

/-- Card equation `(19)`: simultaneous universal and reciprocal-height bound. -/
theorem liCarrierPairContribution_le_min {n : ℕ} {gamma : ℝ}
    (hgamma : gamma ≠ 0) :
    liCarrierPairContribution n gamma ≤
      min 4 ((n : ℝ) ^ (2 : ℕ) / (gamma ^ (2 : ℕ) + 1 / 4)) := by
  exact le_min (liCarrierPairContribution_le_four hgamma)
    (liCarrierPairContribution_le_quadratic hgamma)

end

end RHTower
