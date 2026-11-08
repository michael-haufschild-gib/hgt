import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanStripBounds
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart

/-!
# Vertical decay of the actual averaged Narain Mellin transform

The exact filled-numerator quotient isolates the reciprocal-zeta loss.
All remaining factors retain exponential decay on fixed vertical strips.
-/

open Complex RHTower
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The exact averaged quotient away from the universal main pole. -/
theorem narainMellinMean_eq_filled_quotient (Y Z : Height) {u : ℂ}
    (hu : u ≠ 1 / 2) :
    narainMellinMean Y Z u =
      filledNumeratorMean Y u * filledNumeratorMean Z u /
        (2 * (u * (1 + 2 * u)) * xi (1 + 2 * u) * (u - 1 / 2) ^ 2) := by
  have htwo : 2 * u - 1 ≠ 0 := by
    intro h
    apply hu
    linear_combination h / 2
  have h := narainMeanMainPoleNumerator_eq Y Z htwo
  rw [← div_div]
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hu))).mpr
  change narainMellinMean Y Z u * (u - 1 / 2) ^ 2 =
    narainMeanMainPoleNumerator Y Z u
  rw [h, mul_comm]

/-- Away from the real axis the elementary denominator factors only improve the bound. -/
theorem norm_narainMellinMean_le_filled (Y Z : Height) {u : ℂ} (ht : 1 ≤ |u.im|) :
    ‖narainMellinMean Y Z u‖ ≤
      ‖filledNumeratorMean Y u‖ * ‖filledNumeratorMean Z u‖ * ‖(xi (1 + 2 * u))⁻¹‖ := by
  have hu : u ≠ 1 / 2 := by
    intro h
    norm_num [h] at ht
  have h₀ : 1 ≤ ‖u‖ := ht.trans (Complex.abs_im_le_norm u)
  have h₁ : 1 ≤ ‖1 + 2 * u‖ := by
    have h := Complex.abs_im_le_norm (1 + 2 * u)
    have him : (1 + 2 * u).im = 2 * u.im := by simp
    rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith only [ht, h]
  have h₂ : 1 ≤ ‖u - 1 / 2‖ := by
    have h := Complex.abs_im_le_norm (u - 1 / 2)
    exact ht.trans (by simpa using h)
  rw [narainMellinMean_eq_filled_quotient Y Z hu]
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
  rw [norm_inv]
  have hp : (1 : ℝ) ≤ ‖u‖ * ‖1 + 2 * u‖ := by
    simpa using mul_le_mul h₀ h₁ zero_le_one (norm_nonneg u)
  have hq : (1 : ℝ) ≤ ‖u - 1 / 2‖ ^ 2 := by
    nlinarith only [h₂, sq_nonneg (‖u - 1 / 2‖ - 1)]
  have hd : 1 ≤ 2 * (‖u‖ * ‖1 + 2 * u‖) * ‖u - 1 / 2‖ ^ 2 := by
    have h := mul_le_mul hp hq zero_le_one
      (mul_nonneg (norm_nonneg u) (norm_nonneg (1 + 2 * u)))
    nlinarith only [h]
  calc
    _ = (‖filledNumeratorMean Y u‖ * ‖filledNumeratorMean Z u‖ * ‖xi (1 + 2 * u)‖⁻¹) /
        (2 * (‖u‖ * ‖1 + 2 * u‖) * ‖u - 1 / 2‖ ^ 2) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := div_le_self (by positivity) hd

/-- The averaged Mellin transform keeps exponential decay after the inverse xi factor. -/
theorem exists_narainMellinMean_strip_bound (Y Z : Height) {B : ℝ} (hB : 0 ≤ B) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ u : ℂ, |u.re| ≤ B → 1 ≤ |u.im| →
      ‖narainMellinMean Y Z u‖ ≤ C * (1 + |u.im|) ^ N *
        Real.exp (-(Real.pi * |u.im| / 2)) * ‖(riemannZeta (1 + 2 * u))⁻¹‖ := by
  obtain ⟨CY, NY, hCY, hY⟩ := exists_filledNumeratorMean_strip_bound Y hB
  obtain ⟨CZ, NZ, hCZ, hZ⟩ := exists_filledNumeratorMean_strip_bound Z hB
  obtain ⟨CD, ND, hCD, hD⟩ := exists_exp_mul_norm_inv_xi_le (1 - 2 * B) (1 + 2 * B)
  refine ⟨CY * CZ * CD, NY + NZ + ND, by positivity, ?_⟩
  intro u hu ht
  have hre := abs_le.mp hu
  have hY' := hY u hu ht
  have hZ' := hZ u hu ht
  have hD' := hD u (by simp; linarith only [hre.1])
    (by simp; linarith only [hre.2]) ht
  calc
    _ ≤ ‖filledNumeratorMean Y u‖ * ‖filledNumeratorMean Z u‖ *
        ‖(xi (1 + 2 * u))⁻¹‖ := norm_narainMellinMean_le_filled Y Z ht
    _ ≤ (CY * (1 + |u.im|) ^ NY * Real.exp (-(Real.pi * |u.im| / 2))) *
        (CZ * (1 + |u.im|) ^ NZ * Real.exp (-(Real.pi * |u.im| / 2))) *
        ‖(xi (1 + 2 * u))⁻¹‖ := by gcongr
    _ = (CY * CZ * (1 + |u.im|) ^ (NY + NZ) * Real.exp (-(Real.pi * |u.im| / 2))) *
        (Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖) := by
      rw [pow_add]
      ring
    _ ≤ (CY * CZ * (1 + |u.im|) ^ (NY + NZ) * Real.exp (-(Real.pi * |u.im| / 2))) *
        (CD * (1 + |u.im|) ^ ND * ‖(riemannZeta (1 + 2 * u))⁻¹‖) :=
      mul_le_mul_of_nonneg_left hD' (by positivity)
    _ = _ := by rw [pow_add]; ring

#print axioms exists_narainMellinMean_strip_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
