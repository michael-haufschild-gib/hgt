import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapPhaseGeometry
import GaloisForLFunctions.RHTower.RouteRCorrectedMultiplierGammaOrientationDescent

/-!
# Radial phase polarization of the Route-R essential cap

The pre-divisor source phase and the physical Xi phase have the same prime angle.  Their quotient
is the horizontal half-density gain.  This file measures that quotient in the already fixed
completed-Xi same-fibre polarization.

The source phase acts isometrically on the retained nonzero Xi coefficient.  Physical phase
isometry on that same coefficient is equivalent to singular Stokes flatness.  In the two Gamma
orientations, character determinants cancel unconditionally, but the positive energy excess is
the square of the difference of the reciprocal gains times the retained coefficient energy.  Thus
Krein/determinant reciprocity is not the missing law: equality in the positive polarization is.
-/

open Complex

namespace RHTower

noncomputable section

/-- Physical-to-source phase quotient.  It isolates the horizontal gain without changing the
prime angle or the retained Xi coefficient. -/
def ccmRationalAdelicPrimeXiRadialPhaseCorrection
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) /
    ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho

/-- Exact source-phase/radial factorization of the physical half-density character. -/
theorem ccmRationalAdelicPrimeXiRadialPhaseCorrection_mul_source
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiRadialPhaseCorrection p rho *
        ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho =
      bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) := by
  exact div_mul_cancel₀ _
    (ccmRationalAdelicPrimeXiSourcePhaseCharacter_ne_zero p rho)

/-- Modulus of the radial correction is exactly the horizontal half-density gain. -/
theorem norm_ccmRationalAdelicPrimeXiRadialPhaseCorrection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ‖ccmRationalAdelicPrimeXiRadialPhaseCorrection p rho‖ =
      ‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ := by
  rw [ccmRationalAdelicPrimeXiRadialPhaseCorrection, norm_div,
    norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter, div_one]

/-- The radial correction is unitary exactly when the essential cap is singular-Stokes flat. -/
theorem norm_ccmRationalAdelicPrimeXiRadialPhaseCorrection_eq_one_iff_singularStokesFlat
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ‖ccmRationalAdelicPrimeXiRadialPhaseCorrection p rho‖ = 1 ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  rw [norm_ccmRationalAdelicPrimeXiRadialPhaseCorrection,
    norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le]
  constructor
  · intro hre
    apply (ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).2
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2 hre
  · intro hflat
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1
      ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).1 hflat)

/-- One-coordinate positive energy after multiplication by a phase scalar. -/
def ccmRationalAdelicPrimeXiPhasePolarizationEnergy
    (q : XiZeroCopy) (lam c : ℂ) : ℝ :=
  completedXiSameFiberPolarization q (lam * c) (lam * c)

theorem ccmRationalAdelicPrimeXiPhasePolarizationEnergy_eq
    (q : XiZeroCopy) (lam c : ℂ) :
    ccmRationalAdelicPrimeXiPhasePolarizationEnergy q lam c =
      ‖lam‖ ^ 2 * Complex.normSq c := by
  rw [ccmRationalAdelicPrimeXiPhasePolarizationEnergy,
    completedXiSameFiberPolarization_self, Complex.normSq_mul,
    Complex.normSq_eq_norm_sq]

/-- Positive energy of the canonical source phase on the retained Xi atom. -/
def ccmRationalAdelicPrimeXiSourcePhaseEnergy
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℝ :=
  ccmRationalAdelicPrimeXiPhasePolarizationEnergy
    (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
    (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho)
    (ccmRationalAdelicPrimeXiCartierCoefficient rho)

/-- Positive energy of the physical half-density phase on the same retained Xi atom. -/
def ccmRationalAdelicPrimeXiPhysicalPhaseEnergy
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℝ :=
  ccmRationalAdelicPrimeXiPhasePolarizationEnergy
    (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)
    (bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ))
    (ccmRationalAdelicPrimeXiCartierCoefficient rho)

/-- Pre-divisor source phase is an unconditional positive isometry on the retained coefficient. -/
theorem ccmRationalAdelicPrimeXiSourcePhaseEnergy_eq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourcePhaseEnergy p rho =
      Complex.normSq (ccmRationalAdelicPrimeXiCartierCoefficient rho) := by
  rw [ccmRationalAdelicPrimeXiSourcePhaseEnergy,
    ccmRationalAdelicPrimeXiPhasePolarizationEnergy_eq,
    norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter]
  norm_num

theorem ccmRationalAdelicPrimeXiPhysicalPhaseEnergy_eq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPhysicalPhaseEnergy p rho =
      ‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ ^ 2 *
        Complex.normSq (ccmRationalAdelicPrimeXiCartierCoefficient rho) := by
  rw [ccmRationalAdelicPrimeXiPhysicalPhaseEnergy,
    ccmRationalAdelicPrimeXiPhasePolarizationEnergy_eq]

/-- Same-fibre positive phase isometry on the retained atom is exactly singular Stokes flatness. -/
theorem ccmRationalAdelicPrimeXiPhysicalPhaseEnergy_eq_source_iff_singularStokesFlat
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPhysicalPhaseEnergy p rho =
        ccmRationalAdelicPrimeXiSourcePhaseEnergy p rho ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  rw [ccmRationalAdelicPrimeXiPhysicalPhaseEnergy_eq,
    ccmRationalAdelicPrimeXiSourcePhaseEnergy_eq]
  let lam := bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)
  let c := ccmRationalAdelicPrimeXiCartierCoefficient rho
  have hc : 0 < Complex.normSq c :=
    Complex.normSq_pos.mpr (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho)
  constructor
  · intro henergy
    have hsq : ‖lam‖ ^ 2 = 1 := by
      apply mul_right_cancel₀ hc.ne'
      simpa [lam, c] using henergy
    have hnorm : ‖lam‖ = 1 := by
      nlinarith [norm_nonneg lam]
    exact
      (norm_ccmRationalAdelicPrimeXiRadialPhaseCorrection_eq_one_iff_singularStokesFlat
        p rho).1 (by
          rw [norm_ccmRationalAdelicPrimeXiRadialPhaseCorrection]
          exact hnorm)
  · intro hflat
    have hnorm : ‖lam‖ = 1 := by
      exact (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le _).2
        ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1
          ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).1 hflat))
    rw [show ‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ = 1 by
      simpa [lam] using hnorm]
    norm_num

/-- Gamma reflection makes the two physical radial gains reciprocal.  This determinant-level law
is unconditional and therefore cannot by itself annihilate the cap. -/
theorem ccmRationalAdelicPrimeXiPhysicalPhaseNorm_mul_reflection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ *
        ‖bilateralHalfDensityCharacter (p : ℕ)
          (xiZeroReflectEquiv rho : ℂ)‖ = 1 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [norm_bilateralHalfDensityCharacter (by exact_mod_cast p.2.pos),
    norm_bilateralHalfDensityCharacter (by exact_mod_cast p.2.pos),
    xiZeroReflectEquiv_apply]
  simp only [Complex.sub_re, Complex.one_re]
  rw [← Real.rpow_add hpR]
  convert Real.rpow_zero (p : ℝ) using 1
  ring

/-- Functional-equation parity preserves the positive energy of the retained Xi coefficient. -/
theorem normSq_ccmRationalAdelicPrimeXiCartierCoefficient_reflection
    (rho : XiDivisorSupport) :
    Complex.normSq (ccmRationalAdelicPrimeXiCartierCoefficient
      (xiZeroReflectEquiv rho)) =
      Complex.normSq (ccmRationalAdelicPrimeXiCartierCoefficient rho) := by
  rw [ccmRationalAdelicPrimeXiCartierCoefficient_reflection,
    Complex.normSq_eq_norm_sq, norm_mul, norm_pow,
    Complex.normSq_eq_norm_sq]
  simp

/-- Positive physical phase energy in both Gamma orientations. -/
def ccmRationalAdelicPrimeXiGammaPairedPhysicalPhaseEnergy
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℝ :=
  ccmRationalAdelicPrimeXiPhysicalPhaseEnergy p rho +
    ccmRationalAdelicPrimeXiPhysicalPhaseEnergy p (xiZeroReflectEquiv rho)

/-- Corresponding unitary source-phase energy in both Gamma orientations. -/
def ccmRationalAdelicPrimeXiGammaPairedSourcePhaseEnergy
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℝ :=
  ccmRationalAdelicPrimeXiSourcePhaseEnergy p rho +
    ccmRationalAdelicPrimeXiSourcePhaseEnergy p (xiZeroReflectEquiv rho)

/-- Exact positive two-orientation excess.  Reciprocal determinant cancellation leaves the square
of the gain mismatch, so a second Gamma orientation cannot erase the physical port. -/
theorem ccmRationalAdelicPrimeXiGammaPairedPhaseEnergy_sub_source
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiGammaPairedPhysicalPhaseEnergy p rho -
        ccmRationalAdelicPrimeXiGammaPairedSourcePhaseEnergy p rho =
      (‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ -
          ‖bilateralHalfDensityCharacter (p : ℕ)
            (xiZeroReflectEquiv rho : ℂ)‖) ^ 2 *
        Complex.normSq (ccmRationalAdelicPrimeXiCartierCoefficient rho) := by
  rw [ccmRationalAdelicPrimeXiGammaPairedPhysicalPhaseEnergy,
    ccmRationalAdelicPrimeXiGammaPairedSourcePhaseEnergy,
    ccmRationalAdelicPrimeXiPhysicalPhaseEnergy_eq,
    ccmRationalAdelicPrimeXiPhysicalPhaseEnergy_eq,
    ccmRationalAdelicPrimeXiSourcePhaseEnergy_eq,
    ccmRationalAdelicPrimeXiSourcePhaseEnergy_eq,
    normSq_ccmRationalAdelicPrimeXiCartierCoefficient_reflection]
  have hrecip := ccmRationalAdelicPrimeXiPhysicalPhaseNorm_mul_reflection p rho
  let a := ‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖
  let b := ‖bilateralHalfDensityCharacter (p : ℕ)
    (xiZeroReflectEquiv rho : ℂ)‖
  let C := Complex.normSq (ccmRationalAdelicPrimeXiCartierCoefficient rho)
  change a ^ 2 * C + b ^ 2 * C - (C + C) = (a - b) ^ 2 * C
  change a * b = 1 at hrecip
  calc
    a ^ 2 * C + b ^ 2 * C - (C + C) =
        (a ^ 2 + b ^ 2 - 2) * C := by ring
    _ = (a ^ 2 + b ^ 2 - 2 * (a * b)) * C := by simp [hrecip]
    _ = (a - b) ^ 2 * C := by ring

theorem ccmRationalAdelicPrimeXiGammaPairedSourcePhaseEnergy_le_physical
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiGammaPairedSourcePhaseEnergy p rho ≤
      ccmRationalAdelicPrimeXiGammaPairedPhysicalPhaseEnergy p rho := by
  rw [← sub_nonneg]
  rw [ccmRationalAdelicPrimeXiGammaPairedPhaseEnergy_sub_source]
  exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)

/-- Equality in the transported positive polarization, simultaneously in both Gamma orientations,
is exactly singular Stokes flatness. -/
theorem ccmRationalAdelicPrimeXiGammaPairedPhysicalPhaseEnergy_eq_source_iff_singularStokesFlat
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiGammaPairedPhysicalPhaseEnergy p rho =
        ccmRationalAdelicPrimeXiGammaPairedSourcePhaseEnergy p rho ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  rw [← sub_eq_zero,
    ccmRationalAdelicPrimeXiGammaPairedPhaseEnergy_sub_source]
  have hc :
      Complex.normSq (ccmRationalAdelicPrimeXiCartierCoefficient rho) ≠ 0 :=
    (Complex.normSq_pos.mpr
      (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho)).ne'
  rw [mul_eq_zero, or_iff_left hc, sq_eq_zero_iff, sub_eq_zero]
  constructor
  · intro heq
    have hrecip := ccmRationalAdelicPrimeXiPhysicalPhaseNorm_mul_reflection p rho
    have hnorm : ‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ = 1 := by
      nlinarith [norm_nonneg
        (bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ))]
    exact
      (norm_ccmRationalAdelicPrimeXiRadialPhaseCorrection_eq_one_iff_singularStokesFlat
        p rho).1 (by
          rw [norm_ccmRationalAdelicPrimeXiRadialPhaseCorrection]
          exact hnorm)
  · intro hflat
    have hre : (rho : ℂ).re = 1 / 2 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1
        ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).1 hflat)
    have hnorm : ‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ = 1 :=
      (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le _).2 hre
    have href :
        ‖bilateralHalfDensityCharacter (p : ℕ)
          (xiZeroReflectEquiv rho : ℂ)‖ = 1 := by
      apply (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le _).2
      rw [xiZeroReflectEquiv_apply]
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    rw [hnorm, href]

end

end RHTower
