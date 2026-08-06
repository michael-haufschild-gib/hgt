import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapSingularStokesLaw
import GaloisForLFunctions.RHTower.BilateralModerationXiDivisorBridge

/-!
# Phase-geometric source boundary for the Route-R essential cap

The pre-divisor Cartier source retains the nonzero leading Xi coefficient but has unit geometric
dilation gain.  This module separates the part of the physical half-density character which the
source supplies unconditionally: its Xi-height phase.

For every actual Xi support point and ordinary prime, the resulting bilateral source orbit is
nonzero, polynomially moderate, and satisfies the unitary prime-angle sewing law.  The same fixed
orbit satisfies the physical half-density sewing law exactly when the prime-log essential cap is
singular-Stokes flat.  Equivalently, any nonzero moderate physical sewing orbit produces singular
flatness.

Thus phase regularity and source non-erasure are unconditional.  The remaining RH-strength datum
is precisely physical sewing of the already constructed source phase orbit; no norm identity,
fixed-ideal preservation, or critical-line premise is hidden in the construction.
-/

open Complex

namespace RHTower

noncomputable section

/-- Fixed-circle representative of the Xi height: discard horizontal displacement while retaining
the complete vertical phase. -/
def ccmRationalAdelicPrimeXiSourcePhasePoint
    (rho : XiDivisorSupport) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (rho : ℂ).im * Complex.I

@[simp]
theorem ccmRationalAdelicPrimeXiSourcePhasePoint_re
    (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeXiSourcePhasePoint rho).re = 1 / 2 := by
  simp [ccmRationalAdelicPrimeXiSourcePhasePoint]

@[simp]
theorem ccmRationalAdelicPrimeXiSourcePhasePoint_im
    (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeXiSourcePhasePoint rho).im = (rho : ℂ).im := by
  simp [ccmRationalAdelicPrimeXiSourcePhasePoint]

/-- Unitary prime-angle character supplied by source height phase. -/
def ccmRationalAdelicPrimeXiSourcePhaseCharacter
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  bilateralHalfDensityCharacter (p : ℕ)
    (ccmRationalAdelicPrimeXiSourcePhasePoint rho)

theorem norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ‖ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho‖ = 1 := by
  exact (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le _).2
    (ccmRationalAdelicPrimeXiSourcePhasePoint_re rho)

theorem ccmRationalAdelicPrimeXiSourcePhaseCharacter_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho ≠ 0 := by
  intro h
  have hnorm := norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho
  rw [h, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- Coefficient-faithful bilateral source phase orbit.  Its origin is the first nonzero Xi jet
retained by the pre-divisor rational Cartier functor. -/
def ccmRationalAdelicPrimeXiSourcePhaseOrbit
    (p : Nat.Primes) (rho : XiDivisorSupport) (e : ℤ) : ℂ :=
  bilateralEigenFamily
      (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho) e *
    ccmRationalAdelicPrimeXiCartierCoefficient rho

@[simp]
theorem ccmRationalAdelicPrimeXiSourcePhaseOrbit_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho 0 =
      ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  simp [ccmRationalAdelicPrimeXiSourcePhaseOrbit, bilateralEigenFamily]

theorem ccmRationalAdelicPrimeXiSourcePhaseOrbit_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [ccmRationalAdelicPrimeXiSourcePhaseOrbit_zero, Pi.zero_apply] at h0
  exact ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho h0

/-- The source phase orbit is an actual polynomially moderate fixed-circle boundary. -/
theorem ccmRationalAdelicPrimeXiSourcePhaseOrbit_moderate
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    bilateralModerate (ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho) := by
  refine ⟨‖ccmRationalAdelicPrimeXiCartierCoefficient rho‖, 0, fun e ↦ ?_⟩
  rw [pow_zero, mul_one, ccmRationalAdelicPrimeXiSourcePhaseOrbit, norm_mul,
    bilateralEigenFamily, norm_zpow,
    norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter, one_zpow, one_mul]

/-- Exact unitary phase sewing before physical horizontal gain is imposed. -/
theorem ccmRationalAdelicPrimeXiSourcePhaseOrbit_sewing
    (p : Nat.Primes) (rho : XiDivisorSupport) (e : ℤ) :
    ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho (e - 1) =
      ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho *
        ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho e := by
  rw [ccmRationalAdelicPrimeXiSourcePhaseOrbit,
    ccmRationalAdelicPrimeXiSourcePhaseOrbit,
    bilateralEigenFamily_sewing
      (ccmRationalAdelicPrimeXiSourcePhaseCharacter_ne_zero p rho) e]
  ring

/-- A nonzero moderate phase boundary carrying the physical half-density character.  Unlike a
fixed norm or ideal assertion, this only asks for distributional prime-angle sewing. -/
def CCMRationalAdelicPrimeXiPhysicalPhaseModerateLanding
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  ∃ c : ℤ → ℂ, c ≠ 0 ∧ bilateralModerate c ∧
    ∀ e : ℤ,
      c (e - 1) = bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) * c e

/-- Any source construction of a nonzero moderate physical phase orbit annihilates the essential
cap. -/
theorem ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_of_phaseModerateLanding
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (h : CCMRationalAdelicPrimeXiPhysicalPhaseModerateLanding p rho) :
    CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  rcases h with ⟨c, hc, hmod, hsew⟩
  have hre : (rho : ℂ).re = 1 / 2 :=
    re_eq_half_of_moderate_bilateral_eigen p.2.two_le hc hmod hsew
  apply (ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).2
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2 hre

/-- Singular flatness supplies the canonical source phase orbit as a physical moderate landing. -/
theorem ccmRationalAdelicPrimeXiPhysicalPhaseModerateLanding_of_singularStokesFlat
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hflat : CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho) :
    CCMRationalAdelicPrimeXiPhysicalPhaseModerateLanding p rho := by
  have hre : (rho : ℂ).re = 1 / 2 :=
    (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1
      ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).1 hflat)
  have hpoint : ccmRationalAdelicPrimeXiSourcePhasePoint rho = (rho : ℂ) := by
    apply Complex.ext
    · rw [ccmRationalAdelicPrimeXiSourcePhasePoint_re, hre]
    · rw [ccmRationalAdelicPrimeXiSourcePhasePoint_im]
  refine ⟨ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho,
    ccmRationalAdelicPrimeXiSourcePhaseOrbit_ne_zero p rho,
    ccmRationalAdelicPrimeXiSourcePhaseOrbit_moderate p rho, ?_⟩
  intro e
  rw [ccmRationalAdelicPrimeXiSourcePhaseOrbit_sewing]
  rw [ccmRationalAdelicPrimeXiSourcePhaseCharacter, hpoint]

/-- Exact phase-geometric presentation of Route R's remaining singular law. -/
theorem ccmRationalAdelicPrimeXiPhysicalPhaseModerateLanding_iff_singularStokesFlat
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiPhysicalPhaseModerateLanding p rho ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho :=
  ⟨ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_of_phaseModerateLanding p rho,
    ccmRationalAdelicPrimeXiPhysicalPhaseModerateLanding_of_singularStokesFlat p rho⟩

/-- The already constructed coefficient-faithful source phase orbit obeys physical sewing exactly
when the essential cap is singular-Stokes flat. -/
theorem ccmRationalAdelicPrimeXiSourcePhaseOrbit_physicalSewing_iff_singularStokesFlat
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (∀ e : ℤ,
      ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho (e - 1) =
        bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) *
          ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho e) ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  constructor
  · intro hsew
    exact ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_of_phaseModerateLanding
      p rho ⟨ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho,
        ccmRationalAdelicPrimeXiSourcePhaseOrbit_ne_zero p rho,
        ccmRationalAdelicPrimeXiSourcePhaseOrbit_moderate p rho, hsew⟩
  · intro hflat
    have hre : (rho : ℂ).re = 1 / 2 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1
        ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).1 hflat)
    have hpoint : ccmRationalAdelicPrimeXiSourcePhasePoint rho = (rho : ℂ) := by
      apply Complex.ext
      · rw [ccmRationalAdelicPrimeXiSourcePhasePoint_re, hre]
      · rw [ccmRationalAdelicPrimeXiSourcePhasePoint_im]
    intro e
    rw [ccmRationalAdelicPrimeXiSourcePhaseOrbit_sewing]
    rw [ccmRationalAdelicPrimeXiSourcePhaseCharacter, hpoint]

end

end RHTower
