import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapReflectedPhaseHermiticity
import GaloisForLFunctions.RHTower.RouteRPreDivisorRationalCartierSourceFunctor

/-!
# Reflection-quadrature phase port for Route R

One reflected trace has a phase-node escape: `z + z⁻¹` may be real because `z` itself is real,
even when `‖z‖ ≠ 1`.  The independent oriented quadrature `i (z - z⁻¹)` removes that escape.
The sum of the two squared imaginary parts is exactly

`(‖z‖ - ‖z⁻¹‖)²`.

For the physical half-density character this is precisely the reciprocal Gamma-orientation gain
mismatch already appearing in Route R's positive paired polarization excess.  The corresponding
two source-height quadratures are real unconditionally.  Thus one ordinary prime suffices: joint
source-to-physical Hermiticity of the even and oriented odd quadratures is singular Stokes
flatness, with no phase-node exception and no critical-line premise.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact algebraic value of the two reciprocal reflection quadratures. -/
theorem reciprocalPhaseQuadraturePort_eq_normSq
    {z : ℂ} (hz : z ≠ 0) :
    (z + z⁻¹).im ^ 2 + (I * (z - z⁻¹)).im ^ 2 =
      (Complex.normSq z - 1) ^ 2 / Complex.normSq z := by
  have hN : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  rw [Complex.add_im, Complex.inv_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul,
    Complex.sub_re, Complex.inv_re]
  field_simp [hN]
  rw [Complex.normSq_apply]
  ring

theorem reciprocalPhaseQuadraturePort_eq_norm_sub_inv_sq
    {z : ℂ} (hz : z ≠ 0) :
    (z + z⁻¹).im ^ 2 + (I * (z - z⁻¹)).im ^ 2 =
      (‖z‖ - ‖z⁻¹‖) ^ 2 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [reciprocalPhaseQuadraturePort_eq_normSq hz, norm_inv,
    Complex.normSq_eq_norm_sq]
  field_simp

theorem reciprocalPhaseQuadraturePort_eq_zero_iff_norm_eq_one
    {z : ℂ} (hz : z ≠ 0) :
    (z + z⁻¹).im ^ 2 + (I * (z - z⁻¹)).im ^ 2 = 0 ↔
      ‖z‖ = 1 := by
  rw [reciprocalPhaseQuadraturePort_eq_normSq hz]
  have hN : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  rw [div_eq_zero_iff, or_iff_left hN, sq_eq_zero_iff, sub_eq_zero,
    Complex.normSq_eq_norm_sq]
  constructor
  · intro hs
    nlinarith [norm_nonneg z]
  · intro hn
    rw [hn]
    norm_num

/-- The oriented odd reciprocal quadrature is real on a unitary source phase. -/
theorem orientedReciprocalPhaseMoment_im_eq_zero_of_norm_eq_one
    {z : ℂ} (hnorm : ‖z‖ = 1) :
    (I * (z - z⁻¹)).im = 0 := by
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    Complex.sub_re, Complex.inv_re, hsq]
  ring

/-- Oriented odd physical reflection moment. -/
def ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  I * (bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) -
    bilateralHalfDensityCharacter (p : ℕ) (xiZeroReflectEquiv rho : ℂ))

/-- Oriented odd source-height reflection moment. -/
def ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  I * (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho -
    ccmRationalAdelicPrimeXiSourcePhaseCharacter p (xiZeroReflectEquiv rho))

/-- Both even and oriented odd source moments are Hermitian unconditionally. -/
theorem ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment_im_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment p rho).im = 0 := by
  rw [ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment,
    ccmRationalAdelicPrimeXiSourcePhaseCharacter_reflection_eq_inv]
  exact orientedReciprocalPhaseMoment_im_eq_zero_of_norm_eq_one
    (norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho)

/-- Positive one-prime port containing both reflection quadratures. -/
def ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℝ :=
  (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho).im ^ 2 +
    (ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p rho).im ^ 2

/-- Corresponding source-height quadrature port. -/
def ccmRationalAdelicPrimeXiReflectedSourcePhaseQuadraturePort
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℝ :=
  (ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment p rho).im ^ 2 +
    (ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment p rho).im ^ 2

theorem ccmRationalAdelicPrimeXiReflectedSourcePhaseQuadraturePort_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedSourcePhaseQuadraturePort p rho = 0 := by
  rw [ccmRationalAdelicPrimeXiReflectedSourcePhaseQuadraturePort,
    ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment_im_eq_zero,
    ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment_im_eq_zero]
  norm_num

/-- The phase quadrature port is exactly the reciprocal positive gain mismatch. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_normMismatch
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort p rho =
      (‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ -
        ‖bilateralHalfDensityCharacter (p : ℕ)
          (xiZeroReflectEquiv rho : ℂ)‖) ^ 2 := by
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment,
    ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv]
  exact reciprocalPhaseQuadraturePort_eq_norm_sub_inv_sq
    (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (by exact_mod_cast p.2.ne_zero)))

/-- The same phase port is the normalized square of the Deninger mate-gain defect.  This is the
direct scalar bridge from reflection quadratures to the singular Bockstein channel. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_mateGainDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort p rho =
      (deningerHalfDensityMateGain (p : ℕ) (rho : ℂ) - 1) ^ 2 /
        deningerHalfDensityMateGain (p : ℕ) (rho : ℂ) := by
  have hz : bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (by exact_mod_cast p.2.ne_zero))
  have hn : ‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hz
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment,
    ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv,
    reciprocalPhaseQuadraturePort_eq_normSq hz,
    Complex.normSq_eq_norm_sq,
    deningerHalfDensityMateGain_eq_norm_inv_sq p.2.pos]
  field_simp
  ring

/-- Exact identification with Route R's already transported positive paired polarization excess. -/
theorem ccmRationalAdelicPrimeXiGammaPairedPhaseEnergy_sub_source_eq_quadraturePort
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiGammaPairedPhysicalPhaseEnergy p rho -
        ccmRationalAdelicPrimeXiGammaPairedSourcePhaseEnergy p rho =
      ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort p rho *
        Complex.normSq (ccmRationalAdelicPrimeXiCartierCoefficient rho) := by
  rw [ccmRationalAdelicPrimeXiGammaPairedPhaseEnergy_sub_source,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_normMismatch]

/-- Exact coefficient-faithful source identity: mate gain times positive phase-polarization excess
is the norm-square of the explicit pre-divisor Cartier/Bockstein comparison defect. -/
theorem ccmRationalAdelicPrimeXiMateGain_mul_phaseEnergyExcess_eq_sourceDefectNormSq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerHalfDensityMateGain (p : ℕ) (rho : ℂ) *
        (ccmRationalAdelicPrimeXiGammaPairedPhysicalPhaseEnergy p rho -
          ccmRationalAdelicPrimeXiGammaPairedSourcePhaseEnergy p rho) =
      Complex.normSq
        (ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho) := by
  rw [ccmRationalAdelicPrimeXiGammaPairedPhaseEnergy_sub_source_eq_quadraturePort,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_mateGainDefect,
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq,
    Complex.normSq_mul]
  have hg : deningerHalfDensityMateGain (p : ℕ) (rho : ℂ) ≠ 0 :=
    (deningerHalfDensityMateGain_pos (p : ℕ) (rho : ℂ)).ne'
  field_simp [hg]
  norm_num [Complex.normSq_apply]
  ring

/-- One-prime joint quadrature Hermiticity. -/
def CCMRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho).im = 0 ∧
    (ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p rho).im = 0

theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_zero_iff_hermitian
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort p rho = 0 ↔
      CCMRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian p rho := by
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort,
    CCMRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg
      (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho).im,
      sq_nonneg
        (ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p rho).im]
  · rintro ⟨heven, hodd⟩
    rw [heven, hodd]
    norm_num

/-- One-prime phase-quadrature Hermiticity is singular Stokes flatness with no phase-node branch. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_zero_iff_flat
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort p rho = 0 ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment,
    ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv]
  have hz : bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (by exact_mod_cast p.2.ne_zero))
  constructor
  · intro hport
    have hnorm : ‖bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)‖ = 1 :=
      (reciprocalPhaseQuadraturePort_eq_zero_iff_norm_eq_one hz).1 hport
    have hre : (rho : ℂ).re = 1 / 2 :=
      (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le _).1 hnorm
    exact (ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).2
      ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2 hre)
  · intro hflat
    have hre : (rho : ℂ).re = 1 / 2 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1
        ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).1 hflat)
    apply (reciprocalPhaseQuadraturePort_eq_zero_iff_norm_eq_one hz).2
    exact (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le _).2 hre

theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian_iff_flat
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian p rho ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho :=
  (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_zero_iff_hermitian
    p rho).symm.trans
    (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_zero_iff_flat
      p rho)

/-- Exact remaining one-prime source-to-physical phase landing: both physical quadratures inherit
the corresponding source reality laws. -/
def CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho).im =
      (ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment p rho).im ∧
    (ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p rho).im =
      (ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment p rho).im

theorem ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_flat
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding p rho ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  rw [CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding,
    ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment_im_eq_zero,
    ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment_im_eq_zero]
  exact ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian_iff_flat p rho

/-- Phase-quadrature landing is exactly the existing fixed same-fibre completed-Xi norm law. -/
theorem ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_sameFiberNormIdentity
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding p rho ↔
      CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho :=
  (ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_flat p rho).trans
    ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).trans
      ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).trans
        (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_re_eq_half p rho).symm))

/-- Equivalent source-dagger form of the phase-quadrature landing. -/
theorem ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_sourceDaggerIdentity
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding p rho ↔
      CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho :=
  (ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_sameFiberNormIdentity
    p rho).trans
    (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_sourceDaggerIdentity p rho)

/-- Phase-quadrature landing is exactly annihilation of the explicit pre-divisor Cartier
comparison defect. -/
theorem ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_sourceCartierDefect_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding p rho ↔
      ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho = 0 :=
  (ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_flat p rho).trans
    ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).trans
      ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).trans
        (ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_re_eq_half
          p rho 0).symm))

/-- Homological form: one-prime joint quadrature landing is null-homology of the actual retained
cofinal central Bockstein class. -/
theorem ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_sourceNullHomologous
    (p : Nat.Primes) (rho : XiDivisorSupport) (m : ℕ) :
    CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding p rho ↔
      CCMMobiusThetaPhysicalDefectSourceNullHomologous (p : ℕ) rho p m :=
  (ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_sourceCartierDefect_eq_zero
    p rho).trans
    (ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_sourceNull
      p rho m)

theorem forall_ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_RH
    (p : Nat.Primes) :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding p rho) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff_RH]
  exact forall_congr'
    (ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_flat p)

end

end RHTower
