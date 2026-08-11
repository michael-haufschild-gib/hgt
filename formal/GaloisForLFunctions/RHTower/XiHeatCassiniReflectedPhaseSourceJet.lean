import GaloisForLFunctions.RHTower.XiHeatCassiniPhaseClockLanding
import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapReflectedPhaseHermiticity

/-!
# Reflected source jet behind the Xi heat--Cassini phase clock

Horizontal half-grade and vertical phase are independent before divisor specialization.  On the
continuous log-prime scale, reflection-minus-identity couples them in the imaginary source
boundary

`2 sinh(a x / 2) sin(γ x)`.

Its first nonzero neutral-scale jet is the mixed second jet `2 a γ`.  At a Xi divisor copy this is
exactly `-2` times the imaginary part of the squared centered node.  Thus the Cassini phase clock
is not missing from the arithmetic source: it is the mixed grade--phase source jet which is erased
when either coordinate is completed separately to an even energy.
-/

open Complex

namespace RHTower

noncomputable section

/-- Unitary height phase before specialization to a discrete prime clock. -/
def xiReflectedPhaseLogScaleCharacter (γ x : ℝ) : ℂ :=
  Complex.exp (-(((γ * x : ℝ) : ℂ) * I))

/-- Continuous log-prime interpolation of the independent phase/half-grade source. -/
def xiReflectedPhaseLogScaleHalfGradeSource
    (x : ℝ) (u : ℂ) (a : ℝ) : ℂ :=
  ((Real.exp (a * x / 2) : ℝ) : ℂ) * u

/-- Reflection-minus-identity boundary before grade and phase are specialized to a divisor. -/
def xiReflectedPhaseLogScaleBoundary
    (a γ x : ℝ) : ℂ :=
  xiReflectedPhaseLogScaleHalfGradeSource x
      (xiReflectedPhaseLogScaleCharacter γ x) (-a) -
    xiReflectedPhaseLogScaleHalfGradeSource x
      (xiReflectedPhaseLogScaleCharacter γ x) a

/-- Real normal form of the reflected source boundary's phase channel. -/
def xiReflectedPhaseLogScaleImag (a γ x : ℝ) : ℝ :=
  2 * Real.sinh (a * x / 2) * Real.sin (γ * x)

/-- First log-scale jet of the reflected source phase channel. -/
def xiReflectedPhaseLogScaleFirstJet (a γ x : ℝ) : ℝ :=
  a * Real.cosh (a * x / 2) * Real.sin (γ * x) +
    2 * γ * Real.sinh (a * x / 2) * Real.cos (γ * x)

/-- Second log-scale jet.  Its neutral value retains only the mixed grade--phase tensor. -/
def xiReflectedPhaseLogScaleSecondJet (a γ x : ℝ) : ℝ :=
  (a ^ 2 / 2 - 2 * γ ^ 2) * Real.sinh (a * x / 2) * Real.sin (γ * x) +
    2 * a * γ * Real.cosh (a * x / 2) * Real.cos (γ * x)

/-- The real normal form is exactly the imaginary source boundary, before prime specialization. -/
theorem xiReflectedPhaseLogScaleBoundary_im
    (a γ x : ℝ) :
    (xiReflectedPhaseLogScaleBoundary a γ x).im =
      xiReflectedPhaseLogScaleImag a γ x := by
  rw [xiReflectedPhaseLogScaleBoundary,
    xiReflectedPhaseLogScaleHalfGradeSource,
    xiReflectedPhaseLogScaleHalfGradeSource,
    xiReflectedPhaseLogScaleCharacter]
  rw [show -(((γ * x : ℝ) : ℂ) * I) = (((-(γ * x) : ℝ) : ℂ) * I) by
    simp]
  rw [Complex.exp_mul_I]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.I_re, Complex.I_im,
    zero_mul, add_zero, mul_one, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  rw [xiReflectedPhaseLogScaleImag, Real.sinh_eq]
  simp only [Real.sin_neg]
  ring_nf

/-- Continuous half-grade source specializes exactly to the existing prime source. -/
theorem xiReflectedPhaseLogScaleHalfGradeSource_log_prime
    (p : Nat.Primes) (u : ℂ) (a : ℝ) :
    xiReflectedPhaseLogScaleHalfGradeSource (Real.log (p : ℝ)) u a =
      ccmRationalAdelicPrimePhaseTwistedHalfGradeSource p u a := by
  rw [xiReflectedPhaseLogScaleHalfGradeSource,
    ccmRationalAdelicPrimePhaseTwistedHalfGradeSource,
    Real.rpow_def_of_pos (by exact_mod_cast p.2.pos)]
  congr 1
  ring_nf

/-- Continuous height character specializes exactly to the existing source-height prime phase. -/
theorem xiReflectedPhaseLogScaleCharacter_log_prime
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    xiReflectedPhaseLogScaleCharacter (rho : ℂ).im (Real.log (p : ℝ)) =
      ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho := by
  have hphase := bilateralJetFamily_zpow_on_line
    (by exact_mod_cast p.2.pos) (rho : ℂ).im (1 : ℤ)
  simp only [one_mul, Int.cast_one, zpow_one] at hphase
  simpa [xiReflectedPhaseLogScaleCharacter,
    ccmRationalAdelicPrimeXiSourcePhaseCharacter,
    ccmRationalAdelicPrimeXiSourcePhasePoint] using hphase.symm

/-- Existing reflected physical phase moment is the discrete prime trace of the continuous source
boundary. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_im_eq_logScaleBoundary
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho).im =
      (xiReflectedPhaseLogScaleBoundary
        (primeDepthBVWoldXiCenteredRate rho) (rho : ℂ).im
        (Real.log (p : ℝ))).im := by
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_im_eq_sourceBoundary]
  rw [xiReflectedPhaseLogScaleBoundary,
    xiReflectedPhaseLogScaleCharacter_log_prime,
    xiReflectedPhaseLogScaleHalfGradeSource_log_prime,
    xiReflectedPhaseLogScaleHalfGradeSource_log_prime]
  rfl

/-- Existing physical phase moment therefore samples the exact hyperbolic--trigonometric source
jet. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_im_eq_logScaleImag
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho).im =
      xiReflectedPhaseLogScaleImag
        (primeDepthBVWoldXiCenteredRate rho) (rho : ℂ).im
        (Real.log (p : ℝ)) := by
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_im_eq_logScaleBoundary,
    xiReflectedPhaseLogScaleBoundary_im]

/-- First exact log-scale derivative of the reflected source phase channel. -/
theorem hasDerivAt_xiReflectedPhaseLogScaleImag
    (a γ x : ℝ) :
    HasDerivAt (xiReflectedPhaseLogScaleImag a γ)
      (xiReflectedPhaseLogScaleFirstJet a γ x) x := by
  have hsinh :=
    (Real.hasDerivAt_sinh (a * x / 2)).comp x
      (((hasDerivAt_id x).const_mul a).div_const 2)
  have hsin :=
    (Real.hasDerivAt_sin (γ * x)).comp x
      ((hasDerivAt_id x).const_mul γ)
  simpa only [xiReflectedPhaseLogScaleImag, Function.comp_apply, id_eq] using!
    ((hsinh.const_mul 2).mul hsin).congr_deriv (by
      dsimp only [xiReflectedPhaseLogScaleFirstJet]
      simp only [Function.comp_apply, id_eq]
      ring)

/-- Second exact log-scale derivative of the reflected source phase channel. -/
theorem hasDerivAt_xiReflectedPhaseLogScaleFirstJet
    (a γ x : ℝ) :
    HasDerivAt (xiReflectedPhaseLogScaleFirstJet a γ)
      (xiReflectedPhaseLogScaleSecondJet a γ x) x := by
  have hsinh :=
    (Real.hasDerivAt_sinh (a * x / 2)).comp x
      (((hasDerivAt_id x).const_mul a).div_const 2)
  have hcosh :=
    (Real.hasDerivAt_cosh (a * x / 2)).comp x
      (((hasDerivAt_id x).const_mul a).div_const 2)
  have hsin :=
    (Real.hasDerivAt_sin (γ * x)).comp x
      ((hasDerivAt_id x).const_mul γ)
  have hcos :=
    (Real.hasDerivAt_cos (γ * x)).comp x
      ((hasDerivAt_id x).const_mul γ)
  simpa only [xiReflectedPhaseLogScaleFirstJet, Function.comp_apply, id_eq] using!
    ((((hcosh.const_mul a).mul hsin).add
      ((hsinh.const_mul (2 * γ)).mul hcos))).congr_deriv (by
        dsimp only [xiReflectedPhaseLogScaleSecondJet]
        simp only [Function.comp_apply, id_eq]
        ring)

/-- The first neutral-scale jet vanishes: grade and phase can only be seen jointly at second
order. -/
theorem xiReflectedPhaseLogScaleFirstJet_zero (a γ : ℝ) :
    xiReflectedPhaseLogScaleFirstJet a γ 0 = 0 := by
  simp [xiReflectedPhaseLogScaleFirstJet]

/-- **Mixed neutral-source jet law.**  The first nonzero source jet is exactly `2 a γ`. -/
theorem xiReflectedPhaseLogScaleSecondJet_zero (a γ : ℝ) :
    xiReflectedPhaseLogScaleSecondJet a γ 0 = 2 * a * γ := by
  simp [xiReflectedPhaseLogScaleSecondJet]

/-- The phase channel carries the nontrivial sign character under either independent involution. -/
theorem xiReflectedPhaseLogScaleImag_neg_grade (a γ x : ℝ) :
    xiReflectedPhaseLogScaleImag (-a) γ x =
      -xiReflectedPhaseLogScaleImag a γ x := by
  unfold xiReflectedPhaseLogScaleImag
  rw [show -a * x / 2 = -(a * x / 2) by ring, Real.sinh_neg]
  ring

theorem xiReflectedPhaseLogScaleImag_neg_phase (a γ x : ℝ) :
    xiReflectedPhaseLogScaleImag a (-γ) x =
      -xiReflectedPhaseLogScaleImag a γ x := by
  unfold xiReflectedPhaseLogScaleImag
  rw [show -γ * x = -(γ * x) by ring, Real.sin_neg]
  ring

/-- Negating grade and phase together returns to the same Klein-four orbit character. -/
theorem xiReflectedPhaseLogScaleImag_neg_grade_neg_phase (a γ x : ℝ) :
    xiReflectedPhaseLogScaleImag (-a) (-γ) x =
      xiReflectedPhaseLogScaleImag a γ x := by
  rw [xiReflectedPhaseLogScaleImag_neg_grade,
    xiReflectedPhaseLogScaleImag_neg_phase]
  ring

/-- Neutral mixed source jet attached to one divisor copy. -/
def xiReflectedPhaseNeutralMixedJet (q : XiZeroCopy) : ℝ :=
  xiReflectedPhaseLogScaleSecondJet
    (primeDepthBVWoldXiCenteredRate q.1) (q.1 : ℂ).im 0

/-- The mixed source jet is exactly the phase-linear squared-node coordinate. -/
theorem xiReflectedPhaseNeutralMixedJet_eq_neg_two_mul_squaredNode_im
    (q : XiZeroCopy) :
    xiReflectedPhaseNeutralMixedJet q = -2 * (xiSquaredNode q).im := by
  rw [xiReflectedPhaseNeutralMixedJet,
    xiReflectedPhaseLogScaleSecondJet_zero,
    xiSquaredNode_im_eq_neg_centeredWoldRate_mul_height]
  ring

/-- The phase clock frequency is minus one half of the pre-divisor mixed source jet. -/
theorem xiSquaredNode_im_eq_neg_half_mul_reflectedPhaseNeutralMixedJet
    (q : XiZeroCopy) :
    (xiSquaredNode q).im = -(1 / 2 : ℝ) * xiReflectedPhaseNeutralMixedJet q := by
  rw [xiReflectedPhaseNeutralMixedJet_eq_neg_two_mul_squaredNode_im]
  ring

/-- Atomwise Cassini decoherence is driven exactly by the mixed pre-divisor source jet. -/
theorem xiHeatCassiniPhaseClockAtom_eq_reflectedPhaseNeutralMixedJet
    (y u : ℝ) (q : XiZeroCopy) :
    xiHeatCassiniPhaseClockAtom y u q =
      Real.exp (-((y + (xiSquaredNode q).re) * u)) *
        (1 - Real.cos ((xiReflectedPhaseNeutralMixedJet q / 2) * u)) := by
  rw [xiHeatCassiniPhaseClockAtom,
    xiSquaredNode_im_eq_neg_half_mul_reflectedPhaseNeutralMixedJet]
  rw [show (-(1 / 2 : ℝ) * xiReflectedPhaseNeutralMixedJet q) * u =
      -((xiReflectedPhaseNeutralMixedJet q / 2) * u) by ring,
    Real.cos_neg]

end

end RHTower
