import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompletedBalancedSpinTwoFirstLiveJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingSchwarzOddDiagonalCausalPropagatorObstruction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompletedEisensteinContinuumPhaseNoGo
import GaloisForLFunctions.RHTower.XiWeilHardyCriticalLocusPoissonReserve
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# First-live completed balanced spin-two causal-diagonal no-go

The multiplicity-matched completed balanced spin-two angular jet is Schwarz-real on every
critical Xi fibre.  Its external-square jet has phase `(-i)^(2m)`, its Bochner coefficient is
real, and its two shifted completed-Xi factors form a conjugate pair.  Exact unit HB incidence,
however, forces the radial scale times this nonzero real jet to equal the negative unit AIME
numerator, whose imaginary part is nonzero on every critical Xi copy.

Channel-Schwarz oddness forces every copy-diagonal Peierls weight to be real.  Hardy's theorem
supplies an unconditional critical Xi copy, so no such global causal diagonal weight can realize
the actual first-live HB incidence.  A surviving HB producer must therefore use genuinely
non-diagonal fibre/channel response.

`[NEW] [HB ROUTE KILL] [FIRST-LIVE JET] [CAUSAL SCHWARZ] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

private theorem neg_I_pow_mul_real_square_im_eq_zero (m : ℕ) (a : ℝ) :
    (((-Complex.I) ^ m * (a : ℂ)) * ((-Complex.I) ^ m * (a : ℂ))).im = 0 := by
  have hp : (-Complex.I) ^ m * (-Complex.I) ^ m = (-1 : ℂ) ^ m := by
    rw [← mul_pow]
    congr 1
    rw [neg_mul_neg, Complex.I_mul_I]
  have heq : ((-Complex.I) ^ m * (a : ℂ)) * ((-Complex.I) ^ m * (a : ℂ)) =
      ((((-1 : ℝ) ^ m) * a ^ 2 : ℝ) : ℂ) := by
    calc
      _ = ((-1 : ℂ) ^ m) * ((a ^ 2 : ℝ) : ℂ) := by
        rw [← hp]
        push_cast
        ring
      _ = ((((-1 : ℝ) ^ m) * a ^ 2 : ℝ) : ℂ) := by
        push_cast
        rfl
  rw [heq]
  exact ofReal_im _

/-- The exact order-`2m` projecting external-square jet is real on a critical Xi fibre. -/
theorem iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_im_eq_zero_of_criticalLine
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    (iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
        d4BMCompletedEisensteinProjectingExternalSquare
        (d4BMXiProjectingEisensteinCenteredParameter q)).im = 0 := by
  have hzIm : (xiSpectralPoint q).im = 0 := by
    simp [xiSpectralPoint, Complex.mul_im, hline]
  have hz : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hzIm
  rw [iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_at_twiceMultiplicity]
  rw [iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi]
  rw [hz, iteratedDeriv_XiC_ofReal]
  have him := neg_I_pow_mul_real_square_im_eq_zero
    (d4BMXiProjectingLegMultiplicity q)
    (iteratedDeriv (d4BMXiProjectingLegMultiplicity q) Xi (xiSpectralPoint q).re)
  have hchooseIm :
      ((Nat.choose (2 * d4BMXiProjectingLegMultiplicity q)
        (d4BMXiProjectingLegMultiplicity q) : ℂ)).im = 0 := by simp
  rw [show
      (Nat.choose (2 * d4BMXiProjectingLegMultiplicity q)
          (d4BMXiProjectingLegMultiplicity q) : ℂ) *
          ((-Complex.I) ^ d4BMXiProjectingLegMultiplicity q *
            ((iteratedDeriv (d4BMXiProjectingLegMultiplicity q) Xi
              (xiSpectralPoint q).re : ℝ) : ℂ)) *
          ((-Complex.I) ^ d4BMXiProjectingLegMultiplicity q *
            ((iteratedDeriv (d4BMXiProjectingLegMultiplicity q) Xi
              (xiSpectralPoint q).re : ℝ) : ℂ)) =
        (Nat.choose (2 * d4BMXiProjectingLegMultiplicity q)
          (d4BMXiProjectingLegMultiplicity q) : ℂ) *
          (((-Complex.I) ^ d4BMXiProjectingLegMultiplicity q *
            ((iteratedDeriv (d4BMXiProjectingLegMultiplicity q) Xi
              (xiSpectralPoint q).re : ℝ) : ℂ)) *
          ((-Complex.I) ^ d4BMXiProjectingLegMultiplicity q *
            ((iteratedDeriv (d4BMXiProjectingLegMultiplicity q) Xi
              (xiSpectralPoint q).re : ℝ) : ℂ))) by ring]
  rw [Complex.mul_im]
  rw [hchooseIm, him]
  ring

/-- The actual repeated-leg Bochner/shifted-Xi side factor is real on a critical Xi fibre. -/
theorem d4BMCompletedBalancedSpinTwoProjectingSideFactor_actualRepeated_im_eq_zero_of_criticalLine
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    (d4BMCompletedBalancedSpinTwoProjectingSideFactor
      d4BMActualRepeatedEisensteinCenteredParameter
      (d4BMXiProjectingEisensteinCenteredParameter q)).im = 0 := by
  have hzIm : (xiSpectralPoint q).im = 0 := by
    simp [xiSpectralPoint, Complex.mul_im, hline]
  have hz : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hzIm
  have hpair :
      XiC (-xiSpectralPoint q - 3 * Complex.I) =
        (starRingEnd ℂ) (XiC (xiSpectralPoint q - 3 * Complex.I)) := by
    rw [show -xiSpectralPoint q - 3 * Complex.I =
        -(xiSpectralPoint q + 3 * Complex.I) by ring, XiC_even]
    rw [← XiC_conj]
    congr 1
    apply Complex.ext
    · simp
    · simp [hzIm]
  unfold d4BMCompletedBalancedSpinTwoProjectingSideFactor
    d4BMXiProjectingEisensteinCenteredParameter
  rw [thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_actualRepeated_projecting_factorization]
  unfold thetaCuspHawkingCompletedEisensteinXiFactor
    d4BMActualRepeatedEisensteinCenteredParameter
  rw [show -Complex.I * (2 * (3 / 2 : ℂ) + Complex.I * xiSpectralPoint q) =
      xiSpectralPoint q - 3 * Complex.I by
    calc
      -Complex.I * (2 * (3 / 2 : ℂ) + Complex.I * xiSpectralPoint q) =
          -3 * Complex.I - (Complex.I * Complex.I) * xiSpectralPoint q := by ring
      _ = xiSpectralPoint q - 3 * Complex.I := by rw [Complex.I_mul_I]; ring]
  rw [show -Complex.I * (2 * (3 / 2 : ℂ) - Complex.I * xiSpectralPoint q) =
      -xiSpectralPoint q - 3 * Complex.I by
    calc
      -Complex.I * (2 * (3 / 2 : ℂ) - Complex.I * xiSpectralPoint q) =
          -3 * Complex.I + (Complex.I * Complex.I) * xiSpectralPoint q := by ring
      _ = -xiSpectralPoint q - 3 * Complex.I := by rw [Complex.I_mul_I]; ring]
  rw [hpair]
  have hcoeffIm :
      (((4 * xiSpectralPoint q ^ 2 + 1) *
        (4 * xiSpectralPoint q ^ 2 + 25)) / 32).im = 0 := by
    rw [hz]
    have hsqIm : ((((xiSpectralPoint q).re : ℂ) ^ 2)).im = 0 := by
      rw [pow_two, Complex.mul_im]
      simp
    simp
    rw [hsqIm]
    ring
  have hpairIm :
      (XiC (xiSpectralPoint q - 3 * Complex.I) *
        (starRingEnd ℂ) (XiC (xiSpectralPoint q - 3 * Complex.I))).im = 0 := by
    simp [Complex.mul_im]
    ring
  rw [show
      ((4 * xiSpectralPoint q ^ 2 + 1) *
          (4 * xiSpectralPoint q ^ 2 + 25)) / 32 *
          XiC (xiSpectralPoint q - 3 * Complex.I) *
          (starRingEnd ℂ) (XiC (xiSpectralPoint q - 3 * Complex.I)) =
        (((4 * xiSpectralPoint q ^ 2 + 1) *
          (4 * xiSpectralPoint q ^ 2 + 25)) / 32) *
          (XiC (xiSpectralPoint q - 3 * Complex.I) *
          (starRingEnd ℂ) (XiC (xiSpectralPoint q - 3 * Complex.I))) by ring]
  rw [Complex.mul_im, hcoeffIm, hpairIm]
  ring

/-- The complete first live multiplicity-matched angular jet is real on every critical fibre. -/
theorem d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet_im_eq_zero_of_criticalLine
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    (d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet q).im = 0 := by
  unfold d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet
  rw [iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_at_twiceMultiplicity]
  rw [Complex.mul_im,
    iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_im_eq_zero_of_criticalLine
      q hline,
    d4BMCompletedBalancedSpinTwoProjectingSideFactor_actualRepeated_im_eq_zero_of_criticalLine
      q hline]
  ring

/-- Exact first-live HB incidence forces a genuinely nonreal radial scale on every critical
Xi fibre. -/
theorem d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoRequiredRadialScale_im_ne_zero_of_criticalLine
    (n : ℕ) (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    (d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoRequiredRadialScale
      n 1 q).im ≠ 0 := by
  intro hscaleIm
  let scale :=
    d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoRequiredRadialScale n 1 q
  let radialScale : ℂ → ℂ := fun _ => scale
  have hincidence :
      d4FullCrossBranchProjectedResidue 1
          (d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder
            q radialScale)
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
    apply (d4FullCrossBranchProjectedResidue_actualMultiplicityMatched_eq_unitBMTarget_iff_radialScale
      n 1 radialScale q).2
    rfl
  have hforced :=
    (d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_forcedCounterterm_of_criticalLine
      n 1
      (d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder
        q radialScale)
      q hline).1 hincidence
  rw [d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq]
    at hforced
  have hproductIm :
      (radialScale (xiSpectralPoint q) *
        d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet q).im = 0 := by
    rw [Complex.mul_im,
      d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet_im_eq_zero_of_criticalLine
        q hline]
    simp [radialScale, scale, hscaleIm]
  have him := congrArg Complex.im hforced
  rw [hproductIm, Complex.neg_im] at him
  apply d4FundamentalQNMCrossBranchAIMENumerator_one_im_ne_zero_of_re_eq_half q hline
  linarith

/-- Closed route class: copy-diagonal causal Peierls weights cannot realize the actual
multiplicity-matched first-live completed balanced spin-two HB incidence on every Xi copy. -/
def D4HBActualMultiplicityMatchedCompletedBalancedSpinTwoCopyDiagonalCausalRouteKilled : Prop :=
  ∀ n : ℕ,
    ¬ ∃ w : XiZeroCopy → ℂ,
      HBXiPeierlsWeightedPropagatorChannelSchwarzOdd w ∧
        ∀ q : XiZeroCopy,
          d4FullCrossBranchProjectedResidue 1
              (d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder
                q (fun _ => w q))
              (xiSpectralPoint q) =
            d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q

/-- Premise-free Lean certificate killing the complete copy-diagonal causal radial/left-QNM
realization of the actual first-live completed balanced spin-two HB route. -/
theorem d4HBActualMultiplicityMatchedCompletedBalancedSpinTwoCopyDiagonalCausalRouteKilled :
    D4HBActualMultiplicityMatchedCompletedBalancedSpinTwoCopyDiagonalCausalRouteKilled := by
  intro n
  rintro ⟨w, hodd, hincidence⟩
  let qCritical : XiCriticalLineResolventCopy :=
    Classical.choice nonempty_xiCriticalLineResolventCopy_of_hardy
  let q : XiZeroCopy := qCritical.1
  have hline : (q.1 : ℂ).re = 1 / 2 := qCritical.2
  have hwStar : (starRingEnd ℂ) (w q) = w q :=
    (hbXiPeierlsWeightedPropagatorChannelSchwarzOdd_iff w).1 hodd q
  have hwIm : (w q).im = 0 := by
    have him := congrArg Complex.im hwStar
    rw [Complex.conj_im] at him
    linarith
  have hforced :=
    (d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_forcedCounterterm_of_criticalLine
      n 1
      (d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder
        q (fun _ => w q))
      q hline).1 (hincidence q)
  rw [d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq]
    at hforced
  have hproductIm :
      (w q * d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet q).im = 0 := by
    rw [Complex.mul_im, hwIm,
      d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet_im_eq_zero_of_criticalLine
        q hline]
    ring
  have him := congrArg Complex.im hforced
  rw [hproductIm, Complex.neg_im] at him
  exact d4FundamentalQNMCrossBranchAIMENumerator_one_im_ne_zero_of_re_eq_half q hline
    (by linarith)

end

end RHTower
