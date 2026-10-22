import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEKGContinuumQNMOnlyCompletenessNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyDelayedPumpProbe
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMEBMGlobalSourceIncompatibility
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianArchimedeanContour
import GaloisForLFunctions.HTGeometry.CausalFourierBridge

/-!
# Completed-Eisenstein continuum phase exclusion for HB

The literal completed angular EKG density defines a finite-energy Birmingham--Mokhtari continuum
state. Its four horizontal Xi factors occur in reflected pairs, so the density is even. The
physical chiral projection kernel is also real and even. Consequently the imaginary part of the
reduced Fourier integrand is odd, and the exact damped continuum response is real at every delay.

At a critical Xi copy, the exact unit-seed cross-branch AIME numerator is nonreal: its angular
denominator has imaginary part one quarter of the nonzero Xi ordinate. Thus this actual
completed-Eisenstein continuum response can never supply the negative AIME counterterm forced by
the unit BM target. A surviving nonlinear source must carry genuinely complex phase-sensitive
incidence rather than remain in this real-even continuum sector.

`[NEW] [HB ROUTE KILL] [ACTUAL CONTINUUM] [ALL DELAYS] [LEAN-PROVED]`
-/

open Complex Real MeasureTheory

namespace RHTower

noncomputable section

/-- The literal completed-Eisenstein continuum density is even in physical energy. -/
theorem thetaCuspHawkingCompletedEisensteinContinuumDensity_neg
    (q : XiZeroCopy) (t r : ℝ) :
    thetaCuspHawkingCompletedEisensteinContinuumDensity q t (-r) =
      thetaCuspHawkingCompletedEisensteinContinuumDensity q t r := by
  rw [thetaCuspHawkingCompletedEisensteinContinuumDensity_eq_lineFactors,
    thetaCuspHawkingCompletedEisensteinContinuumDensity_eq_lineFactors]
  simp only [neg_neg]
  ring

/-- The four completed horizontal factors give a uniform pointwise bound on the literal density. -/
theorem exists_thetaCuspHawkingCompletedEisensteinContinuumDensity_bounded
    (q : XiZeroCopy) (t : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ,
      thetaCuspHawkingCompletedEisensteinContinuumDensity q t r ≤ B := by
  let a := thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q)
  let cPlus := thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) + t
  let cMinus := thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) - t
  have ha : |a| < 1 :=
    abs_thetaCuspHawkingCompletedEisensteinPhysicalHeight_lt_one q
  obtain ⟨BPlus, hBPlus, hbPlus⟩ :=
    exists_thetaCuspHawkingCompletedEisensteinLineNormSq_bounded ha cPlus
  obtain ⟨BMinus, hBMinus, hbMinus⟩ :=
    exists_thetaCuspHawkingCompletedEisensteinLineNormSq_bounded ha cMinus
  refine ⟨BPlus ^ (2 : ℕ) * BMinus ^ (2 : ℕ),
    mul_nonneg (sq_nonneg BPlus) (sq_nonneg BMinus), fun r => ?_⟩
  rw [thetaCuspHawkingCompletedEisensteinContinuumDensity_eq_lineFactors]
  calc
    _ ≤ BPlus * BPlus * BMinus * BMinus := by
      gcongr
      · exact sq_nonneg _
      · exact sq_nonneg _
      · exact sq_nonneg _
      · exact hbPlus r
      · exact hbPlus (-r)
      · exact hbMinus r
      · exact hbMinus (-r)
    _ = BPlus ^ (2 : ℕ) * BMinus ^ (2 : ℕ) := by ring

/-- Integrability and the four-factor bound admit the literal density to physical continuum
energy space. -/
theorem memLp_two_thetaCuspHawkingCompletedEisensteinContinuumDensity
    (q : XiZeroCopy) (t : ℝ) :
    MemLp (fun r : ℝ =>
      (thetaCuspHawkingCompletedEisensteinContinuumDensity q t r : ℂ)) 2 volume := by
  obtain ⟨B, -, hB⟩ :=
    exists_thetaCuspHawkingCompletedEisensteinContinuumDensity_bounded q t
  refine memLp_two_of_integrable_of_norm_le
    (integrable_thetaCuspHawkingCompletedEisensteinContinuumDensity q t).ofReal
    (C := B) ?_
  intro r
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (thetaCuspHawkingCompletedEisensteinContinuumDensity_nonneg q t r)]
  exact hB r

/-- Finite-energy BM state whose field is the actual completed-Eisenstein density. -/
def d4BMCompletedEisensteinContinuumState
    (q : XiZeroCopy) (t : ℝ) : D4BMFiniteEnergyContinuumState where
  field r := (thetaCuspHawkingCompletedEisensteinContinuumDensity q t r : ℂ)
  finiteEnergy := memLp_two_thetaCuspHawkingCompletedEisensteinContinuumDensity q t

/-- The physical BM chiral continuum kernel has no imaginary part. -/
lemma d4BMPhysicalContinuumChiralKernel_im (r : ℝ) :
    (d4BMPhysicalContinuumChiralKernel r).im = 0 := by
  unfold d4BMPhysicalContinuumChiralKernel
  rw [Complex.div_im]
  norm_num [Complex.normSq, Complex.mul_re, Complex.mul_im, pow_two]

/-- Actual completed-Eisenstein chiral source density remains even after physical projection. -/
theorem d4BMCompletedEisensteinContinuumSourceDensity_neg
    (q : XiZeroCopy) (t r : ℝ) :
    d4BMFiniteEnergyContinuumSourceDensity
        (d4BMCompletedEisensteinContinuumState q t) (-r) =
      d4BMFiniteEnergyContinuumSourceDensity
        (d4BMCompletedEisensteinContinuumState q t) r := by
  change (thetaCuspHawkingCompletedEisensteinContinuumDensity q t (-r) : ℂ) *
      d4BMPhysicalContinuumChiralKernel (-r) =
    (thetaCuspHawkingCompletedEisensteinContinuumDensity q t r : ℂ) *
      d4BMPhysicalContinuumChiralKernel r
  rw [thetaCuspHawkingCompletedEisensteinContinuumDensity_neg]
  unfold d4BMPhysicalContinuumChiralKernel
  simp only [neg_sq]

/-- Actual completed-Eisenstein chiral source density is real-valued. -/
theorem d4BMCompletedEisensteinContinuumSourceDensity_im
    (q : XiZeroCopy) (t r : ℝ) :
    (d4BMFiniteEnergyContinuumSourceDensity
      (d4BMCompletedEisensteinContinuumState q t) r).im = 0 := by
  change (((thetaCuspHawkingCompletedEisensteinContinuumDensity q t r : ℝ) : ℂ) *
    d4BMPhysicalContinuumChiralKernel r).im = 0
  rw [Complex.mul_im, d4BMPhysicalContinuumChiralKernel_im]
  simp

/-- The imaginary part of the actual reduced continuum Fourier integrand is odd. -/
lemma d4BMCompletedEisensteinContinuumReducedIntegrand_im_neg
    (q : XiZeroCopy) (t delay r : ℝ) :
    (d4BMFiniteEnergyContinuumSourceDensity
        (d4BMCompletedEisensteinContinuumState q t) (-r) *
      Complex.exp (-Complex.I * ((-r : ℝ) : ℂ) * delay)).im =
    -(d4BMFiniteEnergyContinuumSourceDensity
        (d4BMCompletedEisensteinContinuumState q t) r *
      Complex.exp (-Complex.I * (r : ℂ) * delay)).im := by
  rw [d4BMCompletedEisensteinContinuumSourceDensity_neg]
  have hsIm := d4BMCompletedEisensteinContinuumSourceDensity_im q t r
  simp [Complex.mul_im, Complex.exp_im, hsIm]

/-- At every physical delay, the exact completed-Eisenstein BM continuum response is real. -/
theorem d4BMCompletedEisensteinContinuumDelayedResponse_im
    (q : XiZeroCopy) (t delay : ℝ) :
    (d4BMFiniteEnergyContinuumDelayedResponse
      (d4BMCompletedEisensteinContinuumState q t) delay).im = 0 := by
  rw [d4BMFiniteEnergyContinuumDelayedResponse_eq_factorized]
  unfold d4BMFiniteEnergyContinuumFactoredResponse
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hInt := integrable_d4BMFiniteEnergyContinuumReducedIntegrand
    (d4BMCompletedEisensteinContinuumState q t) delay
  rw [← Complex.imCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hInt]
  change Real.exp (-(3 / 2 * delay)) *
      (∫ r : ℝ, (d4BMFiniteEnergyContinuumSourceDensity
        (d4BMCompletedEisensteinContinuumState q t) r *
        Complex.exp (-Complex.I * (r : ℂ) * delay)).im) = 0
  rw [RiemannGaussian.integral_odd_eq_zero]
  · ring
  · exact d4BMCompletedEisensteinContinuumReducedIntegrand_im_neg q t delay

/-- On a critical Xi copy, the AIME angular denominator inherits one quarter of the nonzero
Xi ordinate as its imaginary part. -/
theorem d4ThetaTeukolskyAngularQ_xi_add_two_im_of_re_eq_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    (d4ThetaTeukolskyAngularQ (xiSpectralPoint q) + 2).im =
      (q.1 : ℂ).im / 4 := by
  rw [d4ThetaTeukolskyAngularQ_eq_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  simp [Complex.add_im, Complex.mul_im, Complex.sub_im, hline]
  ring

/-- Exact imaginary coordinate of the unit AIME numerator on the critical line. -/
theorem d4FundamentalQNMCrossBranchAIMENumerator_one_im_of_re_eq_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    (d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q)).im =
      3 * (q.1 : ℂ).im /
        Complex.normSq (d4ThetaTeukolskyAngularQ (xiSpectralPoint q) + 2) := by
  rw [d4FundamentalQNMCrossBranchAIMENumerator,
    d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq]
  norm_num only [Complex.normSq_one, one_mul]
  rw [show ((1 : ℝ) : ℂ) = 1 by norm_num, one_mul]
  rw [Complex.div_im,
    d4ThetaTeukolskyAngularQ_xi_add_two_im_of_re_eq_half q hline]
  norm_num
  ring

/-- The unit cross-branch AIME numerator is nonreal at every critical Xi copy. -/
theorem d4FundamentalQNMCrossBranchAIMENumerator_one_im_ne_zero_of_re_eq_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    (d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q)).im ≠ 0 := by
  rw [d4FundamentalQNMCrossBranchAIMENumerator_one_im_of_re_eq_half q hline]
  apply div_ne_zero
  · apply mul_ne_zero
    · norm_num
    · intro him
      have hheight := xiZeroCopy_one_lt_im_sq q
      rw [him] at hheight
      norm_num at hheight
  · intro hnorm
    exact d4ThetaTeukolskyAngularQ_xi_add_two_ne_zero q
      (Complex.normSq_eq_zero.mp hnorm)

/-- The actual completed-Eisenstein continuum response cannot equal the critical-line AIME
counterterm at any physical delay. -/
theorem d4BMCompletedEisensteinContinuumDelayedResponse_ne_forcedCounterterm
    (q : XiZeroCopy) (t delay : ℝ) (hline : (q.1 : ℂ).re = 1 / 2) :
    d4BMFiniteEnergyContinuumDelayedResponse
        (d4BMCompletedEisensteinContinuumState q t) delay ≠
      -d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) := by
  intro h
  have him := congrArg Complex.im h
  rw [d4BMCompletedEisensteinContinuumDelayedResponse_im,
    Complex.neg_im] at him
  exact d4FundamentalQNMCrossBranchAIMENumerator_one_im_ne_zero_of_re_eq_half q hline
    (by linarith)

/-- **Closed route kill.** On every critical Xi fibre, at every external energy and delay, using
the literal completed-Eisenstein physical continuum response as the same-pole remainder fails the
exact unit BM boundary incidence demanded by the full cross-branch projected residue. -/
theorem d4HBCompletedEisensteinContinuumCountertermRouteKilled :
    ∀ (n : ℕ) (q : XiZeroCopy) (t delay : ℝ),
      (q.1 : ℂ).re = 1 / 2 →
      d4FullCrossBranchProjectedResidue 1
          (fun _ => d4BMFiniteEnergyContinuumDelayedResponse
            (d4BMCompletedEisensteinContinuumState q t) delay)
          (xiSpectralPoint q) ≠
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  intro n q t delay hline hmatch
  have hforced :=
    (d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_forcedCounterterm_of_criticalLine
      n 1
      (fun _ => d4BMFiniteEnergyContinuumDelayedResponse
        (d4BMCompletedEisensteinContinuumState q t) delay)
      q hline).mp hmatch
  exact d4BMCompletedEisensteinContinuumDelayedResponse_ne_forcedCounterterm
    q t delay hline hforced

end

end RHTower
