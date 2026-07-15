import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteArithmeticEndpoint
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetTopRow

/-!
# Cofinal selection at a finite arithmetic endpoint

The finite-arithmetic endpoint is computed from the first `M` square-index density atoms.  After
substitution, exact affine cancellation removes every base-depth pairing: the actual untruncated
current is the Hermitian current of the finite density-transform defect alone.  In particular this
defect is independent of both the Prouhet order `m` and the Haar depth `N`.

This permits the useful quantifier order.  First choose `M` from density convergence.  With that
same `M` fixed, the endpoint tends to zero as `N → ∞`, its affine denominator is eventually
nonzero, and the coefficient-weighted top row at exactly that endpoint tends to zero.  Hence one
cofinal `N` controls the endpoint, the actual untruncated current, and the complete weighted top
row while using the same polynomial and endpoint throughout.
-/

open Complex Real Polynomial MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The finite-density transform-pair error seen by the actual untruncated current. -/
def canonicalThetaTailFiniteArithmeticDensityDefectCurrent
    (M : ℕ) (z : ℂ) : ℝ :=
  symmetricHermitianCrossCurrentData
    (thetaCuspTailSecondDensityFiniteAtomPhaseValue M z -
      thetaCuspTailSecondDensityPhaseValue z)
    (thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z -
      thetaCuspTailSecondDensityPhaseDerivative z)
    (thetaHalfExponentialPhaseValue z)
    (thetaHalfExponentialPhaseDerivative z)

/-- Subtracting two base currents with the same returned pairings removes those pairings exactly. -/
theorem phaseAdaptedReturnedSourceBaseCurrent_sub_eq_densityDefect
    (V₀ D₀ R R' A A' E E' : ℂ) :
    phaseAdaptedReturnedSourceBaseCurrent V₀ D₀ R R' E E' -
        phaseAdaptedReturnedSourceBaseCurrent V₀ D₀ A A' E E' =
      symmetricHermitianCrossCurrentData (A - R) (A' - R') E E' := by
  unfold phaseAdaptedReturnedSourceBaseCurrent
    symmetricHermitianCrossCurrentData
  simp only [map_add, map_sub, map_neg]
  simp [Complex.mul_im]
  ring

/-- Exact uniformity in `N`: wherever the affine denominator is nonzero, endpoint substitution
turns the actual untruncated current into a function of `M` and `z` alone. -/
theorem canonicalThetaTailFiniteArithmeticUntruncatedCurrent_eq_densityDefect
    (m N M : ℕ) {z : ℂ}
    (hden : phaseAdaptedCriticalSelfConsistentDenominator m N
      (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) ≠ 0) :
    canonicalThetaTailFiniteArithmeticUntruncatedCurrent m N M z =
      canonicalThetaTailFiniteArithmeticDensityDefectCurrent M z := by
  rw [canonicalThetaTailFiniteArithmeticUntruncatedCurrent_eq_base_sub
    m N M hden]
  exact phaseAdaptedReturnedSourceBaseCurrent_sub_eq_densityDefect _ _ _ _ _ _ _ _

/-- The depth-independent finite density-transform defect vanishes as the atom cutoff grows. -/
theorem tendsto_canonicalThetaTailFiniteArithmeticDensityDefectCurrent
    {z : ℂ} (hz : 0 ≤ z.im) :
    Tendsto (fun M : ℕ =>
      canonicalThetaTailFiniteArithmeticDensityDefectCurrent M z)
      atTop (nhds 0) := by
  have hvalue :=
    (tendsto_thetaCuspTailSecondDensityFiniteAtomPhaseValue hz).sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => thetaCuspTailSecondDensityPhaseValue z) atTop
        (nhds (thetaCuspTailSecondDensityPhaseValue z)))
  have hderivative :=
    (tendsto_thetaCuspTailSecondDensityFiniteAtomPhaseDerivative hz).sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => thetaCuspTailSecondDensityPhaseDerivative z) atTop
        (nhds (thetaCuspTailSecondDensityPhaseDerivative z)))
  simpa only [canonicalThetaTailFiniteArithmeticDensityDefectCurrent,
    sub_self, symmetricHermitianCrossCurrentData, neg_zero, zero_mul, mul_zero,
    map_zero, add_zero, Complex.zero_im] using
      symmetricHermitianCrossCurrentData_tendsto
        (E := thetaHalfExponentialPhaseValue z)
        (E' := thetaHalfExponentialPhaseDerivative z)
        hvalue hderivative

/-- For a fixed finite atom cutoff, the corresponding arithmetic endpoint tends to zero cofinally
in the Haar depth. -/
theorem canonicalThetaTailFiniteArithmeticProuhetEndpoint_tendsto_zero
    (m M : ℕ) {z : ℂ} (hzLower : -(1 / 2 : ℝ) < z.im)
    (hzHalf : z.im < 1 / 2) :
    Tendsto (fun N : ℕ =>
      canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z)
      atTop (nhds 0) := by
  have hBq := phaseAdaptedProuhetBase_eval_dyadicDecay_ne_zero m hzHalf
  have hQ := thetaHalfExponentialPhaseCurrent_ne_zero hzLower
  simpa only [canonicalThetaTailFiniteArithmeticProuhetEndpoint] using
    phaseAdaptedCriticalSelfConsistentEndpoint_tendsto_zero
      m (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter hzHalf
      (thetaCuspTailSecondDensityFiniteAtomPhaseValue M z)
      (thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z)
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) hBq hQ

/-- The affine denominator needed by every finite-arithmetic endpoint is eventually nonzero. -/
theorem canonicalThetaTailFiniteArithmeticDenominator_eventually_ne_zero
    (m : ℕ) {z : ℂ} (hzLower : -(1 / 2 : ℝ) < z.im)
    (hzHalf : z.im < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      phaseAdaptedCriticalSelfConsistentDenominator m N
        (spectralTranslationPhase (Real.log 2) z)
        dyadicProuhetGrowthCharacter z
        (thetaHalfExponentialPhaseValue z)
        (thetaHalfExponentialPhaseDerivative z) ≠ 0 := by
  exact phaseAdaptedCriticalSelfConsistentDenominator_eventually_ne_zero
    m (spectralTranslationPhase (Real.log 2) z)
    dyadicProuhetGrowthCharacter hzHalf
    (thetaHalfExponentialPhaseValue z)
    (thetaHalfExponentialPhaseDerivative z)
    (thetaHalfExponentialPhaseCurrent_ne_zero hzLower)

/-- The complete coefficient-weighted top row formed from the same finite-arithmetic endpoint and
the same phase-adapted Prouhet polynomial as the untruncated current. -/
def canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent
    (d m N M : ℕ) (z : ℂ) : ℂ :=
  phaseAdaptedProuhetWeightedTopRowCurrent
    (canonicalPhaseAdaptedWeightedHaarPolynomial m z
      (canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z))
    dyadicProuhetDecayCharacter N d z

/-- For fixed `M`, the coefficient-weighted top row at its finite-arithmetic endpoint tends to
zero with the common depth `N`. -/
theorem tendsto_canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent
    (d m M : ℕ) {z : ℂ} (hzLower : -(1 / 2 : ℝ) < z.im)
    (hzHalf : z.im < 1 / 2) :
    Tendsto (fun N : ℕ =>
      canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent d m N M z)
      atTop (nhds 0) := by
  have htau := canonicalThetaTailFiniteArithmeticProuhetEndpoint_tendsto_zero
    m M hzLower hzHalf
  simpa only [canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent,
    canonicalPhaseAdaptedWeightedHaarPolynomial] using
      phaseAdaptedProuhetWeightedTopRowCurrent_tendsto_zero
        m (spectralTranslationPhase (Real.log 2) z)
        dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter
        (fun N : ℕ =>
          canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z)
        d z htau

/-- **Cofinal finite-arithmetic selection, with reversed useful order.**  For fixed `d,z,m`, first
choose a single finite atom cutoff `M`.  Every sufficiently large common depth `N` then has nonzero
affine denominator and simultaneously controls the endpoint, the actual untruncated current, and
the coefficient-weighted top row. -/
theorem exists_M_eventually_canonicalThetaTailFiniteArithmeticCofinalSelection
    (d m : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ M : ℕ, ∀ᶠ N : ℕ in atTop,
      phaseAdaptedCriticalSelfConsistentDenominator m N
          (spectralTranslationPhase (Real.log 2) z)
          dyadicProuhetGrowthCharacter z
          (thetaHalfExponentialPhaseValue z)
          (thetaHalfExponentialPhaseDerivative z) ≠ 0 ∧
        ‖canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z‖ < epsilon ∧
        ‖canonicalThetaTailFiniteArithmeticUntruncatedCurrent m N M z‖ < epsilon ∧
        ‖canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent d m N M z‖ < epsilon := by
  have hdefectNorm : Tendsto (fun M : ℕ =>
      ‖canonicalThetaTailFiniteArithmeticDensityDefectCurrent M z‖)
      atTop (nhds 0) := by
    simpa using
      (tendsto_canonicalThetaTailFiniteArithmeticDensityDefectCurrent hz0.le).norm
  have hMEventually : ∀ᶠ M : ℕ in atTop,
      ‖canonicalThetaTailFiniteArithmeticDensityDefectCurrent M z‖ < epsilon :=
    hdefectNorm.eventually (eventually_lt_nhds hepsilon)
  obtain ⟨M, hM⟩ := hMEventually.exists
  refine ⟨M, ?_⟩
  have hzLower : -(1 / 2 : ℝ) < z.im := by linarith
  have hden := canonicalThetaTailFiniteArithmeticDenominator_eventually_ne_zero
    m hzLower hzHalf
  have htauNorm : Tendsto (fun N : ℕ =>
      ‖canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z‖)
      atTop (nhds 0) := by
    simpa using
      (canonicalThetaTailFiniteArithmeticProuhetEndpoint_tendsto_zero
        m M hzLower hzHalf).norm
  have htau : ∀ᶠ N : ℕ in atTop,
      ‖canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z‖ < epsilon :=
    htauNorm.eventually (eventually_lt_nhds hepsilon)
  have htopNorm : Tendsto (fun N : ℕ =>
      ‖canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent d m N M z‖)
      atTop (nhds 0) := by
    simpa using
      (tendsto_canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent
        d m M hzLower hzHalf).norm
  have htop : ∀ᶠ N : ℕ in atTop,
      ‖canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent d m N M z‖ < epsilon :=
    htopNorm.eventually (eventually_lt_nhds hepsilon)
  filter_upwards [hden, htau, htop] with N hN hNtau hNtop
  refine ⟨hN, hNtau, ?_, hNtop⟩
  rw [canonicalThetaTailFiniteArithmeticUntruncatedCurrent_eq_densityDefect
    m N M hN]
  exact hM

/-- Pointwise joint selection of one finite atom cutoff and one common cofinal depth. -/
theorem exists_canonicalThetaTailFiniteArithmeticCofinalSelection
    (d m : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ M N : ℕ,
      phaseAdaptedCriticalSelfConsistentDenominator m N
          (spectralTranslationPhase (Real.log 2) z)
          dyadicProuhetGrowthCharacter z
          (thetaHalfExponentialPhaseValue z)
          (thetaHalfExponentialPhaseDerivative z) ≠ 0 ∧
        ‖canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z‖ < epsilon ∧
        ‖canonicalThetaTailFiniteArithmeticUntruncatedCurrent m N M z‖ < epsilon ∧
        ‖canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent d m N M z‖ < epsilon := by
  obtain ⟨M, hM⟩ :=
    exists_M_eventually_canonicalThetaTailFiniteArithmeticCofinalSelection
      d m hz0 hzHalf hepsilon
  obtain ⟨N, hN⟩ := hM.exists
  exact ⟨M, N, hN⟩

/-- Eventual anisotropic selection.  The top-row degree is exactly the scheduled odd Taylor degree,
and the endpoint, actual untruncated current, and weighted top row share the same selected `M,N` and
are all bounded by the scaled squared final Taylor value. -/
theorem eventually_exists_canonicalThetaTailFiniteArithmeticCofinalSelection_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) (hsigma0 : 0 < sigma.re) (hsigmaHalf : sigma.re < 1 / 2)
    (m : ℕ → ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∃ M N : ℕ,
      phaseAdaptedCriticalSelfConsistentDenominator (m n) N
          (spectralTranslationPhase (Real.log 2)
            (xiCTaylorAnisotropicCenteredPoint sigma n))
          dyadicProuhetGrowthCharacter
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (thetaHalfExponentialPhaseValue
            (xiCTaylorAnisotropicCenteredPoint sigma n))
          (thetaHalfExponentialPhaseDerivative
            (xiCTaylorAnisotropicCenteredPoint sigma n)) ≠ 0 ∧
        ‖canonicalThetaTailFiniteArithmeticProuhetEndpoint (m n) N M
            (xiCTaylorAnisotropicCenteredPoint sigma n)‖ <
          (epsilon * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              ((xiCTaylorPolynomial
                (xiCTaylorOddDegreeSchedule D
                  (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                    (xiCTaylorAnisotropicCenteredPoint sigma n)) ∧
        ‖canonicalThetaTailFiniteArithmeticUntruncatedCurrent (m n) N M
            (xiCTaylorAnisotropicCenteredPoint sigma n)‖ <
          (epsilon * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              ((xiCTaylorPolynomial
                (xiCTaylorOddDegreeSchedule D
                  (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                    (xiCTaylorAnisotropicCenteredPoint sigma n)) ∧
        ‖canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent
            (xiCTaylorOddDegreeSchedule D
              (xiCTaylorAnisotropicScheduleStage sigma n))
            (m n) N M (xiCTaylorAnisotropicCenteredPoint sigma n)‖ <
          (epsilon * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              ((xiCTaylorPolynomial
                (xiCTaylorOddDegreeSchedule D
                  (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                    (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  have hzero : Tendsto (fun n : ℕ =>
      (0 : ℝ) * (((n + 1 : ℕ) : ℝ) ^
        (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
    simpa only [zero_mul] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hpositive :=
    eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
      hD sigma (fun _ : ℕ => (0 : ℝ)) hzero hepsilon
  have himPos :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_pos sigma hsigmaHalf
  have himHalf :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_lt_half sigma hsigma0
  filter_upwards [hpositive, himPos, himHalf] with n hn hzn0 hznHalf
  exact exists_canonicalThetaTailFiniteArithmeticCofinalSelection
    (xiCTaylorOddDegreeSchedule D
      (xiCTaylorAnisotropicScheduleStage sigma n))
    (m n) hzn0 hznHalf hn

end

end RHTower
