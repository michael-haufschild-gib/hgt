import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetIntegratedHaarCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticPairCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticPhaseSeam

/-!
# Finite arithmetic endpoint for the phase-adapted Haar current

The self-consistent phase-adapted endpoint cancels the untruncated theta-tail/seam current, but its
definition uses the full positive-half-line density transform.  This module replaces those two
transform values by the first `M` exact square-index density atoms.

The replacement is noncircular.  The affine endpoint denominator is independent of the density
value and derivative.  Consequently the current at the finite arithmetic endpoint is exactly the
difference of two affine base currents.  The finite positive atom source converges in `L¹`, with
the derivative dominated by the first density moment, so this difference tends to zero.
-/

open Complex Real Polynomial MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The first `M` exact square-index atoms of the differentiated theta-tail density. -/
def thetaCuspTailSecondDensityFiniteAtomSource (M : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range M, thetaCuspTailSecondDensityAtom (n + 1) x

theorem thetaCuspTailSecondDensityFiniteAtomSource_nonneg
    (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspTailSecondDensityFiniteAtomSource M x := by
  unfold thetaCuspTailSecondDensityFiniteAtomSource
  exact Finset.sum_nonneg fun n _hn =>
    (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos n) hx).le

theorem thetaCuspTailSecondDensityFiniteAtomSource_le
    (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspTailSecondDensityFiniteAtomSource M x ≤
      thetaCuspTailSecondDensity x := by
  have hs : Summable
      (fun n : ℕ => thetaCuspTailSecondDensityAtom (n + 1) x) := by
    unfold thetaCuspTailSecondDensityAtom
    simpa only using (summable_thetaCuspTailDerivative 2 x).mul_left 4
  calc
    thetaCuspTailSecondDensityFiniteAtomSource M x ≤
        ∑' n : ℕ, thetaCuspTailSecondDensityAtom (n + 1) x := by
      unfold thetaCuspTailSecondDensityFiniteAtomSource
      exact hs.sum_le_tsum (Finset.range M) fun n _hn =>
        (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos n) hx).le
    _ = thetaCuspTailSecondDensity x :=
      (thetaCuspTailSecondDensity_eq_tsum_atom x).symm

theorem tendsto_thetaCuspTailSecondDensityFiniteAtomSource
    (x : ℝ) :
    Tendsto (fun M : ℕ => thetaCuspTailSecondDensityFiniteAtomSource M x)
      atTop (nhds (thetaCuspTailSecondDensity x)) := by
  have hs : Summable
      (fun n : ℕ => thetaCuspTailSecondDensityAtom (n + 1) x) := by
    unfold thetaCuspTailSecondDensityAtom
    simpa only using (summable_thetaCuspTailDerivative 2 x).mul_left 4
  have h := hs.hasSum.tendsto_sum_nat
  rw [← thetaCuspTailSecondDensity_eq_tsum_atom x] at h
  simpa only [thetaCuspTailSecondDensityFiniteAtomSource] using h

/-- Finite arithmetic approximation to the positive-half-line canonical density transform. -/
def thetaCuspTailSecondDensityFiniteAtomPhaseValue
    (M : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensityFiniteAtomSource M x : ℂ) *
      spectralTranslationPhase x z

/-- Derivative companion of the finite arithmetic density transform. -/
def thetaCuspTailSecondDensityFiniteAtomPhaseDerivative
    (M : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensityFiniteAtomSource M x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase x z)

theorem tendsto_thetaCuspTailSecondDensityFiniteAtomPhaseValue
    {z : ℂ} (hz : 0 ≤ z.im) :
    Tendsto (fun M : ℕ => thetaCuspTailSecondDensityFiniteAtomPhaseValue M z)
      atTop (nhds (thetaCuspTailSecondDensityPhaseValue z)) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℂ := fun M x =>
    (thetaCuspTailSecondDensityFiniteAtomSource M x : ℂ) *
      spectralTranslationPhase x z
  let bound : ℝ → ℝ := fun x => thetaCuspTailSecondDensity x
  have hboundInt : Integrable bound mu := by
    have h := integrableOn_pow_mul_thetaCuspTailSecondDensity 0
    simp only [pow_zero, one_mul] at h
    exact h
  have hFmeas : ∀ᶠ M : ℕ in atTop, AEStronglyMeasurable (F M) mu := by
    filter_upwards with M
    exact ((by
      dsimp only [F, thetaCuspTailSecondDensityFiniteAtomSource]
      unfold thetaCuspTailSecondDensityAtom thetaCuspPolynomialAtom
        spectralTranslationPhase
      fun_prop : Continuous (F M))).aestronglyMeasurable
  have hbound : ∀ᶠ M : ℕ in atTop, ∀ᵐ x : ℝ ∂mu,
      ‖F M x‖ ≤ bound x := by
    filter_upwards with M
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hsrc0 := thetaCuspTailSecondDensityFiniteAtomSource_nonneg M hx.le
    have hsrc := thetaCuspTailSecondDensityFiniteAtomSource_le M hx.le
    have hphase := norm_spectralTranslationPhase_le_one hx.le hz
    dsimp only [F, bound]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsrc0]
    calc
      thetaCuspTailSecondDensityFiniteAtomSource M x *
          ‖spectralTranslationPhase x z‖ ≤
        thetaCuspTailSecondDensityFiniteAtomSource M x := by
          exact mul_le_of_le_one_right hsrc0 hphase
      _ ≤ thetaCuspTailSecondDensity x := hsrc
  have hlim : ∀ᵐ x : ℝ ∂mu,
      Tendsto (fun M : ℕ => F M x) atTop
        (nhds ((thetaCuspTailSecondDensity x : ℂ) *
          spectralTranslationPhase x z)) := by
    filter_upwards with x
    have hreal := tendsto_thetaCuspTailSecondDensityFiniteAtomSource x
    have hcomplex : Tendsto
        (fun M : ℕ => (thetaCuspTailSecondDensityFiniteAtomSource M x : ℂ))
        atTop (nhds (thetaCuspTailSecondDensity x : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [F] using
      hcomplex.mul_const (spectralTranslationPhase x z)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    bound hFmeas hbound hboundInt hlim
  simpa only [thetaCuspTailSecondDensityFiniteAtomPhaseValue,
    thetaCuspTailSecondDensityPhaseValue, F, mu] using hDCT

theorem tendsto_thetaCuspTailSecondDensityFiniteAtomPhaseDerivative
    {z : ℂ} (hz : 0 ≤ z.im) :
    Tendsto
      (fun M : ℕ => thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z)
      atTop (nhds (thetaCuspTailSecondDensityPhaseDerivative z)) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℂ := fun M x =>
    (thetaCuspTailSecondDensityFiniteAtomSource M x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase x z)
  let bound : ℝ → ℝ := fun x =>
    x * thetaCuspTailSecondDensity x
  have hboundInt : Integrable bound mu := by
    have h := integrableOn_pow_mul_thetaCuspTailSecondDensity 1
    simp only [pow_one] at h
    exact h
  have hFmeas : ∀ᶠ M : ℕ in atTop, AEStronglyMeasurable (F M) mu := by
    filter_upwards with M
    exact ((by
      dsimp only [F, thetaCuspTailSecondDensityFiniteAtomSource]
      unfold thetaCuspTailSecondDensityAtom thetaCuspPolynomialAtom
        spectralTranslationPhase
      fun_prop : Continuous (F M))).aestronglyMeasurable
  have hbound : ∀ᶠ M : ℕ in atTop, ∀ᵐ x : ℝ ∂mu,
      ‖F M x‖ ≤ bound x := by
    filter_upwards with M
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hsrc0 := thetaCuspTailSecondDensityFiniteAtomSource_nonneg M hx0
    have hsrc := thetaCuspTailSecondDensityFiniteAtomSource_le M hx0
    have hphase := norm_spectralTranslationPhase_le_one hx0 hz
    have hxnorm : ‖(x : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    have hinner :
        ‖(x : ℂ) * I * spectralTranslationPhase x z‖ ≤ x := by
      rw [norm_mul, norm_mul, hxnorm, norm_I, mul_one]
      exact mul_le_of_le_one_right hx0 hphase
    dsimp only [F, bound]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsrc0]
    calc
      thetaCuspTailSecondDensityFiniteAtomSource M x *
          ‖(x : ℂ) * I * spectralTranslationPhase x z‖ ≤
        thetaCuspTailSecondDensityFiniteAtomSource M x * x := by
          exact mul_le_mul_of_nonneg_left hinner hsrc0
      _ ≤ thetaCuspTailSecondDensity x * x := by
          exact mul_le_mul_of_nonneg_right hsrc hx0
      _ = x * thetaCuspTailSecondDensity x := by ring
  have hlim : ∀ᵐ x : ℝ ∂mu,
      Tendsto (fun M : ℕ => F M x) atTop
        (nhds ((thetaCuspTailSecondDensity x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z))) := by
    filter_upwards with x
    have hreal := tendsto_thetaCuspTailSecondDensityFiniteAtomSource x
    have hcomplex : Tendsto
        (fun M : ℕ => (thetaCuspTailSecondDensityFiniteAtomSource M x : ℂ))
        atTop (nhds (thetaCuspTailSecondDensity x : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [F] using hcomplex.mul_const
      ((x : ℂ) * I * spectralTranslationPhase x z)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    bound hFmeas hbound hboundInt hlim
  simpa only [thetaCuspTailSecondDensityFiniteAtomPhaseDerivative,
    thetaCuspTailSecondDensityPhaseDerivative, F, mu] using hDCT

/-- Exact affine cancellation after the endpoint is computed with approximating source data.
The affine denominator disappears; the returned current is only the difference of the two base
currents. -/
theorem phaseAdaptedReturnedSourceCurrent_at_approximantEndpoint_eq
    (N : ℕ) (V₀ D₀ Vₛ Dₛ R R' A A' E E' : ℂ)
    (hden : dyadicAffineCurrentDenominator N
      (phaseAdaptedReturnedSourceSlopeCurrent Vₛ Dₛ E E')
      ((E' * (starRingEnd ℂ) E).im) ≠ 0) :
    let tau := phaseAdaptedReturnedSourceCancellationEndpoint
      N V₀ D₀ Vₛ Dₛ A A' E E'
    let c : ℝ := ((2 : ℝ) ^ N * tau + 1) / 4
    symmetricHermitianCrossCurrentData
        (-(V₀ + (tau : ℂ) * Vₛ) - R + (c : ℂ) * E)
        ((D₀ + (tau : ℂ) * Dₛ) - R' + (c : ℂ) * E') E E' =
      phaseAdaptedReturnedSourceBaseCurrent V₀ D₀ R R' E E' -
        phaseAdaptedReturnedSourceBaseCurrent V₀ D₀ A A' E E' := by
  dsimp only
  rw [phaseAdaptedReturnedSourceCurrent_affine]
  have hcancel := phaseAdaptedReturnedSourceCancellationEndpoint_cancels
    N V₀ D₀ Vₛ Dₛ A A' E E' hden
  dsimp only at hcancel
  rw [phaseAdaptedReturnedSourceCurrent_affine] at hcancel
  unfold phaseAdaptedReturnedSourceBaseCurrent
  linarith

/-- The critical returned current written in its endpoint-affine value--derivative coordinates. -/
theorem phaseAdaptedCriticalReturnedSourceCurrent_eq_affineData
    (m N : ℕ) (u : ℂ) (r tau : ℝ) (z R R' E E' : ℂ) :
    phaseAdaptedCriticalReturnedSourceCurrent m N u r tau z R R' E E' =
      let P₀ := phaseAdaptedTwoEndpointProuhetPolynomial m u
        dyadicProuhetDecayCharacter r 0
      let S := phaseAdaptedTwoEndpointProuhetEndpointSlope m u
        dyadicProuhetDecayCharacter r
      let V₀ := phaseAdaptedCriticalReturnedValuePairing P₀ N z
      let D₀ := phaseAdaptedCriticalReturnedDerivativePairing P₀ N z
      let Vₛ := phaseAdaptedCriticalReturnedValuePairing S N z
      let Dₛ := phaseAdaptedCriticalReturnedDerivativePairing S N z
      let c : ℝ := ((2 : ℝ) ^ N * tau + 1) / 4
      symmetricHermitianCrossCurrentData
        (-(V₀ + (tau : ℂ) * Vₛ) - R + (c : ℂ) * E)
        ((D₀ + (tau : ℂ) * Dₛ) - R' + (c : ℂ) * E') E E' := by
  dsimp only
  unfold phaseAdaptedCriticalReturnedSourceCurrent
  dsimp only
  rw [phaseAdaptedCriticalReturnedValuePairing_endpoint_affine,
    phaseAdaptedCriticalReturnedDerivativePairing_endpoint_affine]

/-- Endpoint obtained only from a finite square-index theta packet and elementary seam data. -/
def canonicalThetaTailFiniteArithmeticProuhetEndpoint
    (m N M : ℕ) (z : ℂ) : ℝ :=
  phaseAdaptedCriticalSelfConsistentEndpoint m N
    (spectralTranslationPhase (Real.log 2) z)
    dyadicProuhetGrowthCharacter z
    (thetaCuspTailSecondDensityFiniteAtomPhaseValue M z)
    (thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z)
    (thetaHalfExponentialPhaseValue z)
    (thetaHalfExponentialPhaseDerivative z)

/-- The actual canonical returned current evaluated at the finite arithmetic endpoint. -/
def canonicalThetaTailFiniteArithmeticUntruncatedCurrent
    (m N M : ℕ) (z : ℂ) : ℝ :=
  phaseAdaptedCriticalReturnedSourceCurrent m N
    (spectralTranslationPhase (Real.log 2) z)
    dyadicProuhetGrowthCharacter
    (canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z) z
    (thetaCuspTailSecondDensityPhaseValue z)
    (thetaCuspTailSecondDensityPhaseDerivative z)
    (thetaHalfExponentialPhaseValue z)
    (thetaHalfExponentialPhaseDerivative z)

theorem canonicalThetaTailFiniteArithmeticUntruncatedCurrent_eq_base_sub
    (m N M : ℕ) {z : ℂ}
    (hden : phaseAdaptedCriticalSelfConsistentDenominator m N
      (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) ≠ 0) :
    let u := spectralTranslationPhase (Real.log 2) z
    let P₀ := phaseAdaptedTwoEndpointProuhetPolynomial m u
      dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter 0
    let V₀ := phaseAdaptedCriticalReturnedValuePairing P₀ N z
    let D₀ := phaseAdaptedCriticalReturnedDerivativePairing P₀ N z
    canonicalThetaTailFiniteArithmeticUntruncatedCurrent m N M z =
      phaseAdaptedReturnedSourceBaseCurrent V₀ D₀
        (thetaCuspTailSecondDensityPhaseValue z)
        (thetaCuspTailSecondDensityPhaseDerivative z)
        (thetaHalfExponentialPhaseValue z)
        (thetaHalfExponentialPhaseDerivative z) -
      phaseAdaptedReturnedSourceBaseCurrent V₀ D₀
        (thetaCuspTailSecondDensityFiniteAtomPhaseValue M z)
        (thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z)
        (thetaHalfExponentialPhaseValue z)
        (thetaHalfExponentialPhaseDerivative z) := by
  dsimp only
  let u := spectralTranslationPhase (Real.log 2) z
  let P₀ := phaseAdaptedTwoEndpointProuhetPolynomial m u
    dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter 0
  let S := phaseAdaptedTwoEndpointProuhetEndpointSlope m u
    dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter
  let V₀ := phaseAdaptedCriticalReturnedValuePairing P₀ N z
  let D₀ := phaseAdaptedCriticalReturnedDerivativePairing P₀ N z
  let Vₛ := phaseAdaptedCriticalReturnedValuePairing S N z
  let Dₛ := phaseAdaptedCriticalReturnedDerivativePairing S N z
  let A := thetaCuspTailSecondDensityFiniteAtomPhaseValue M z
  let A' := thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z
  let R := thetaCuspTailSecondDensityPhaseValue z
  let R' := thetaCuspTailSecondDensityPhaseDerivative z
  let E := thetaHalfExponentialPhaseValue z
  let E' := thetaHalfExponentialPhaseDerivative z
  have hgeneric := phaseAdaptedReturnedSourceCurrent_at_approximantEndpoint_eq
    N V₀ D₀ Vₛ Dₛ R R' A A' E E' (by
      simpa only [phaseAdaptedCriticalSelfConsistentDenominator,
        S, Vₛ, Dₛ, E, E'] using hden)
  unfold canonicalThetaTailFiniteArithmeticUntruncatedCurrent
    canonicalThetaTailFiniteArithmeticProuhetEndpoint
  rw [phaseAdaptedCriticalReturnedSourceCurrent_eq_affineData]
  unfold phaseAdaptedCriticalSelfConsistentEndpoint
  dsimp only [u, P₀, S, V₀, D₀, Vₛ, Dₛ, A, A', R, R', E, E'] at hgeneric ⊢
  exact hgeneric

theorem tendsto_canonicalThetaTailFiniteArithmeticUntruncatedCurrent
    (m N : ℕ) {z : ℂ} (hz : 0 ≤ z.im)
    (hden : phaseAdaptedCriticalSelfConsistentDenominator m N
      (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) ≠ 0) :
    Tendsto (fun M : ℕ =>
      canonicalThetaTailFiniteArithmeticUntruncatedCurrent m N M z)
      atTop (nhds 0) := by
  let u := spectralTranslationPhase (Real.log 2) z
  let P₀ := phaseAdaptedTwoEndpointProuhetPolynomial m u
    dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter 0
  let V₀ := phaseAdaptedCriticalReturnedValuePairing P₀ N z
  let D₀ := phaseAdaptedCriticalReturnedDerivativePairing P₀ N z
  let R := thetaCuspTailSecondDensityPhaseValue z
  let R' := thetaCuspTailSecondDensityPhaseDerivative z
  let E := thetaHalfExponentialPhaseValue z
  let E' := thetaHalfExponentialPhaseDerivative z
  have hR := tendsto_thetaCuspTailSecondDensityFiniteAtomPhaseValue hz
  have hR' := tendsto_thetaCuspTailSecondDensityFiniteAtomPhaseDerivative hz
  have hbase : Tendsto (fun M : ℕ =>
      phaseAdaptedReturnedSourceBaseCurrent V₀ D₀
        (thetaCuspTailSecondDensityFiniteAtomPhaseValue M z)
        (thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z) E E')
      atTop (nhds (phaseAdaptedReturnedSourceBaseCurrent V₀ D₀ R R' E E')) := by
    have hvalue : Tendsto (fun M : ℕ =>
        -V₀ - thetaCuspTailSecondDensityFiniteAtomPhaseValue M z +
          (1 / 4 : ℂ) * E) atTop
        (nhds (-V₀ - R + (1 / 4 : ℂ) * E)) := by
      exact (tendsto_const_nhds.sub hR).add tendsto_const_nhds
    have hderivative : Tendsto (fun M : ℕ =>
        D₀ - thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z +
          (1 / 4 : ℂ) * E') atTop
        (nhds (D₀ - R' + (1 / 4 : ℂ) * E')) := by
      exact (tendsto_const_nhds.sub hR').add tendsto_const_nhds
    simpa only [phaseAdaptedReturnedSourceBaseCurrent] using
      symmetricHermitianCrossCurrentData_tendsto
        (E := E) (E' := E') hvalue hderivative
  have hdiff : Tendsto (fun M : ℕ =>
      phaseAdaptedReturnedSourceBaseCurrent V₀ D₀ R R' E E' -
        phaseAdaptedReturnedSourceBaseCurrent V₀ D₀
          (thetaCuspTailSecondDensityFiniteAtomPhaseValue M z)
          (thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z) E E')
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ =>
        phaseAdaptedReturnedSourceBaseCurrent V₀ D₀ R R' E E') atTop
        (nhds (phaseAdaptedReturnedSourceBaseCurrent V₀ D₀ R R' E E')) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hbase
  apply hdiff.congr'
  filter_upwards with M
  exact (canonicalThetaTailFiniteArithmeticUntruncatedCurrent_eq_base_sub
    m N M hden).symm

end

end RHTower

namespace RHTower

noncomputable section

/-- Literal signed Haar current whose endpoint is computed from only finitely many square-index
atoms. -/
def canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent
    (m N M : ℕ) (z : ℂ) : ℝ :=
  phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z
    (canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z)

theorem canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent_eq
    (m N M : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2) :
    canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent
        m N M z =
      (1 / 2 : ℝ) *
        canonicalThetaTailFiniteArithmeticUntruncatedCurrent m N M z := by
  unfold canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent
  rw [phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint_eq
    m N hz0 hzHalf]
  rfl

theorem
    tendsto_canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent
    (m N : ℕ) {z : ℂ} (hz0 : 0 < z.im)
    (hzHalf : z.im < 1 / 2)
    (hden : phaseAdaptedCriticalSelfConsistentDenominator m N
      (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) ≠ 0) :
    Tendsto (fun M : ℕ =>
      canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent
        m N M z) atTop (nhds 0) := by
  have h := (tendsto_canonicalThetaTailFiniteArithmeticUntruncatedCurrent
    m N hz0.le hden).const_mul (1 / 2 : ℝ)
  have heq : (fun M : ℕ =>
      (1 / 2 : ℝ) * canonicalThetaTailFiniteArithmeticUntruncatedCurrent
        m N M z) =ᶠ[atTop]
      (fun M : ℕ =>
        canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent
          m N M z) := by
    filter_upwards with M
    exact (canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent_eq
      m N M hz0 hzHalf).symm
  simpa only [mul_zero] using h.congr' heq

/-- **Independent finite-arithmetic upper cancellation.**  On every admissible anisotropic mesh,
one first selects a finite Haar depth with nonzero elementary affine denominator and then a finite
square-index cutoff.  The endpoint uses only that finite theta packet, while the actual integrated
untruncated Haar current is smaller than any prescribed sublinear multiple of the squared final
Taylor value. -/
theorem eventually_exists_canonicalThetaTailFiniteArithmeticHaarCurrent_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) (hsigma0 : 0 < sigma.re) (hsigmaHalf : sigma.re < 1 / 2)
    (m : ℕ → ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∃ N M : ℕ,
      canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent
          (m n) N M (xiCTaylorAnisotropicCenteredPoint sigma n) <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  have hzero : Tendsto (fun n : ℕ =>
      (0 : ℝ) * (((n + 1 : ℕ) : ℝ) ^
        (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
    simp
  have hpositive :=
    eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
      hD sigma (fun _ : ℕ => (0 : ℝ)) hzero hepsilon
  have himPos :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_pos sigma hsigmaHalf
  have himHalf :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_lt_half sigma hsigma0
  filter_upwards [hpositive, himPos, himHalf] with n hn hzn0 hznHalf
  let z := xiCTaylorAnisotropicCenteredPoint sigma n
  let E := thetaHalfExponentialPhaseValue z
  let E' := thetaHalfExponentialPhaseDerivative z
  have hQ : (E' * (starRingEnd ℂ) E).im ≠ 0 := by
    dsimp only [E, E']
    exact thetaHalfExponentialPhaseCurrent_ne_zero (by linarith)
  have hdenEventually :=
    phaseAdaptedCriticalSelfConsistentDenominator_eventually_ne_zero
      (m n) (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter hznHalf E E' hQ
  obtain ⟨N, hN⟩ := hdenEventually.exists
  have htend :=
    tendsto_canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent
      (m n) N hzn0 hznHalf (by
        simpa only [z, E, E'] using hN)
  have heventually : ∀ᶠ M : ℕ in atTop,
      canonicalThetaTailFiniteArithmeticWeightedReflectedHaarIntegratedCurrent
          (m n) N M z <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval z) := by
    exact htend.eventually (eventually_lt_nhds (by simpa only [z] using hn))
  obtain ⟨M, hM⟩ := heventually.exists
  exact ⟨N, M, by simpa only [z] using hM⟩

end

end RHTower
