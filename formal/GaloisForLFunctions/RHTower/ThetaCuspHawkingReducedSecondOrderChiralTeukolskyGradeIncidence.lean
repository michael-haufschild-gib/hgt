import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEClockLogarithmicMonodromyTransduction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullEinsteinGaugeFixedRadiationGram
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyTiltedAngularLeakage

/-!
# Reduced second-order chiral Teukolsky grade incidence

The reduced second-order chiral Teukolsky source is resolved by composing the full-Einstein
quadratic grade source with the exact ingoing Birmingham--Mokhtari Green coefficient and the
orthogonal-helicity Teukolsky projection.  At the holomorphic doubled weight `2s`, exact Einstein
grade separation deletes every mixed and anti-chiral same-grade counterterm.

The surviving coefficient is the existing physical mixed-horizon source projection, hence the
nowhere-zero HC58 transducer times the HC57 source-FE centered-QNM clock defect.  For a nonzero
Einstein seed it is nonzero exactly at tilted divisors, exactly when the same doubled cusp weight
lies off the unitary Eisenstein line.  Every separated nonzero source profile then has nonzero
residual against a symmetric one-sector horizon angular operator.

This closes the previously stated nonvanishing `2s` source-incidence core on tilted fibres.  The
remaining physical producer is a law forbidding the forced angular leakage; no such law is assumed
here.

`[NEW] [SECOND-ORDER TEUKOLSKY SOURCE] [2S INCIDENCE] [ANGULAR LEAKAGE] [LEAN-PROVED]`
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Grade-resolved reduced second-order chiral Teukolsky source obtained by composing the full
Einstein quadratic source with the exact ingoing BM Green coefficient and helicity projection. -/
def d4ThetaReducedSecondOrderChiralTeukolskyGradeSource
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) (weight : ℂ) : ℂ :=
  d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q *
    (d4BMGaugeFixedSecondHarmonicGreen q *
      d4ThetaFullEinsteinQuadraticGradeSource amplitude mixed anti q weight)

/-- At the doubled holomorphic grade, the reduced source is exactly the existing physical
mixed-horizon optical source projection. -/
theorem d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_opticalSource
    (amplitude mixed anti orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) =
      d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q := by
  rw [d4ThetaReducedSecondOrderChiralTeukolskyGradeSource,
    d4ThetaFullEinsteinQuadraticGradeSource_sameGrade_eq_selfDual,
    d4BMMixedHorizonOpticalSourceProjection_eq]

/-- The actual reduced `2s` Teukolsky source coefficient is the nowhere-zero HC58 transducer
times the HC57 reflected centered-clock defect. -/
theorem d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_clockDefect
    (n : ℕ) (amplitude mixed anti orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) =
      hbXiPeierlsClockToChiralSourceTransducer amplitude q *
        hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient n q := by
  rw [d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_opticalSource
      amplitude mixed anti orthogonalMixing q,
    d4BMMixedHorizonOpticalSourceProjection_eq_clockTransducer_mul_defectCoefficient
      (n := n)]

/-- For a nonzero seed, the reduced second-order chiral `2s` coefficient is nonzero exactly at a
tilted divisor. -/
theorem d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (mixed anti orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) ≠ 0 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_opticalSource
      amplitude mixed anti orthogonalMixing q]
  exact not_congr
    (d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half
      ha orthogonalMixing q)

/-- Universal extinction of the exact reduced second-order chiral `2s` coefficient is RH. -/
theorem forall_d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_zero_iff_rh
    {amplitude : ℂ} (ha : amplitude ≠ 0) (n : ℕ) (mixed anti : ℂ) :
    (∀ q : XiZeroCopy,
      d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) = 0) ↔
      RiemannHypothesis := by
  rw [← forall_hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq_zero_iff_rh n]
  constructor
  · intro hall q
    have hsource := hall q
    rw [d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_clockDefect
      n amplitude mixed anti 0 q, mul_eq_zero] at hsource
    exact hsource.resolve_left
      (hbXiPeierlsClockToChiralSourceTransducer_ne_zero ha q)
  · intro hall q
    rw [d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_clockDefect
      n amplitude mixed anti 0 q, hall q, mul_zero]

/-- The doubled holomorphic source weight is nonunitary exactly at a tilted divisor. -/
theorem d4ThetaTeukolskyQuadraticChiralCuspWeight_xi_re_ne_half_iff
    (q : XiZeroCopy) :
    (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)).re ≠ 1 / 2 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hweight hline
    apply hweight
    apply (d4ThetaTeukolskyQuadraticChiralCuspWeight_re_eq_half_iff
      (xiSpectralPoint q)).2
    rw [xiSpectralPoint_im_eq]
    linarith
  · intro hline hweight
    apply hline
    have him := (d4ThetaTeukolskyQuadraticChiralCuspWeight_re_eq_half_iff
      (xiSpectralPoint q)).1 hweight
    rw [xiSpectralPoint_im_eq] at him
    linarith

/-- For a nonzero seed, excitation of the exact reduced `2s` source is equivalent to failure of
unitary-line admission of that same doubled weight. -/
theorem d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_ne_zero_iff_weight_nonunitary
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (mixed anti orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) ≠ 0 ↔
      (d4ThetaTeukolskyQuadraticChiralCuspWeight
        (xiSpectralPoint q)).re ≠ 1 / 2 := by
  rw [d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff
      ha mixed anti orthogonalMixing q,
    d4ThetaTeukolskyQuadraticChiralCuspWeight_xi_re_ne_half_iff]

/-- Physical one-sector admission rule for every excited doubled principal source. -/
def D4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceIsUnitary
    (amplitude mixed anti : ℂ) : Prop :=
  ∀ q : XiZeroCopy,
    d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) ≠ 0 →
      (d4ThetaTeukolskyQuadraticChiralCuspWeight
        (xiSpectralPoint q)).re = 1 / 2

/-- For any nonzero seed, requiring every excited reduced `2s` source to remain in a single
self-adjoint principal-series channel is equivalent to RH. -/
theorem d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceIsUnitary_iff_rh
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (mixed anti : ℂ) :
    D4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceIsUnitary
        amplitude mixed anti ↔ RiemannHypothesis := by
  constructor
  · intro hunitary
    apply (riemannHypothesis_iff_d4ThetaTeukolskyQuadraticChiralPrincipalReturnIsUnitary).2
    intro q
    by_cases hline : (q.1 : ℂ).re = 1 / 2
    · exact (d4ThetaTeukolskyQuadraticChiralCuspWeight_re_eq_half_iff
        (xiSpectralPoint q)).2 (by rw [xiSpectralPoint_im_eq]; linarith)
    · exact hunitary q
        ((d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff
          ha mixed anti 0 q).2 hline)
  · intro hRH
    have hreturn :=
      (riemannHypothesis_iff_d4ThetaTeukolskyQuadraticChiralPrincipalReturnIsUnitary).1 hRH
    intro q hsource
    exact hreturn q

/-- A separated angular profile carrying the actual reduced doubled-grade source coefficient. -/
def d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (amplitude mixed anti : ℂ) (profile : H) (q : XiZeroCopy) : H :=
  d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
      (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) • profile

/-- Every nonzero tilted reduced `2s` source profile is nonzero. -/
theorem d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector_ne_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (mixed anti orthogonalMixing : ℂ) (profile : H) (hprofile : profile ≠ 0)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
        amplitude mixed anti profile q ≠ 0 := by
  apply smul_ne_zero
  · exact (d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff
      ha mixed anti orthogonalMixing q).2 htilt
  · exact hprofile

/-- Source-level closure of the old `2s` open core: every tilted reduced second-order chiral
source has nonzero residual against any symmetric one-sector horizon angular operator. -/
theorem d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSource_tilted_forces_angularLeakage
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H → H) {amplitude : ℂ} (mixed anti orthogonalMixing : ℂ)
    (profile : H) (q : XiZeroCopy)
    (hsa :
      ⟪d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
          amplitude mixed anti profile q,
        A (d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
          amplitude mixed anti profile q)⟫_ℂ =
      ⟪A (d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
          amplitude mixed anti profile q),
        d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
          amplitude mixed anti profile q⟫_ℂ)
    (ha : amplitude ≠ 0) (hprofile : profile ≠ 0)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    A (d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
        amplitude mixed anti profile q) -
      d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue (xiSpectralPoint q) •
        d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
          amplitude mixed anti profile q ≠ 0 := by
  apply d4ThetaTeukolsky_tiltedAngularSource_forces_leakage
    A (d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
      amplitude mixed anti profile q) q hsa
  · exact d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector_ne_zero
      ha mixed anti orthogonalMixing profile hprofile q htilt
  · rw [xiSpectralPoint_im_eq]
    intro him
    apply htilt
    linarith

end

end RHTower
