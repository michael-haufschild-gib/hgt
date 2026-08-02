import GaloisForLFunctions.HTGeometry.PointedShiftIncidence
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaUnitPeriod
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy

/-!
# The pointed incidence fibres of the elliptic gamma logarithmic derivative

The logarithmic derivative of the two-period elliptic gamma function is fixed by the unit period and
hypertranscendental exactly when the two periods together with `1` are rationally independent.  Both
hypotheses of the pointed incidence phase therefore hold for it, and the two fibres of its own
two-shift boundary are a singleton and the empty set.

This is the analytic realization of the incidence-index principle: the same thin boundary has no
pointed differentially algebraic primitive and exactly one ambient one.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {sigma tau : ℂ}

/-- The two-period family. -/
def ellipticPeriodPair (sigma tau : ℂ) : Fin 2 → ℂ := ![sigma, tau]

theorem ellipticPeriodPair_im_pos (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ∀ i, 0 < (ellipticPeriodPair sigma tau i).im := by
  intro i
  fin_cases i
  · exact hsigma
  · exact htau

/-- The logarithmic derivative of the two-period elliptic gamma, as a meromorphic-field element. -/
def ellipticLogDerivMero (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    meroField (Set.univ : Set ℂ) :=
  multipleEllipticGammaLogDerivMero (ellipticPeriodPair sigma tau)
    (ellipticPeriodPair_im_pos hsigma htau)

theorem unitPeriod_defect_ellipticLogDerivMero (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    addTranslationMeroEquiv 1 (ellipticLogDerivMero hsigma htau)
      - ellipticLogDerivMero hsigma htau = 0 := by
  rw [ellipticLogDerivMero, addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero,
    sub_self]

theorem rankThreeMinor_ellipticPeriodPair
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    MultipleEllipticGammaHasRankThreeMinor (ellipticPeriodPair sigma tau) := by
  refine ⟨0, 1, by decide, ?_⟩
  have hval : ellipticGammaSourcePeriods (ellipticPeriodPair sigma tau 0)
      (ellipticPeriodPair sigma tau 1) = ellipticGammaSourcePeriods sigma tau := by
    rfl
  rw [hval]
  exact hindep

theorem hypertranscendental_ellipticLogDerivMero (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    HypertranscendentalOver (RatFunc ℂ) (ellipticLogDerivMero hsigma htau) := by
  rw [ellipticLogDerivMero]
  exact (hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_rankThreeMinor
    (ellipticPeriodPair sigma tau) (ellipticPeriodPair_im_pos hsigma htau)).2
    (rankThreeMinor_ellipticPeriodPair hindep)

/-- **Equation (14b), ambient half.**  The pointed ambient fibre of the elliptic-gamma logarithmic
derivative's own two-shift boundary is exactly that logarithmic derivative. -/
theorem ellipticLogDeriv_ambient_incidence (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (P : ConstantPointing) :
    shiftIncidence Set.univ sigma tau
        (addTranslationMeroEquiv sigma (ellipticLogDerivMero hsigma htau)
          - ellipticLogDerivMero hsigma htau)
        (addTranslationMeroEquiv tau (ellipticLogDerivMero hsigma htau)
          - ellipticLogDerivMero hsigma htau)
        P (P.ev (ellipticLogDerivMero hsigma htau))
      = {ellipticLogDerivMero hsigma htau} :=
  shiftIncidence_ambient_eq_singleton hindep (unitPeriod_defect_ellipticLogDerivMero hsigma htau)

/-- **Equation (14b), thin half.**  The pointed differentially algebraic fibre of the same boundary
is empty. -/
theorem ellipticLogDeriv_da_incidence (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (P : ConstantPointing) :
    shiftIncidence daSector sigma tau
        (addTranslationMeroEquiv sigma (ellipticLogDerivMero hsigma htau)
          - ellipticLogDerivMero hsigma htau)
        (addTranslationMeroEquiv tau (ellipticLogDerivMero hsigma htau)
          - ellipticLogDerivMero hsigma htau)
        P (P.ev (ellipticLogDerivMero hsigma htau))
      = ∅ :=
  shiftIncidence_da_eq_empty hindep (unitPeriod_defect_ellipticLogDerivMero hsigma htau)
    (hypertranscendental_ellipticLogDerivMero hsigma htau hindep)

/-- **The pointed bi-anomaly incidence phase.**  For rationally independent periods the elliptic
gamma logarithmic derivative realizes both sides of the incidence-index principle: an empty pointed
differentially algebraic fibre and a singleton pointed ambient fibre. -/
theorem ellipticLogDeriv_pointed_incidence_phase (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (P : ConstantPointing) :
    shiftIncidence daSector sigma tau
        (addTranslationMeroEquiv sigma (ellipticLogDerivMero hsigma htau)
          - ellipticLogDerivMero hsigma htau)
        (addTranslationMeroEquiv tau (ellipticLogDerivMero hsigma htau)
          - ellipticLogDerivMero hsigma htau)
        P (P.ev (ellipticLogDerivMero hsigma htau)) = ∅
      ∧ shiftIncidence Set.univ sigma tau
        (addTranslationMeroEquiv sigma (ellipticLogDerivMero hsigma htau)
          - ellipticLogDerivMero hsigma htau)
        (addTranslationMeroEquiv tau (ellipticLogDerivMero hsigma htau)
          - ellipticLogDerivMero hsigma htau)
        P (P.ev (ellipticLogDerivMero hsigma htau))
      = {ellipticLogDerivMero hsigma htau} :=
  ⟨ellipticLogDeriv_da_incidence hsigma htau hindep P,
    ellipticLogDeriv_ambient_incidence hsigma htau hindep P⟩

end

end GaloisForLFunctions.HTGeometry
