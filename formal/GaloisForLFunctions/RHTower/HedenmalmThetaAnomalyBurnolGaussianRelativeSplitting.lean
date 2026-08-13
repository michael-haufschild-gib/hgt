import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyBurnolAffineGaugeClassification
import GaloisForLFunctions.RHTower.RiemannSourceForcedHorizontalVanishingFrontier

/-!
# Gaussian/Burnol relative splitting on the Xi divisor

P-G114 isolates the unique transverse gauge of every two-prime Burnol singular synthesis.  Here
that gauge is fixed by independent source geometry: normalized reflected-Gaussian Wronskian, equal
to the prime-tail Gamma/co-Poisson horizontal parameter.

The resulting Gaussian-deformed Burnol row still reconstructs the quotient exactly.  Its failure
to descend through critical-line reflection is explicit, has a strictly positive squared norm, and
vanishes exactly on the critical line.  Globally, descent of this constructed source splitting is
equivalent to RH.  This identifies RH as equality of canonical Burnol and Gaussian source
splittings, without assuming either splitting or fitting a coefficient.
-/

open Complex Real

namespace RHTower

noncomputable section

open DeningerMeyerGaussianGreen

namespace HedenmalmThetaSource

/-- Independent Gaussian/Gamma source gauge inserted into the Burnol affine synthesis torsor. -/
def thetaXiBurnolGaussianHorizontalGauge (q : XiZeroCopy) : ℂ :=
  ((riemannSourceGammaCoPoissonHorizontalParameter q.1 : ℝ) : ℂ)

def thetaXiBurnolGaussianSynthesisFrame (q : XiZeroCopy) : ℂ × ℂ :=
  burnolAffineSynthesisFrame (thetaXiBurnolGaussianHorizontalGauge q)
    (xiSpectralPoint q)

theorem thetaXiBurnolGaussianSynthesis_reconstructs_one (q : XiZeroCopy) :
    (thetaXiBurnolGaussianSynthesisFrame q).1 *
        (thetaXiBurnolAnomalyQuotientFrame q).1 +
      (thetaXiBurnolGaussianSynthesisFrame q).2 *
        (thetaXiBurnolAnomalyQuotientFrame q).2 = 1 := by
  exact burnolAffineSynthesis_identity _ _

theorem thetaXiBurnolGaussianSynthesis_gauge (q : XiZeroCopy) :
    burnolSynthesisGauge (xiSpectralPoint q)
        (thetaXiBurnolGaussianSynthesisFrame q).1
        (thetaXiBurnolGaussianSynthesisFrame q).2 =
      thetaXiBurnolGaussianHorizontalGauge q := by
  exact burnolAffineSynthesis_gauge _ _

/-- The affine gauge is literally the normalized reflected-Gaussian source Wronskian. -/
theorem thetaXiBurnolGaussianHorizontalGauge_eq_wronskian_div_scale
    (q : XiZeroCopy) :
    thetaXiBurnolGaussianHorizontalGauge q =
      deningerMeyerReflectedGaussianLineWronskian q /
        deningerMeyerReflectedGaussianLinePairScale q := by
  rw [thetaXiBurnolGaussianHorizontalGauge,
    deningerMeyerReflectedGaussianLineWronskian_eq_sourceParameter_mul]
  exact (mul_div_cancel_right₀ _
    (deningerMeyerReflectedGaussianLinePairScale_ne_zero q)).symm

theorem thetaXiBurnolGaussianHorizontalGauge_lineConj (q : XiZeroCopy) :
    thetaXiBurnolGaussianHorizontalGauge (xiZeroCopyLineConjEquiv q) =
      -thetaXiBurnolGaussianHorizontalGauge q := by
  rw [thetaXiBurnolGaussianHorizontalGauge, thetaXiBurnolGaussianHorizontalGauge,
    riemannSourceGammaCoPoissonHorizontalParameter]
  change ((-riemannReflectedSourceEntropy
      (1 - starRingEnd ℂ (q.1 : ℂ)) : ℝ) : ℂ) =
    -((-riemannReflectedSourceEntropy (q.1 : ℂ) : ℝ) : ℂ)
  have href := riemannReflectedSourceEntropy_reflection (q.1 : ℂ)
  change riemannReflectedSourceEntropy
      (1 - starRingEnd ℂ (q.1 : ℂ)) =
    -riemannReflectedSourceEntropy (q.1 : ℂ) at href
  rw [href]
  push_cast
  ring

theorem thetaXiBurnolGaussianHorizontalGauge_real (q : XiZeroCopy) :
    (starRingEnd ℂ) (thetaXiBurnolGaussianHorizontalGauge q) =
      thetaXiBurnolGaussianHorizontalGauge q := by
  simp [thetaXiBurnolGaussianHorizontalGauge]

/-- Exact two-coordinate failure of the Gaussian-deformed Burnol splitting to descend through
critical-line reflection. -/
theorem thetaXiBurnolGaussianSynthesis_lineConj_defect (q : XiZeroCopy) :
    (thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).1 -
        (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).1 =
      -2 * thetaXiBurnolGaussianHorizontalGauge q *
        (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 3 (xiSpectralPoint q)) ∧
    (thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).2 -
        (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).2 =
      2 * thetaXiBurnolGaussianHorizontalGauge q *
        (starRingEnd ℂ) (burnolCompletedCenteredMultiplier 2 (xiSpectralPoint q)) := by
  rw [thetaXiBurnolGaussianSynthesisFrame, thetaXiBurnolGaussianSynthesisFrame,
    xiSpectralPoint_lineConj, thetaXiBurnolGaussianHorizontalGauge_lineConj]
  rw [burnolAffineSynthesisFrame, burnolAffineSynthesisFrame]
  dsimp only [Prod.fst, Prod.snd]
  simp only [map_add, map_mul, map_sub]
  rw [burnolCanonicalSynthesisCoefficient_conj,
    burnolCanonicalSynthesisCoefficient_conj,
    burnolCompletedCenteredMultiplier_conj,
    burnolCompletedCenteredMultiplier_conj,
    thetaXiBurnolGaussianHorizontalGauge_real]
  constructor <;> ring

def thetaXiBurnolGaussianReflectionDefectEnergy (q : XiZeroCopy) : ℝ :=
  Complex.normSq
      ((thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).1 -
        (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).1) +
    Complex.normSq
      ((thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).2 -
        (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).2)

/-- Reflection defect energy is four times squared horizontal source gauge times Burnol frame
energy. -/
theorem thetaXiBurnolGaussianReflectionDefectEnergy_exact (q : XiZeroCopy) :
    thetaXiBurnolGaussianReflectionDefectEnergy q =
      4 * Complex.normSq (thetaXiBurnolGaussianHorizontalGauge q) *
        burnolTwoPrimeFrameEnergy (xiSpectralPoint q) := by
  obtain ⟨h2, h3⟩ := thetaXiBurnolGaussianSynthesis_lineConj_defect q
  rw [thetaXiBurnolGaussianReflectionDefectEnergy, h2, h3,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_conj,
    Complex.normSq_conj, burnolTwoPrimeFrameEnergy]
  norm_num [Complex.normSq_apply]
  ring

theorem thetaXiBurnolGaussianHorizontalGauge_eq_zero_iff (q : XiZeroCopy) :
    thetaXiBurnolGaussianHorizontalGauge q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaXiBurnolGaussianHorizontalGauge]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp only [ofReal_re, zero_re] at hr
    exact (riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff q.1).1
      ((riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff_parameter_eq_zero q.1).2 hr)
  · intro h
    have hp := (riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff_parameter_eq_zero q.1).1
      ((riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff q.1).2 h)
    exact_mod_cast hp

theorem thetaXiBurnolGaussianReflectionDefectEnergy_eq_zero_iff (q : XiZeroCopy) :
    thetaXiBurnolGaussianReflectionDefectEnergy q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaXiBurnolGaussianReflectionDefectEnergy_exact]
  have hE := burnolTwoPrimeFrameEnergy_pos (xiSpectralPoint q)
  constructor
  · intro h
    have hg : Complex.normSq (thetaXiBurnolGaussianHorizontalGauge q) = 0 := by
      nlinarith
    exact (thetaXiBurnolGaussianHorizontalGauge_eq_zero_iff q).1
      (Complex.normSq_eq_zero.mp hg)
  · intro h
    rw [(thetaXiBurnolGaussianHorizontalGauge_eq_zero_iff q).2 h,
      Complex.normSq_zero]
    ring

/-- Local descent of constructed Gaussian/Burnol splitting is exactly critical-line placement. -/
theorem thetaXiBurnolGaussianSynthesis_descends_iff (q : XiZeroCopy) :
    thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q) =
        ((starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).1,
          (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).2) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [← thetaXiBurnolGaussianReflectionDefectEnergy_eq_zero_iff]
  constructor
  · intro h
    rw [thetaXiBurnolGaussianReflectionDefectEnergy, h]
    simp
  · intro h
    rw [thetaXiBurnolGaussianReflectionDefectEnergy] at h
    have h1 :
        (thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).1 -
          (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).1 = 0 := by
      have hn1 := Complex.normSq_nonneg
        ((thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).1 -
          (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).1)
      have hn2 := Complex.normSq_nonneg
        ((thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).2 -
          (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).2)
      exact Complex.normSq_eq_zero.mp (by nlinarith)
    have h2 :
        (thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).2 -
          (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).2 = 0 := by
      have hn1 := Complex.normSq_nonneg
        ((thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).1 -
          (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).1)
      have hn2 := Complex.normSq_nonneg
        ((thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q)).2 -
          (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).2)
      exact Complex.normSq_eq_zero.mp (by nlinarith)
    apply Prod.ext
    · exact sub_eq_zero.mp h1
    · exact sub_eq_zero.mp h2

/-- **Relative-splitting RH equivalence.**  Constructed Gaussian-deformed Burnol singular synthesis
descends on every Xi copy exactly when RH holds. -/
theorem thetaXiBurnolGaussianSynthesis_descends_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      thetaXiBurnolGaussianSynthesisFrame (xiZeroCopyLineConjEquiv q) =
        ((starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).1,
          (starRingEnd ℂ) (thetaXiBurnolGaussianSynthesisFrame q).2)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    rw [← deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis]
    intro q
    rw [deningerMeyerReflectedGaussianLineWronskian_eq_sourceParameter_mul]
    have hline := (thetaXiBurnolGaussianSynthesis_descends_iff q).1 (h q)
    have hg := (thetaXiBurnolGaussianHorizontalGauge_eq_zero_iff q).2 hline
    have hgreal := congrArg Complex.re hg
    simp only [thetaXiBurnolGaussianHorizontalGauge, ofReal_re, zero_re] at hgreal
    rw [hgreal, ofReal_zero, zero_mul]
  · intro hRH q
    have hw : deningerMeyerReflectedGaussianLineWronskian q = 0 :=
      (deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis).2 hRH q
    have hp : riemannSourceGammaCoPoissonHorizontalParameter q.1 = 0 := by
      rw [deningerMeyerReflectedGaussianLineWronskian_eq_sourceParameter_mul] at hw
      exact_mod_cast (mul_eq_zero.mp hw).resolve_right
        (deningerMeyerReflectedGaussianLinePairScale_ne_zero q)
    apply (thetaXiBurnolGaussianSynthesis_descends_iff q).2
    exact (riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff q.1).1
      ((riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff_parameter_eq_zero q.1).2 hp)

end HedenmalmThetaSource

end

end RHTower
