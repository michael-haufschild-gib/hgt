import GaloisForLFunctions.RHTower.HedenmalmThetaQuantileResolventPortLaw
import GaloisForLFunctions.RHTower.HedenmalmThetaXiMassPhaseLinearWeld

/-!
# Polarized Green realization of the Route T mass packet

The theta quantile source is a nonzero lightlike boundary state.  Cross-polarization by this fixed
state, rather than quadratic energy, extracts the symmetric boundary port sum exactly.  Therefore
Route T's complete safe-line resolvent packet is a coherent superposition of polarized metric
commutator currents.  This representation remains unsquared and phase-linear.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Mass test paired with the fixed-source polarized symplectic current. -/
def xiMassThetaQuantileMetricSymplecticIntegrand
    (a c : ℝ) (tau : ℂ) (x : ℝ) : ℂ :=
  xiMassBottomTest a c tau x *
    thetaQuantileMetricSymplecticCurrent
      (thetaComplexResolvent (thetaEsscherResolventParameter c (-x))
        thetaQuantileCoordinate)

/-- Complete polarized Green packet on a legal exterior theta line. -/
def xiMassThetaQuantileMetricSymplecticIntegral
    (a c : ℝ) (tau : ℂ) : ℂ :=
  ∫ x : ℝ, xiMassThetaQuantileMetricSymplecticIntegrand a c tau x

/-- Pointwise current is `i` times the fixed dipole charge times the Route T row integrand. -/
theorem xiMassThetaQuantileMetricSymplecticIntegrand_eq_I_mul_resolventIntegrand
    {a c : ℝ} (hhalf : 1 / 2 < c) (tau : ℂ) (x : ℝ) :
    xiMassThetaQuantileMetricSymplecticIntegrand a c tau x =
      Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
        xiMassThetaQuantileResolventIntegrand a c tau x := by
  have hcabs : 1 / 2 ≤ |c| := by
    rw [abs_of_pos (lt_trans (by norm_num) hhalf)]
    exact hhalf.le
  have hpencil : IsUnit
      (thetaSourcePencil (thetaEsscherResolventParameter c (-x))) :=
    isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs
      hcabs (-x)
  rw [xiMassThetaQuantileMetricSymplecticIntegrand,
    xiMassThetaQuantileResolventIntegrand,
    thetaQuantileMetricSymplecticCurrent_resolvent_eq_I_mul_pinnedMean hpencil]
  ring

/-- Polarized Green packet is genuinely Bochner integrable.  Its two metric terms are retained as
one coherent current; no invalid termwise absolute split is used. -/
theorem integrable_xiMassThetaQuantileMetricSymplecticIntegrand
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    Integrable (xiMassThetaQuantileMetricSymplecticIntegrand a c tau) := by
  have htheta := integrable_xiMassThetaQuantileResolventIntegrand
    hhalf hca htau
  have hfun : xiMassThetaQuantileMetricSymplecticIntegrand a c tau =
      fun x => (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
        xiMassThetaQuantileResolventIntegrand a c tau x := by
    funext x
    rw [xiMassThetaQuantileMetricSymplecticIntegrand_eq_I_mul_resolventIntegrand
      hhalf]
  rw [hfun]
  exact htheta.const_mul _

/-- **Integrated polarized Green weld.** -/
theorem xiMassThetaQuantileMetricSymplecticIntegral_eq_I_mul_resolventIntegral
    {a c : ℝ} (hhalf : 1 / 2 < c) (tau : ℂ) :
    xiMassThetaQuantileMetricSymplecticIntegral a c tau =
      Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
        xiMassThetaQuantileResolventIntegral a c tau := by
  rw [xiMassThetaQuantileMetricSymplecticIntegral,
    xiMassThetaQuantileResolventIntegral]
  have hfun : xiMassThetaQuantileMetricSymplecticIntegrand a c tau =
      fun x => (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
        xiMassThetaQuantileResolventIntegrand a c tau x := by
    funext x
    rw [xiMassThetaQuantileMetricSymplecticIntegrand_eq_I_mul_resolventIntegrand
      hhalf]
  rw [hfun, MeasureTheory.integral_const_mul]

/-- Recovering the phase-sensitive theta packet divides only by one fixed positive dipole charge. -/
theorem xiMassThetaQuantileResolventIntegral_eq_polarizedGreen
    {a c : ℝ} (hhalf : 1 / 2 < c) (tau : ℂ) :
    xiMassThetaQuantileResolventIntegral a c tau =
      (-Complex.I / pinnedFirstMoment thetaQuantileCoordinate) *
        xiMassThetaQuantileMetricSymplecticIntegral a c tau := by
  rw [xiMassThetaQuantileMetricSymplecticIntegral_eq_I_mul_resolventIntegral
    hhalf tau]
  field_simp [pinnedFirstMoment_thetaQuantileCoordinate_ne_zero,
    Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

/-- Height-uniform line bound for the coherent polarized Green packet. -/
def XiMassThetaQuantileMetricSymplecticIntegralLineBound
    (a c sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassThetaQuantileMetricSymplecticIntegral a c
      ((sigma : ℂ) + (u : ℂ) * Complex.I)‖ ≤ C

/-- Fixed nonzero dipole normalization makes polarized-current boundedness exactly equivalent to
the phase-sensitive resolvent packet bound. -/
theorem xiMassThetaQuantileResolventIntegralLineBound_iff_metricSymplectic
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) :
    XiMassThetaQuantileResolventIntegralLineBound a c sigma ↔
      XiMassThetaQuantileMetricSymplecticIntegralLineBound a c sigma := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖Complex.I * pinnedFirstMoment thetaQuantileCoordinate‖ * C,
      fun u hu => ?_⟩
    rw [xiMassThetaQuantileMetricSymplecticIntegral_eq_I_mul_resolventIntegral
      hhalf, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg _)
  · rintro ⟨C, hC⟩
    refine ⟨‖-Complex.I / pinnedFirstMoment thetaQuantileCoordinate‖ * C,
      fun u hu => ?_⟩
    rw [xiMassThetaQuantileResolventIntegral_eq_polarizedGreen
      hhalf, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg _)

/-- **Pure polarized-Green Route T criterion.** -/
theorem riemannHypothesis_iff_xiMassThetaQuantileMetricSymplecticIntegralLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔
      XiMassThetaQuantileMetricSymplecticIntegralLineBound a c sigma :=
  (riemannHypothesis_iff_xiMassThetaQuantileResolventIntegralLineBound
    hhalf hca hsigma).trans
      (xiMassThetaQuantileResolventIntegralLineBound_iff_metricSymplectic
        hhalf)

end

end RHTower
