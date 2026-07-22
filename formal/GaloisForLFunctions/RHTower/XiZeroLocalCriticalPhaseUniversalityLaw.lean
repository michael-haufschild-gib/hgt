import GaloisForLFunctions.RHTower.GammaMertensOrbitCoboundaryRH
import GaloisForLFunctions.RHTower.PrimeClockScaleFactor
import GaloisForLFunctions.RHTower.PrimePowerCenteredMarkRH
import GaloisForLFunctions.RHTower.PrimeGammaStokesCoxeterRH
import GaloisForLFunctions.RHTower.WeightOneCliffordDirac

/-!
# Xi-zero local critical-phase universality

Critical-line placement of one actual Xi zero has the same realization in Born, prime-clock,
prime-mark, Arakelov, finite-unitary, quadratic-Clifford, and Gamma--Mertens coboundary charts.
The theorem is pointwise and does not turn zero-indexed obligations into vacuous global RH
predicates.
-/

open Complex
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- At an actual Xi zero, reality of the Berry--Keating coordinate is exactly critical-line
placement.  The extra real-axis branch of quadratic reality is excluded by the real zero-free
theorem inside the open critical strip. -/
theorem berryKeatingU_im_eq_zero_iff_re_eq_half_of_xiZero
    {rho : ℂ} (hzero : xi rho = 0) :
    (berryKeatingU rho).im = 0 ↔ rho.re = 1 / 2 := by
  constructor
  · intro him
    by_contra hoff
    apply (berryKeatingU_nonreal_of_offCritical_nonzero_im rho hoff ?_) him
    intro hrhoIm
    have hstrip := xi_zero_re_mem_open_unit hzero
    have hrho : rho = (rho.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa only [Complex.ofReal_im] using hrhoIm
    have hzeroReal : xi (rho.re : ℂ) = 0 := by
      rw [← hrho]
      exact hzero
    exact (xi_ne_zero_real_anchor hstrip.1 hstrip.2) hzeroReal
  · intro hhalf
    exact (berryKeatingU_on_critical rho hhalf).1

/-- The real affine Clifford transform has the same faithful pointwise reality locus at an Xi
zero as the Berry--Keating coordinate. -/
theorem weightOneCliffordEnergy_im_eq_zero_iff_re_eq_half_of_xiZero
    (a : ℝ) {rho : ℂ} (hzero : xi rho = 0) :
    (weightOneCliffordEnergy a rho).im = 0 ↔ rho.re = 1 / 2 := by
  rw [weightOneCliffordEnergy_eq_berryKeatingU]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_eq_zero]
  exact berryKeatingU_im_eq_zero_iff_re_eq_half_of_xiZero hzero

/-- For one actual Xi zero, the reflected Mertens pole pair is a finite Gamma shift-two
coboundary exactly on the critical line. -/
theorem exists_gammaMertensShiftTwoCoboundary_iff_re_eq_half_of_xiZero
    {rho : ℂ} (hzero : xi rho = 0) :
    (∃ E : ℂ →₀ (ℕ →₀ ℂ),
      simplePolePairDifferentialOperator (1 : Polynomial ℂ) 1
          (-rho) (starRingEnd ℂ rho - 1) =
        finiteOrbitCoboundary (2 : ℂ) E) ↔ rho.re = 1 / 2 := by
  constructor
  · rintro ⟨E, hE⟩
    exact mertensPolePair_re_eq_half_of_finiteShiftTwoCoboundary
      (xi_zero_re_mem_open_unit hzero) (L := (1 : Polynomial ℂ)) one_ne_zero E hE
  · intro hhalf
    refine ⟨0, ?_⟩
    have hsupports : -rho = starRingEnd ℂ rho - 1 := by
      apply Complex.ext
      · simp only [neg_re, Complex.conj_re, sub_re, one_re]
        linarith
      · simp only [neg_im, Complex.conj_im, sub_im, one_im]
        ring
    rw [← hsupports]
    simp [simplePolePairDifferentialOperator, finiteOrbitCoboundary,
      translateFiniteSupport]

/-- Eleven simultaneous local realizations of critical placement for one actual Xi zero. -/
structure XiZeroLocalCriticalPhaseUniversalCertificate
    (rho : ℂ) (p : ℕ) (a : ℝ) : Prop where
  bornTemperatureCritical : bornBeta rho = 1
  reflectedPhaseMatch : ReflectedPhaseMatch (bornBeta rho)
  reflectionFixed : 1 - starRingEnd ℂ rho = rho
  reflectedPrimeClockShale : Summable (primeClockReflectionEnergy rho.re)
  perspectiveNeutralExternalClock : PerspectiveNeutralExternalClock rho.re
  centeredPrimeMarkUnit : ‖centeredPrimeMark p rho‖ = 1
  arakelovCoordinateUnit : ‖arakelovW rho‖ = 1
  finiteUnitaryArakelovEigenpacket :
    Nonempty (FiniteUnitaryEigenDatum (arakelovW rho))
  quadraticEnergyReal : (berryKeatingU rho).im = 0
  weightOneCliffordEnergyReal : (weightOneCliffordEnergy a rho).im = 0
  gammaMertensShiftTwoCoboundary :
    ∃ E : ℂ →₀ (ℕ →₀ ℂ),
      simplePolePairDifferentialOperator (1 : Polynomial ℂ) 1
          (-rho) (starRingEnd ℂ rho - 1) =
        finiteOrbitCoboundary (2 : ℂ) E

/-- **Xi-zero local critical-phase universality law.**  At any actual Xi zero and any prime-mark
base `p > 1`, critical placement is exactly the common eleven-chart phase. -/
theorem xiZero_re_eq_half_iff_localCriticalPhaseUniversalCertificate
    {rho : ℂ} (hzero : xi rho = 0) {p : ℕ} (hp : 1 < p) (a : ℝ) :
    rho.re = 1 / 2 ↔ XiZeroLocalCriticalPhaseUniversalCertificate rho p a := by
  have hrho0 : rho ≠ 0 := by
    intro hrho
    subst rho
    have hstrip := xi_zero_re_mem_open_unit hzero
    norm_num at hstrip
  constructor
  · intro hhalf
    have harakelov : ‖arakelovW rho‖ = 1 :=
      (arakelovW_norm_one_iff_critical rho hrho0).2 hhalf
    exact {
      bornTemperatureCritical := by unfold bornBeta; linarith
      reflectedPhaseMatch := (reflectedPhaseMatch_iff (bornBeta rho)).2 (by
        unfold bornBeta
        linarith)
      reflectionFixed := (fe_reflection_fixed_iff rho).2 hhalf
      reflectedPrimeClockShale :=
        (summable_primeClockReflectionEnergy_iff rho.re).2 hhalf
      perspectiveNeutralExternalClock :=
        (perspectiveNeutralExternalClock_iff rho.re).2 hhalf
      centeredPrimeMarkUnit := (centeredPrimeMark_norm_eq_one_iff hp rho).2 hhalf
      arakelovCoordinateUnit := harakelov
      finiteUnitaryArakelovEigenpacket :=
        (finiteUnitaryEigenDatum_iff_norm_eq_one (arakelovW rho)).2 harakelov
      quadraticEnergyReal :=
        (berryKeatingU_im_eq_zero_iff_re_eq_half_of_xiZero hzero).2 hhalf
      weightOneCliffordEnergyReal :=
        (weightOneCliffordEnergy_im_eq_zero_iff_re_eq_half_of_xiZero a hzero).2 hhalf
      gammaMertensShiftTwoCoboundary :=
        (exists_gammaMertensShiftTwoCoboundary_iff_re_eq_half_of_xiZero hzero).2 hhalf }
  · intro hcertificate
    exact (summable_primeClockReflectionEnergy_iff rho.re).1
      hcertificate.reflectedPrimeClockShale

/-- The synchronized failure of all eleven local critical-line realizations. -/
structure XiZeroLocalCriticalPhaseFailureUniversalCertificate
    (rho : ℂ) (p : ℕ) (a : ℝ) : Prop where
  bornTemperatureNoncritical : bornBeta rho ≠ 1
  reflectedPhaseMismatch : ¬ ReflectedPhaseMatch (bornBeta rho)
  reflectionNotFixed : 1 - starRingEnd ℂ rho ≠ rho
  reflectedPrimeClockNotShale : ¬ Summable (primeClockReflectionEnergy rho.re)
  perspectiveClockNotNeutral : ¬ PerspectiveNeutralExternalClock rho.re
  centeredPrimeMarkNotUnit : ‖centeredPrimeMark p rho‖ ≠ 1
  arakelovCoordinateNotUnit : ‖arakelovW rho‖ ≠ 1
  noFiniteUnitaryArakelovEigenpacket :
    ¬ Nonempty (FiniteUnitaryEigenDatum (arakelovW rho))
  quadraticEnergyNonreal : (berryKeatingU rho).im ≠ 0
  weightOneCliffordEnergyNonreal : (weightOneCliffordEnergy a rho).im ≠ 0
  noGammaMertensShiftTwoCoboundary :
    ¬ ∃ E : ℂ →₀ (ℕ →₀ ℂ),
      simplePolePairDifferentialOperator (1 : Polynomial ℂ) 1
          (-rho) (starRingEnd ℂ rho - 1) =
        finiteOrbitCoboundary (2 : ℂ) E

/-- **Synchronized local failure law.**  An actual Xi zero is off the critical line exactly when
all eleven faithful local realizations fail. -/
theorem xiZero_re_ne_half_iff_localCriticalPhaseFailureUniversalCertificate
    {rho : ℂ} (hzero : xi rho = 0) {p : ℕ} (hp : 1 < p) (a : ℝ) :
    rho.re ≠ 1 / 2 ↔ XiZeroLocalCriticalPhaseFailureUniversalCertificate rho p a := by
  have hrho0 : rho ≠ 0 := by
    intro hrho
    subst rho
    have hstrip := xi_zero_re_mem_open_unit hzero
    norm_num at hstrip
  constructor
  · intro hoff
    exact {
      bornTemperatureNoncritical := fun hbeta => hoff (by
        unfold bornBeta at hbeta
        linarith)
      reflectedPhaseMismatch := fun hphase => hoff (by
        have hbeta := (reflectedPhaseMatch_iff (bornBeta rho)).1 hphase
        unfold bornBeta at hbeta
        linarith)
      reflectionNotFixed := fun hfixed => hoff ((fe_reflection_fixed_iff rho).1 hfixed)
      reflectedPrimeClockNotShale := fun hclock => hoff
        ((summable_primeClockReflectionEnergy_iff rho.re).1 hclock)
      perspectiveClockNotNeutral := fun hclock => hoff
        ((perspectiveNeutralExternalClock_iff rho.re).1 hclock)
      centeredPrimeMarkNotUnit := fun hmark => hoff
        ((centeredPrimeMark_norm_eq_one_iff hp rho).1 hmark)
      arakelovCoordinateNotUnit := fun harakelov => hoff
        ((arakelovW_norm_one_iff_critical rho hrho0).1 harakelov)
      noFiniteUnitaryArakelovEigenpacket := fun hpacket => hoff
        ((arakelovW_norm_one_iff_critical rho hrho0).1
          ((finiteUnitaryEigenDatum_iff_norm_eq_one (arakelovW rho)).1 hpacket))
      quadraticEnergyNonreal := fun hreal => hoff
        ((berryKeatingU_im_eq_zero_iff_re_eq_half_of_xiZero hzero).1 hreal)
      weightOneCliffordEnergyNonreal := fun hreal => hoff
        ((weightOneCliffordEnergy_im_eq_zero_iff_re_eq_half_of_xiZero a hzero).1 hreal)
      noGammaMertensShiftTwoCoboundary := fun hcoboundary => hoff
        ((exists_gammaMertensShiftTwoCoboundary_iff_re_eq_half_of_xiZero hzero).1
          hcoboundary) }
  · intro hfailure hhalf
    exact hfailure.reflectedPrimeClockNotShale
      ((summable_primeClockReflectionEnergy_iff rho.re).2 hhalf)

/-- At an actual Xi zero, the synchronized negative phase is exactly the complement of the
positive eleven-chart phase. -/
theorem not_localCriticalPhaseUniversalCertificate_iff_failure
    {rho : ℂ} (hzero : xi rho = 0) {p : ℕ} (hp : 1 < p) (a : ℝ) :
    ¬ XiZeroLocalCriticalPhaseUniversalCertificate rho p a ↔
      XiZeroLocalCriticalPhaseFailureUniversalCertificate rho p a := by
  constructor
  · intro hnotCertificate
    apply (xiZero_re_ne_half_iff_localCriticalPhaseFailureUniversalCertificate
      hzero hp a).1
    intro hhalf
    exact hnotCertificate
      ((xiZero_re_eq_half_iff_localCriticalPhaseUniversalCertificate hzero hp a).1 hhalf)
  · intro hfailure hcertificate
    have hoff :=
      (xiZero_re_ne_half_iff_localCriticalPhaseFailureUniversalCertificate hzero hp a).2
        hfailure
    exact hoff
      ((xiZero_re_eq_half_iff_localCriticalPhaseUniversalCertificate hzero hp a).2
        hcertificate)

end

end RHTower
