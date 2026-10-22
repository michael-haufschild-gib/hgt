import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaRoutePAllPrimeInformationVirialDivergence
import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinDeterminantTransgression

/-!
# Route P information action from signed Gamma Bockstein

The valuation-one geometric-KL virial is not merely analogous to Route R's signed Gamma
Bockstein.  Its radial derivative is exactly a positive gauge times grade multiplied by the
literal signed determinant transgression, and the KL term is its interval action integral.

For positive grade the Bockstein itself is negative, while the canonical radial action density is
strictly positive.  Thus passing from signed pre-polar determinant data to information geometry
removes rather than creates cancellation.  This identifies the exact precursor of P-G58's
all-prime divergence and closes determinant-action cancellation as a producer.
-/

open Real Set Filter Topology MeasureTheory
open scoped Interval

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- At doubled grade, signed Gamma Bockstein is Fisher weight times negative hyperbolic sine. -/
theorem primeGammaCofinalBocksteinCoefficient_two_mul_eq_sinh
    (p : Nat.Primes) (t : ℝ) :
    RHTower.primeGammaCofinalBocksteinCoefficient (2 * t) p =
      -2 * RHTower.primeActivationOccupancyFisherDensity p *
        Real.sinh (2 * Real.log (p : ℝ) * t) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [RHTower.primeGammaCofinalBocksteinCoefficient,
    RHTower.primeActivationOccupancyFisherTwist,
    RHTower.primeActivationOccupancyFisherTwist,
    Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0,
    Real.sinh_eq]
  rw [show Real.log (p : ℝ) * -(2 * t) =
      -(2 * Real.log (p : ℝ) * t) by ring,
    show Real.log (p : ℝ) * (2 * t) =
      2 * Real.log (p : ℝ) * t by ring]
  ring

/-- Radial action density of signed determinant transgression. -/
def sourceHorizontalPrimeBocksteinActionDensity
    (p : Nat.Primes) (t : ℝ) : ℝ :=
  -8 * (((p : ℝ) + 1) ^ 2 / (p : ℝ) ^ 2) *
    Real.log (p : ℝ) ^ 2 * t *
      RHTower.primeGammaCofinalBocksteinCoefficient (2 * t) p

/-- Closed hyperbolic form of Bockstein action density. -/
theorem sourceHorizontalPrimeBocksteinActionDensity_eq
    (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeBocksteinActionDensity p t =
      16 * (p : ℝ)⁻¹ * Real.log (p : ℝ) ^ 2 * t *
        Real.sinh (2 * Real.log (p : ℝ) * t) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  rw [sourceHorizontalPrimeBocksteinActionDensity,
    primeGammaCofinalBocksteinCoefficient_two_mul_eq_sinh,
    RHTower.primeActivationOccupancyFisherDensity_eq]
  field_simp [hpne]
  ring

/-- Information virial derivative is exactly radial Gamma-Bockstein action density. -/
theorem hasDerivAt_sourceHorizontalPrimeGeometricKLScaleTerm_zero_eq_bocksteinAction
    (p : Nat.Primes) (t : ℝ) :
    HasDerivAt (sourceHorizontalPrimeGeometricKLScaleTerm p 0)
      (sourceHorizontalPrimeBocksteinActionDensity p t) t := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have h := hasDerivAt_sourceHorizontalPrimeGeometricKLScaleTerm p 0 t
  apply h.congr_deriv
  rw [sourceHorizontalPrimeBocksteinActionDensity_eq]
  norm_num
  rw [Real.exp_neg, Real.exp_log hp0]
  ring

/-- **P-G59 action identity.**  Valuation-one geometric KL virial is accumulated signed
Gamma-Bockstein determinant transgression along radial grade. -/
theorem intervalIntegral_sourceHorizontalPrimeBocksteinActionDensity
    (p : Nat.Primes) (t : ℝ) :
    (∫ r in (0 : ℝ)..t, sourceHorizontalPrimeBocksteinActionDensity p r) =
      sourceHorizontalPrimeGeometricKLScaleTerm p 0 t := by
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) t,
      HasDerivAt (sourceHorizontalPrimeGeometricKLScaleTerm p 0)
        (sourceHorizontalPrimeBocksteinActionDensity p r) r :=
    fun r _ =>
      hasDerivAt_sourceHorizontalPrimeGeometricKLScaleTerm_zero_eq_bocksteinAction p r
  have hcont : Continuous (sourceHorizontalPrimeBocksteinActionDensity p) := by
    have hfun : sourceHorizontalPrimeBocksteinActionDensity p = fun r : ℝ =>
        16 * (p : ℝ)⁻¹ * Real.log (p : ℝ) ^ 2 * r *
          Real.sinh (2 * Real.log (p : ℝ) * r) := by
      funext r
      exact sourceHorizontalPrimeBocksteinActionDensity_eq p r
    rw [hfun]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 t)]
  have hzero : sourceHorizontalPrimeGeometricKLScaleTerm p 0 0 = 0 := by
    rw [sourceHorizontalPrimeGeometricKLScaleTerm_zero_eq]
    simp [sourceHorizontalHolonomyVirial]
  rw [hzero, sub_zero]

/-- Positive radial grades make canonical action density strictly positive even though signed
Bockstein coefficient is strictly negative. -/
theorem sourceHorizontalPrimeBocksteinActionDensity_pos
    (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    0 < sourceHorizontalPrimeBocksteinActionDensity p t := by
  rw [sourceHorizontalPrimeBocksteinActionDensity_eq]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hu : 0 < 2 * Real.log (p : ℝ) * t := by positivity
  have hsinh : 0 < Real.sinh (2 * Real.log (p : ℝ) * t) :=
    Real.sinh_pos_iff.mpr hu
  positivity

end

end RHTower.HedenmalmThetaSource
