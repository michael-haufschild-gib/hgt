import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.ExpPolynomialDA
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence

/-!
# Exact extremal Bessel-intensity scan

This module closes the affine-reparametrization and elementary-gauge part of the fixed-argument
modified-Bessel intensity theorem.  The physical frequency scan has order coordinate

`nu(omega) = 1 + (2 * I / kappa) * omega`

and its elementary prefactor is an exponential times a nonzero quadratic polynomial.  Both
operations preserve hypertranscendence.  The result is stated as an exact transfer theorem from
the fixed-argument intensity; once the order-intensity theorem is available, no further analytic
or physical hypothesis remains.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The nonzero affine slope in the physical order coordinate. -/
def extremalBesselOrderSlope (kappa : ℝ) : ℂ :=
  2 * Complex.I / (kappa : ℂ)

/-- The quadratic part of Good's exact fixed-argument prefactor, including its constant
normalization.  Its value is

`(pi^2 kappa^2)^-1 * (1 - 4 omega^2 / (kappa^2 s^2))`.
-/
def extremalBesselIntensityPrefactorPolynomial (kappa s : ℝ) : Polynomial ℂ :=
  Polynomial.C (((Real.pi : ℂ) ^ 2 * (kappa : ℂ) ^ 2)⁻¹) *
    (1 - Polynomial.C (4 / ((kappa : ℂ) ^ 2 * (s : ℂ) ^ 2)) * Polynomial.X ^ 2)

/-- Entire continuation of the elementary physical prefactor in equation (13) of the card. -/
def extremalBesselIntensityPrefactor (kappa s : ℝ) (omega : ℂ) : ℂ :=
  Complex.exp ((-2 * (Real.pi : ℂ) / (kappa : ℂ)) * omega) *
    (extremalBesselIntensityPrefactorPolynomial kappa s).eval omega

/-- Fixed-argument Bessel intensity pulled back to the calibrated physical frequency line. -/
def extremalBesselIntensityCore (kappa s : ℝ) (omega : ℂ) : ℂ :=
  modifiedBesselOrderIntensity s (extremalBesselOrderSlope kappa * omega + 1)

/-- Exact entire continuation of the calibrated all-time extremal intensity scan. -/
def extremalBesselIntensityScan (kappa s : ℝ) (omega : ℂ) : ℂ :=
  extremalBesselIntensityPrefactor kappa s omega *
    extremalBesselIntensityCore kappa s omega

theorem extremalBesselOrderSlope_ne_zero {kappa : ℝ} (hkappa : 0 < kappa) :
    extremalBesselOrderSlope kappa ≠ 0 := by
  unfold extremalBesselOrderSlope
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  · exact_mod_cast ne_of_gt hkappa

theorem extremalBesselIntensityPrefactorPolynomial_ne_zero
    {kappa s : ℝ} (hkappa : 0 < kappa) :
    extremalBesselIntensityPrefactorPolynomial kappa s ≠ 0 := by
  intro hzero
  have hval := congrArg (Polynomial.eval 0) hzero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkappaC : (kappa : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hkappa
  have hden : (Real.pi : ℂ) ^ 2 * (kappa : ℂ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hpi) (pow_ne_zero _ hkappaC)
  have hinv : (((Real.pi : ℂ) ^ 2 * (kappa : ℂ) ^ 2)⁻¹) = 0 := by
    simpa [extremalBesselIntensityPrefactorPolynomial] using hval
  exact (inv_ne_zero hden) hinv

theorem analyticOnNhd_extremalBesselIntensityPrefactor (kappa s : ℝ) :
    AnalyticOnNhd ℂ (extremalBesselIntensityPrefactor kappa s) Set.univ := by
  have hphase : AnalyticOnNhd ℂ
      (fun omega : ℂ => (-2 * (Real.pi : ℂ) / (kappa : ℂ)) * omega) Set.univ :=
    analyticOnNhd_const.mul analyticOnNhd_id
  have hpoly : AnalyticOnNhd ℂ
      (fun omega : ℂ =>
        (extremalBesselIntensityPrefactorPolynomial kappa s).eval omega) Set.univ := by
    have h : AnalyticOnNhd ℂ
        (fun omega : ℂ =>
          (((Real.pi : ℂ) ^ 2 * (kappa : ℂ) ^ 2)⁻¹) *
            (1 - (4 / ((kappa : ℂ) ^ 2 * (s : ℂ) ^ 2)) * omega ^ 2)) Set.univ :=
      analyticOnNhd_const.mul
        (analyticOnNhd_const.sub (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2)))
    simpa [extremalBesselIntensityPrefactorPolynomial] using h
  exact hphase.cexp.mul hpoly

theorem analyticOnNhd_extremalBesselIntensityCore
    {kappa s : ℝ} (hs : 0 < s) :
    AnalyticOnNhd ℂ (extremalBesselIntensityCore kappa s) Set.univ := by
  apply (analyticOnNhd_modifiedBesselOrderIntensity hs).comp
  · exact (analyticOnNhd_const.mul analyticOnNhd_id).add analyticOnNhd_const
  · exact Set.mapsTo_univ _ _

theorem analyticOnNhd_extremalBesselIntensityScan
    {kappa s : ℝ} (hs : 0 < s) :
    AnalyticOnNhd ℂ (extremalBesselIntensityScan kappa s) Set.univ :=
  (analyticOnNhd_extremalBesselIntensityPrefactor kappa s).mul
    (analyticOnNhd_extremalBesselIntensityCore hs)

theorem differentiallyAlgebraic_extremalBesselIntensityPrefactor
    (kappa s : ℝ) :
    DifferentiallyAlgebraic (extremalBesselIntensityPrefactor kappa s) := by
  change DifferentiallyAlgebraic (fun omega =>
    Complex.exp ((-2 * (Real.pi : ℂ) / (kappa : ℂ)) * omega) *
      (extremalBesselIntensityPrefactorPolynomial kappa s).eval omega)
  exact
    differentiallyAlgebraic_cexp_mul_polynomial
      (-2 * (Real.pi : ℂ) / (kappa : ℂ))
      (extremalBesselIntensityPrefactorPolynomial kappa s)

private theorem analyticMeroElement_ne_zero_of_value
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) {z : ℂ} (hz : f z ≠ 0) :
    analyticMeroElement f hf ≠ 0 := by
  intro hzero
  have hanalytic : analyticFunctionElement f hf = 0 := by
    apply IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ)
    simpa [analyticMeroElement] using hzero
  have hgerm := congrArg Subtype.val hanalytic
  change Germ.ofFun (l := Filter.principal Set.univ) f = 0 at hgerm
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  exact hz (eventually_principal.mp hgerm z (Set.mem_univ z))

theorem extremalBesselIntensityPrefactorMero_ne_zero
    {kappa s : ℝ} (hkappa : 0 < kappa) :
    analyticMeroElement (extremalBesselIntensityPrefactor kappa s)
      (analyticOnNhd_extremalBesselIntensityPrefactor kappa s) ≠ 0 := by
  apply analyticMeroElement_ne_zero_of_value
    (analyticOnNhd_extremalBesselIntensityPrefactor kappa s) (z := 0)
  simp only [extremalBesselIntensityPrefactor, mul_zero, Complex.exp_zero,
    one_mul]
  have hpoly := extremalBesselIntensityPrefactorPolynomial_ne_zero
    (s := s) hkappa
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkappaC : (kappa : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hkappa
  simp [extremalBesselIntensityPrefactorPolynomial, hpi, hkappaC]

/-- The global analytic-jet bridge upgrades multiplication by a nonzero entire DA factor to an
exact hypertranscendence equivalence. -/
theorem hypertranscendental_mul_entire_differentiallyAlgebraic
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hgDA : DifferentiallyAlgebraic g)
    (hg0 : analyticMeroElement g hg ≠ 0)
    (hfHT : Hypertranscendental f) :
    Hypertranscendental (fun z => g z * f z) := by
  let fM : meroField Set.univ := analyticMeroElement f hf
  let gM : meroField Set.univ := analyticMeroElement g hg
  have hfMHT : HypertranscendentalOver (RatFunc ℂ) fM := by
    intro hfMDA
    exact hfHT
      (differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement hf
        (by simpa [fM] using hfMDA))
  have hgMDA : DifferentialAlgebraicOver (RatFunc ℂ) gM :=
    differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hg hgDA
  have hprodMHT : HypertranscendentalOver (RatFunc ℂ) (fM * gM) :=
    (hypertranscendentalOver_mul_differentialAlgebraic_iff hgMDA
      (by simpa [gM] using hg0)).2 hfMHT
  intro hprodDA
  have hprodMDA :=
    differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
      (hg.mul hf) hprodDA
  rw [analyticMeroElement_mul hg hf] at hprodMDA
  exact hprodMHT (by simpa [fM, gM, mul_comm] using hprodMDA)

theorem hypertranscendental_extremalBesselIntensityCore_of_intensity
    {kappa s : ℝ} (hkappa : 0 < kappa)
    (hI : Hypertranscendental (modifiedBesselOrderIntensity s)) :
    Hypertranscendental (extremalBesselIntensityCore kappa s) := by
  have htranslated : Hypertranscendental
      (fun z => modifiedBesselOrderIntensity s (z + 1)) :=
    (hypertranscendental_comp_add_const_iff (f := modifiedBesselOrderIntensity s) 1).2 hI
  have hscaled :=
    (hypertranscendental_comp_const_mul_iff_uncond
      (f := fun z => modifiedBesselOrderIntensity s (z + 1))
      (extremalBesselOrderSlope_ne_zero hkappa)).2 htranslated
  change Hypertranscendental
    (fun z => modifiedBesselOrderIntensity s (extremalBesselOrderSlope kappa * z + 1))
  exact hscaled

/-- **Exact physical scan transfer.**  Positive physical scales and fixed-argument Bessel
intensity hypertranscendence force hypertranscendence of Good's calibrated extremal scan. -/
theorem hypertranscendental_extremalBesselIntensityScan_of_intensity
    {kappa s : ℝ} (hkappa : 0 < kappa) (hs : 0 < s)
    (hI : Hypertranscendental (modifiedBesselOrderIntensity s)) :
    Hypertranscendental (extremalBesselIntensityScan kappa s) := by
  have hcore := hypertranscendental_extremalBesselIntensityCore_of_intensity hkappa hI
  change Hypertranscendental (fun z =>
    extremalBesselIntensityPrefactor kappa s z * extremalBesselIntensityCore kappa s z)
  exact
    hypertranscendental_mul_entire_differentiallyAlgebraic
      (analyticOnNhd_extremalBesselIntensityCore hs)
      (analyticOnNhd_extremalBesselIntensityPrefactor kappa s)
      (differentiallyAlgebraic_extremalBesselIntensityPrefactor kappa s)
      (extremalBesselIntensityPrefactorMero_ne_zero hkappa)
      hcore

/-- On the physical domain `omega != 0`, the simplified entire prefactor is exactly the quotient
appearing in Good's coefficient. -/
theorem extremalBesselIntensityPrefactor_eq_good
    {kappa s : ℝ} (hkappa : 0 < kappa) (hs : 0 < s)
    {omega : ℂ} (homega : omega ≠ 0) :
    extremalBesselIntensityPrefactor kappa s omega =
      Complex.exp ((-2 * (Real.pi : ℂ) / (kappa : ℂ)) * omega) *
        (((kappa : ℂ) ^ 2 * (s : ℂ) ^ 2 / (4 * omega) - omega) /
          ((Real.pi : ℂ) ^ 2 * (kappa : ℂ) ^ 2 *
            ((kappa : ℂ) ^ 2 * (s : ℂ) ^ 2 / (4 * omega)))) := by
  have hkappaC : (kappa : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hkappa
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  unfold extremalBesselIntensityPrefactor
  simp only [extremalBesselIntensityPrefactorPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X]
  congr 1
  field_simp [hkappaC, hsC, homega]

end

end GaloisForLFunctions.HTGeometry
