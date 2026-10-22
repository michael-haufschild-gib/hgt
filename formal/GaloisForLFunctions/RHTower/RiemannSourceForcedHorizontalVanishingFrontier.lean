import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittGaussianHorizontalNormalization
import GaloisForLFunctions.RHTower.RiemannGammaCoPoissonHodgeGreenDescentLaw

/-!
# Source-forced horizontal vanishing frontier

This file closes the comparison gaps between four unconditional constructions of the signed
horizontal Xi-divisor orientation:

* reflected prime-tail entropy from the arithmetic source;
* the unsquared reflected-Gaussian line Wronskian;
* the polarized Gamma/co-Poisson Calderón--Witt boundary defect;
* the real part of the multiplicity-weighted centered Xi outer charge.

The source entropy determines the real Gamma/co-Poisson deformation parameter exactly.  The
Gamma/co-Poisson boundary defect is faithful in that parameter, while the Gaussian Wronskian is
that same parameter times a nowhere-zero positive Hermitian scale.  Thus no arbitrary observation,
factorization, bounded operator, positivity assumption, or normalization choice remains in the
reduction.  The only unproved global statement is vanishing of the constructed source-driven
boundary defect on every Xi-divisor fibre; this statement is equivalent to RH.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open DeningerMeyerGaussianGreen

/-- Source-derived real deformation parameter before Gamma/co-Poisson boundary descent. -/
def riemannSourceGammaCoPoissonHorizontalParameter
    (rho : XiDivisorSupport) : ℝ :=
  -riemannReflectedSourceEntropy (rho : ℂ)

/-- Prime-tail source orientation and Green horizontal fracture are the same signed scalar. -/
theorem riemannSourceGammaCoPoissonHorizontalParameter_eq_greenFracture_re
    (rho : XiDivisorSupport) :
    riemannSourceGammaCoPoissonHorizontalParameter rho =
      (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)).re := by
  rw [riemannSourceGammaCoPoissonHorizontalParameter,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp only [sourceCayleyTransverseRate, sub_re, one_re, ofReal_re]
  ring

/-- Existing polarized Gamma/co-Poisson boundary defect driven by canonical source data. -/
def riemannSourceGammaCoPoissonHorizontalDefect
    (rho : XiDivisorSupport) :=
  deningerCalderonWittGammaPolarizedBoundaryReflectionDefect
    (riemannSourceGammaCoPoissonHorizontalParameter rho)

/-- Source driving agrees literally with the previously constructed Green-boundary driving. -/
theorem riemannSourceGammaCoPoissonHorizontalDefect_eq_greenBoundaryDefect
    (rho : XiDivisorSupport) :
    riemannSourceGammaCoPoissonHorizontalDefect rho =
      deningerCalderonWittGammaPolarizedBoundaryReflectionDefect
        (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)).re := by
  rw [riemannSourceGammaCoPoissonHorizontalDefect,
    riemannSourceGammaCoPoissonHorizontalParameter_eq_greenFracture_re]

/-- The constructed Gamma/co-Poisson boundary map loses no source parameter. -/
theorem riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff_parameter_eq_zero
    (rho : XiDivisorSupport) :
    riemannSourceGammaCoPoissonHorizontalDefect rho = 0 ↔
      riemannSourceGammaCoPoissonHorizontalParameter rho = 0 := by
  rw [riemannSourceGammaCoPoissonHorizontalDefect,
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq_zero_iff]

/-- Local source-driven Gamma/co-Poisson vanishing is exactly critical-line placement. -/
theorem riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff
    (rho : XiDivisorSupport) :
    riemannSourceGammaCoPoissonHorizontalDefect rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [riemannSourceGammaCoPoissonHorizontalDefect_eq_greenBoundaryDefect,
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_boundaryFracture_eq_zero_iff]

/-- The source parameter vanishes exactly when the underlying reflected source entropy does. -/
theorem riemannSourceGammaCoPoissonHorizontalParameter_eq_zero_iff_entropy_eq_zero
    (rho : XiDivisorSupport) :
    riemannSourceGammaCoPoissonHorizontalParameter rho = 0 ↔
      riemannReflectedSourceEntropy (rho : ℂ) = 0 := by
  simp [riemannSourceGammaCoPoissonHorizontalParameter]

/-- The unsquared Gaussian reporter is the source parameter times a nowhere-zero positive scale. -/
theorem deningerMeyerReflectedGaussianLineWronskian_eq_sourceParameter_mul
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q =
      ((riemannSourceGammaCoPoissonHorizontalParameter q.1 : ℝ) : ℂ) *
        deningerMeyerReflectedGaussianLinePairScale q := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul,
    riemannSourceGammaCoPoissonHorizontalParameter_eq_greenFracture_re,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp

/-- Multiplicity-weighted Xi outer orientation is the same source parameter with exact scale. -/
theorem centeredXiDivisorCharge_real_eq_sourceParameter
    (rho : XiDivisorSupport) :
    (-(((rho : ℂ) - 1 / 2) *
        ((analyticOrderAt xi (rho : ℂ)).toNat : ℂ))).re =
      -((analyticOrderAt xi (rho : ℂ)).toNat : ℝ) / 2 *
        riemannSourceGammaCoPoissonHorizontalParameter rho := by
  rw [centeredDivisorCharge_real_eq_neg_half_sourceCayleyRate,
    riemannSourceGammaCoPoissonHorizontalParameter,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  ring

/-- Single remaining global proposition after all source/reporter comparisons. -/
def XiSourceForcedHorizontalVanishing : Prop :=
  ∀ rho : XiDivisorSupport,
    riemannSourceGammaCoPoissonHorizontalDefect rho = 0

/-- The remaining boundary statement is exactly vanishing of canonical prime-tail entropy. -/
theorem xiSourceForcedHorizontalVanishing_iff_reflectedSourceEntropy_vanishes :
    XiSourceForcedHorizontalVanishing ↔
      ∀ rho : XiDivisorSupport,
        riemannReflectedSourceEntropy (rho : ℂ) = 0 := by
  apply forall_congr'
  intro rho
  rw [riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff_parameter_eq_zero,
    riemannSourceGammaCoPoissonHorizontalParameter_eq_zero_iff_entropy_eq_zero]

/-- The source-driven formulation is literally the constructed Gamma/co-Poisson descent law. -/
theorem xiSourceForcedHorizontalVanishing_iff_gammaCoPoissonHodgeGreenBoundaryDescends :
    XiSourceForcedHorizontalVanishing ↔
      XiGammaCoPoissonHodgeGreenBoundaryDescends := by
  apply forall_congr'
  intro rho
  rw [riemannSourceGammaCoPoissonHorizontalDefect_eq_greenBoundaryDefect]

/-- The only remaining global vanishing is exactly vanishing of the unsquared Gaussian reporter. -/
theorem xiSourceForcedHorizontalVanishing_iff_gaussianLineWronskian :
    XiSourceForcedHorizontalVanishing ↔
      ∀ q : XiZeroCopy,
        deningerMeyerReflectedGaussianLineWronskian q = 0 := by
  constructor
  · intro h q
    exact (deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff q).2
      ((riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff q.1).1
        (h q.1))
  · intro h rho
    let q : XiZeroCopy :=
      ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
    apply (riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff rho).2
    exact (deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff q).1
      (h q)

/-- Exact formal frontier: source-forced horizontal vanishing is equivalent to RH. -/
theorem xiSourceForcedHorizontalVanishing_iff_riemannHypothesis :
    XiSourceForcedHorizontalVanishing ↔ RiemannHypothesis := by
  rw [xiSourceForcedHorizontalVanishing_iff_gammaCoPoissonHodgeGreenBoundaryDescends,
    xiGammaCoPoissonHodgeGreenBoundaryDescends_iff_riemannHypothesis]

/-- Once source-forced vanishing is proved, no further mathematical premise is needed for RH. -/
theorem riemannHypothesis_of_sourceForcedHorizontalVanishing
    (h : XiSourceForcedHorizontalVanishing) :
    RiemannHypothesis :=
  xiSourceForcedHorizontalVanishing_iff_riemannHypothesis.mp h

end

end RHTower
