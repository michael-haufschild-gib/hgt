import GaloisForLFunctions.HTGeometry.UniversalObservationDescentLaw
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianLineWronskianGreenComparison

/-!
# Gaussian projective descent on the Riemann divisor

The reflected Gaussian and its logarithmic moment form a two-component
source field on actual Xi divisor copies.  This file identifies their
Wronskian with the universal involutive projective wedge and classifies
descent of their logarithmic jet through the maximal line-reflection orbit
observation.

No Riemann-hypothesis assumption is used.
-/

open GaloisForLFunctions.HTGeometry
open scoped Real

namespace RHTower

noncomputable section

namespace DeningerMeyerGaussianGreen

/-- The line-conjugation equivalence is an involution on divisor copies. -/
theorem xiZeroCopyLineConj_involutive :
    Function.Involutive xiZeroCopyLineConjEquiv := by
  intro q
  exact xiZeroCopyLineConjEquiv_apply_apply q

/-- The concrete Gaussian Wronskian is definitionally the universal
involutive projective wedge. -/
theorem deningerMeyerReflectedGaussianLineWronskian_eq_projectiveWedge
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q =
      involutiveProjectiveWedge xiZeroCopyLineConjEquiv
        deningerMeyerReflectedGaussianMellinZeroJet
        deningerMeyerReflectedGaussianMellinFirstJet q := by
  rfl

/-- Equality of reflected logarithmic source jets is exactly the
critical-line equation. -/
theorem deningerMeyerReflectedGaussian_logJet_descends_iff
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianMellinFirstJet q /
          deningerMeyerReflectedGaussianMellinZeroJet q =
        deningerMeyerReflectedGaussianMellinFirstJet
            (xiZeroCopyLineConjEquiv q) /
          deningerMeyerReflectedGaussianMellinZeroJet
            (xiZeroCopyLineConjEquiv q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  calc
    _ ↔ involutiveProjectiveWedge xiZeroCopyLineConjEquiv
          deningerMeyerReflectedGaussianMellinZeroJet
          deningerMeyerReflectedGaussianMellinFirstJet q = 0 :=
      (involutiveProjectiveWedge_eq_zero_iff_logJet_descends
        xiZeroCopyLineConjEquiv q
        (deningerMeyerReflectedGaussianMellinZeroJet_ne_zero q)
        (deningerMeyerReflectedGaussianMellinZeroJet_ne_zero
          (xiZeroCopyLineConjEquiv q))).symm
    _ ↔ deningerMeyerReflectedGaussianLineWronskian q = 0 := by
      rw [deningerMeyerReflectedGaussianLineWronskian_eq_projectiveWedge]
    _ ↔ (q.1 : ℂ).re = 1 / 2 :=
      deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff q

/-- Source logarithmic jet of the reflected Gaussian pair. -/
def deningerMeyerReflectedGaussianLogJet (q : XiZeroCopy) : ℂ :=
  deningerMeyerReflectedGaussianMellinFirstJet q /
    deningerMeyerReflectedGaussianMellinZeroJet q

/-- The Gaussian logarithmic jet is the normalized centered divisor
coordinate. -/
theorem deningerMeyerReflectedGaussianLogJet_eq (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLogJet q =
      ((q.1 : ℂ) - 1 / 2) / (2 * π) := by
  rw [deningerMeyerReflectedGaussianLogJet,
    deningerMeyerReflectedGaussianMellinFirstJet_eq_centered_mul_zeroJet]
  rw [mul_div_cancel_right₀ _
    (deningerMeyerReflectedGaussianMellinZeroJet_ne_zero q)]

/-- **Riemann realization of the universal descent defect.**  The
coequalizer differential of the fixed source logarithmic jet is exactly the
real horizontal displacement, normalized by `π`. -/
theorem deningerMeyerReflectedGaussianLogJet_descentDefect_eq
    (q : XiZeroCopy) :
    involutiveDescentDefect xiZeroCopyLineConjEquiv
        deningerMeyerReflectedGaussianLogJet q =
      ((((q.1 : ℂ).re - 1 / 2) / Real.pi : ℝ) : ℂ) := by
  rw [involutiveDescentDefect,
    deningerMeyerReflectedGaussianLogJet_eq,
    deningerMeyerReflectedGaussianLogJet_eq]
  have hline : ((xiZeroCopyLineConjEquiv q).1 : ℂ) =
      1 - starRingEnd ℂ (q.1 : ℂ) := rfl
  rw [hline]
  have hpiC : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hpiC]
  apply Complex.ext <;> simp <;> ring

/-- The universal source descent defect vanishes at one divisor copy exactly
on the critical line. -/
theorem deningerMeyerReflectedGaussianLogJet_descentDefect_eq_zero_iff
    (q : XiZeroCopy) :
    involutiveDescentDefect xiZeroCopyLineConjEquiv
        deningerMeyerReflectedGaussianLogJet q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerMeyerReflectedGaussianLogJet_descentDefect_eq]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.zero_re] at hr
    exact sub_eq_zero.mp
      ((div_eq_zero_iff.mp hr).resolve_right Real.pi_ne_zero)
  · intro h
    simp [h]

/-- The exterior Wronskian is precisely the endpoint Gaussian gauge times
the universal source descent defect. -/
theorem deningerMeyerReflectedGaussianLineWronskian_eq_gauge_mul_descentDefect
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q =
      (deningerMeyerReflectedGaussianMellinZeroJet q *
        deningerMeyerReflectedGaussianMellinZeroJet
          (xiZeroCopyLineConjEquiv q)) *
      involutiveDescentDefect xiZeroCopyLineConjEquiv
        deningerMeyerReflectedGaussianLogJet q := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_projectiveWedge]
  change involutiveProjectiveWedge xiZeroCopyLineConjEquiv
      deningerMeyerReflectedGaussianMellinZeroJet
      deningerMeyerReflectedGaussianMellinFirstJet q =
    (deningerMeyerReflectedGaussianMellinZeroJet q *
      deningerMeyerReflectedGaussianMellinZeroJet
        (xiZeroCopyLineConjEquiv q)) *
      involutiveDescentDefect xiZeroCopyLineConjEquiv
        (fun p => deningerMeyerReflectedGaussianMellinFirstJet p /
          deningerMeyerReflectedGaussianMellinZeroJet p) q
  exact involutiveProjectiveWedge_eq_gauge_mul_descentDefect_logJet
    xiZeroCopyLineConjEquiv q
    (deningerMeyerReflectedGaussianMellinZeroJet_ne_zero q)
    (deningerMeyerReflectedGaussianMellinZeroJet_ne_zero
      (xiZeroCopyLineConjEquiv q))

/-- **Complete reflected-orbit descent classification.**  The logarithmic
jet of the two fixed Gaussian sources factors through the finest
line-reflection-invariant observation exactly when RH holds. -/
theorem gaussianLogJet_factorsThrough_lineConjOrbit_iff_riemannHypothesis :
    FactorsThrough
        (involutionOrbitObservation xiZeroCopyLineConjEquiv
          xiZeroCopyLineConj_involutive)
        (fun q : XiZeroCopy =>
          deningerMeyerReflectedGaussianMellinFirstJet q /
            deningerMeyerReflectedGaussianMellinZeroJet q) ↔
      RiemannHypothesis := by
  rw [logJet_factorsThrough_involutionOrbit_iff
    xiZeroCopyLineConjEquiv xiZeroCopyLineConj_involutive
    deningerMeyerReflectedGaussianMellinZeroJet_ne_zero]
  change (∀ q : XiZeroCopy,
    deningerMeyerReflectedGaussianLineWronskian q = 0) ↔ RiemannHypothesis
  exact deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis

/-- Any source observation which identifies line-reflected copies and
already carries the Gaussian logarithmic jet proves RH.  The theorem makes
the missing arithmetic factorization explicit; it does not assume one. -/
theorem riemannHypothesis_of_gaussianLogJet_invariant_factorization
    {Q : Type*} (pi : XiZeroCopy -> Q)
    (hpi : InvariantUnder xiZeroCopyLineConjEquiv pi)
    (hfactor : FactorsThrough pi (fun q : XiZeroCopy =>
      deningerMeyerReflectedGaussianMellinFirstJet q /
        deningerMeyerReflectedGaussianMellinZeroJet q)) :
    RiemannHypothesis := by
  rw [← deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis]
  intro q
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_projectiveWedge]
  exact involutiveProjectiveWedge_eq_zero_of_logJet_factorsThrough
    xiZeroCopyLineConjEquiv pi
    deningerMeyerReflectedGaussianMellinZeroJet_ne_zero hpi hfactor q

/-- **Capacity-independent Riemann descent criterion.**  An arbitrary
heterogeneous family of source observations may be infinite and may use
unrelated codomains.  If every channel identifies line-reflected divisor
copies and their full record recovers the Gaussian logarithmic jet on its
attained range, then RH follows.  Thus merely adding further invariant
sources cannot evade the horizontal observation obligation. -/
theorem riemannHypothesis_of_gaussianLogJet_invariantObservationFamily
    {J : Type*} {Y : J -> Type*}
    (obs : forall j, XiZeroCopy -> Y j)
    (hobs : forall j,
      InvariantUnder xiZeroCopyLineConjEquiv (obs j))
    (hfactor : FactorsThroughRange (observationRecord obs)
      deningerMeyerReflectedGaussianLogJet) :
    RiemannHypothesis := by
  have hrefine :
      KernelRefines (observationRecord obs)
        deningerMeyerReflectedGaussianLogJet :=
    (factorsThroughRange_iff_kernelRefines
      (observationRecord obs)
      deningerMeyerReflectedGaussianLogJet).1 hfactor
  rw [← deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis]
  intro q
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff]
  apply (deningerMeyerReflectedGaussian_logJet_descends_iff q).1
  exact hrefine q (xiZeroCopyLineConjEquiv q)
    (invariantUnder_observationRecord
      xiZeroCopyLineConjEquiv obs hobs q).symm

end DeningerMeyerGaussianGreen

end

end RHTower
