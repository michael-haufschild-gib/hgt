import GaloisForLFunctions.RHTower.ThetaCuspHawkingEKGCausalMirrorOpticalLaw
import GaloisForLFunctions.RHTower.ThetaCuspHawkingSchwarzschildJostIncidenceNoGo
import GaloisForLFunctions.HTGeometry.TriangularKernelDeterminant

/-!
# Causal EKG Volterra--Evans determinant blindness

The genuine BCR Einstein--Klein--Gordon coefficient has ordered kernel

`1_{s<u} k_a(s) (k_a'(u))^2`.

Sampling retarded time on ordered shells gives a strictly upper-triangular kernel.  This file
proves two facts simultaneously:

* for every nonzero tilt the sampled EKG kernel itself is nonzero;
* its Fredholm determinants are nevertheless identically one.

Consequently a purely retarded/Volterra backreaction determinant cannot turn theta/Xi source
zeros into Evans poles.  A divisor-faithful nonlinear completion must introduce a return path:
advanced Schwinger--Keldysh coupling, horizon-memory feedback, or another lower-triangular
component.  This is the exact point where a full theta-mirror completion becomes dynamical rather
than a Cayley parametrization.

`[SCOPE]` This is an exact ordered time-shell discretization of the coefficient proved in
`ThetaCuspHawkingEKGCausalMirrorOpticalLaw`.  It is not a construction of the continuum
Schwarzschild/Teukolsky Fredholm determinant.  The theorem says every strictly causal Galerkin
kernel of this form is determinant-blind; continuum incidence still requires trace-class and
projection analysis.
-/

open Complex

noncomputable section

namespace RHTower

/-- Ordered retarded-time shell, shifted so shell `1` samples physical time zero. -/
def thetaCuspTiltedEKGCausalSampleTime (n : ℕ) : ℝ :=
  (n : ℝ) - 1

/-- Time-shell Galerkin kernel of the exact ordered EKG cubic mass density. -/
def thetaCuspTiltedEKGCausalVolterraKernel (a : ℝ) (p : ℕ × ℕ) : ℂ :=
  if p.1 < p.2 then
    ((thetaCuspTiltedSource a (thetaCuspTiltedEKGCausalSampleTime p.1) *
      thetaCuspTiltedEKGDerivativeEnergyDensity a
        (thetaCuspTiltedEKGCausalSampleTime p.2) : ℝ) : ℂ)
  else 0

/-- Causality makes every backward or diagonal matrix entry vanish. -/
theorem thetaCuspTiltedEKGCausalVolterraKernel_strictlyUpper (a : ℝ) :
    GaloisForLFunctions.HTGeometry.TriangularKernel.StrictlyUpperKernel
      (thetaCuspTiltedEKGCausalVolterraKernel a) := by
  intro i j hji
  unfold thetaCuspTiltedEKGCausalVolterraKernel
  rw [if_neg (not_lt_of_ge hji)]

/-- Tilted dynamics is not the zero kernel: shell `0 -> 1` samples nonzero derivative energy at
time zero whenever `a != 0`. -/
theorem thetaCuspTiltedEKGCausalVolterraKernel_zero_one_ne_zero
    {a : ℝ} (ha : a ≠ 0) :
    thetaCuspTiltedEKGCausalVolterraKernel a (0, 1) ≠ 0 := by
  have hderiv : deriv (thetaCuspTiltedSource a) 0 ≠ 0 := by
    rw [deriv_thetaCuspTiltedSource_zero]
    exact mul_ne_zero ha (thetaCuspFullSource_pos_all 0).ne'
  have henergy : thetaCuspTiltedEKGDerivativeEnergyDensity a 0 ≠ 0 := by
    unfold thetaCuspTiltedEKGDerivativeEnergyDensity
    exact pow_ne_zero 2 hderiv
  have hsource : thetaCuspTiltedSource a (-1) ≠ 0 :=
    (thetaCuspTiltedSource_pos a (-1)).ne'
  rw [thetaCuspTiltedEKGCausalVolterraKernel, if_pos (by norm_num)]
  norm_num [thetaCuspTiltedEKGCausalSampleTime]
  exact ⟨hsource, henergy⟩

/-- Fredholm--Evans candidate obtained from the pure retarded EKG Galerkin kernel. -/
def thetaCuspTiltedEKGCausalVolterraEvansDeterminant (a : ℝ) (z : ℂ) : ℂ :=
  HilbertSchmidt.fredholmDet1
    (thetaCuspTiltedEKGCausalVolterraKernel a) z

/-- **Volterra determinant blindness.**  Pure causal EKG ordering has determinant one at every
tilt and spectral parameter, even when its kernel is nonzero. -/
theorem thetaCuspTiltedEKGCausalVolterraEvansDeterminant_eq_one
    (a : ℝ) (z : ℂ) :
    thetaCuspTiltedEKGCausalVolterraEvansDeterminant a z = 1 := by
  unfold thetaCuspTiltedEKGCausalVolterraEvansDeterminant
  exact GaloisForLFunctions.HTGeometry.TriangularKernel.fredholmDet1_eq_one
    (thetaCuspTiltedEKGCausalVolterraKernel_strictlyUpper a) z

theorem thetaCuspTiltedEKGCausalVolterraEvansDeterminant_ne_zero
    (a : ℝ) (z : ℂ) :
    thetaCuspTiltedEKGCausalVolterraEvansDeterminant a z ≠ 0 := by
  rw [thetaCuspTiltedEKGCausalVolterraEvansDeterminant_eq_one]
  norm_num

/-- At every actual theta divisor the pure causal EKG determinant is one while the source/Jost
numerator is zero.  Hence the two objects cannot be identified. -/
theorem thetaCuspTiltedEKGCausalVolterraEvansDeterminant_ne_XiC_at_divisor
    (rho : XiDivisorSupport) :
    thetaCuspTiltedEKGCausalVolterraEvansDeterminant
        (thetaCuspHawkingPositiveJostTilt rho)
        (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)) ≠
      XiC (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)) := by
  rw [thetaCuspTiltedEKGCausalVolterraEvansDeterminant_eq_one,
    XiC_xiSpectralPointSupport_eq_zero_source]
  norm_num

/-- Positive survivor: any divisor-faithful Evans object differs from the pure causal Volterra
determinant at every theta divisor. -/
theorem thetaCuspTiltedEKG_divisorFaithfulEvans_requires_returnPath
    (E : ℝ → ℂ → ℂ)
    (hE : ∀ rho : XiDivisorSupport,
      E (thetaCuspHawkingPositiveJostTilt rho)
        (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)) = 0)
    (rho : XiDivisorSupport) :
    E (thetaCuspHawkingPositiveJostTilt rho)
        (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)) ≠
      thetaCuspTiltedEKGCausalVolterraEvansDeterminant
        (thetaCuspHawkingPositiveJostTilt rho)
        (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)) := by
  rw [hE rho, thetaCuspTiltedEKGCausalVolterraEvansDeterminant_eq_one]
  norm_num

end RHTower
