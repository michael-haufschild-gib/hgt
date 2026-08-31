import GaloisForLFunctions.HTGeometry.ConstitutiveNilpotentSocleLaw
import GaloisForLFunctions.HTGeometry.ConstitutiveParitySuspensionHodge
import GaloisForLFunctions.RHTower.HedenmalmEssentialInverseFlowTrace
import GaloisForLFunctions.RHTower.HedenmalmThetaDivisorPolarizedInterpolation

/-!
# Theta-source conormal socle

Every nonzero spectral root block of the fixed compact theta source has geometric multiplicity one
and nilpotent remainder.  The constitutive kernel-growth law therefore forces one complete Jordan
chain.  Its top power is a nonzero rank-one current with range exactly the source eigenline, and
the theta determinant identifies its exponent with the actual Xi multiplicity.

Parity suspension then gives a source-native nonzero square-zero charge and a nonzero positive
self-adjoint Hodge observer.
-/

open Complex MeasureTheory Module.End
open GaloisForLFunctions.HTGeometry

namespace RHTower.HedenmalmThetaSource

noncomputable section

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Full generalized root block at a nonzero theta-source spectral point. -/
abbrev ThetaRootBlock (mu : ThetaNonzeroSpectrum) :=
  maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)

local instance (mu : ThetaNonzeroSpectrum) : CompleteSpace (ThetaRootBlock mu) :=
  FiniteDimensional.complete ℂ (ThetaRootBlock mu)

/-- Nilpotent remainder of the source operator on one complete generalized root block. -/
def thetaRootNilpotentPart (mu : ThetaNonzeroSpectrum) :
    Module.End ℂ (ThetaRootBlock mu) :=
  thetaRootBlockOperator mu - algebraMap ℂ (Module.End ℂ (ThetaRootBlock mu)) (mu : ℂ)

theorem thetaRootNilpotentPart_isNilpotent (mu : ThetaNonzeroSpectrum) :
    IsNilpotent (thetaRootNilpotentPart mu) :=
  thetaRootBlockOperator_sub_isNilpotent mu

/-- Source ODE uniqueness makes the kernel of every root-block nilpotent remainder exactly one
dimensional. -/
theorem finrank_ker_thetaRootNilpotentPart_eq_one (mu : ThetaNonzeroSpectrum) :
    Module.finrank ℂ (LinearMap.ker (thetaRootNilpotentPart mu)) = 1 := by
  have hev : HasEigenvalue (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ) :=
    (isCompactOperator_thetaKernelOperator.hasEigenvalue_iff_mem_spectrum mu.2.2).2 mu.2.1
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hvEig : thetaKernelOperator v = (mu : ℂ) • v :=
    Module.End.mem_eigenspace_iff.mp hv.1
  have hvG : v ∈ ThetaRootBlock mu :=
    Module.End.eigenspace_le_maxGenEigenspace hv.1
  let vg : ThetaRootBlock mu := ⟨v, hvG⟩
  have hvgne : vg ≠ 0 := by
    intro hzero
    apply hv.2
    exact congrArg Subtype.val hzero
  have hvgker : vg ∈ LinearMap.ker (thetaRootNilpotentPart mu) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change thetaKernelOperator v - (mu : ℂ) • v = 0
    exact sub_eq_zero.mpr hvEig
  have hkerEq : LinearMap.ker (thetaRootNilpotentPart mu) = ℂ ∙ vg := by
    apply le_antisymm
    · intro x hx
      have hxzero := LinearMap.mem_ker.mp hx
      have hxEig : thetaKernelOperator (x : ThetaH) = (mu : ℂ) • (x : ThetaH) := by
        have hval := congrArg Subtype.val hxzero
        change thetaKernelOperator (x : ThetaH) - (mu : ℂ) • (x : ThetaH) = 0 at hval
        exact sub_eq_zero.mp hval
      have hxCompact : thetaCompactSourceInverse (x : ThetaH) =
          (mu : ℂ) • (x : ThetaH) := by
        rw [← thetaKernelOperator_eq_thetaCompactSourceInverse]
        exact hxEig
      have hvCompact : thetaCompactSourceInverse v = (mu : ℂ) • v := by
        rw [← thetaKernelOperator_eq_thetaCompactSourceInverse]
        exact hvEig
      obtain ⟨a, ha⟩ := thetaCompactSourceInverse_eigenvectors_proportional
        mu.2.2 hxCompact hvCompact hv.2
      rw [Submodule.mem_span_singleton]
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact ha.symm
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvgker)
  rw [hkerEq, finrank_span_singleton]
  exact hvgne

/-- Canonical source conormal current: top nonzero power of the root-block nilpotent part. -/
def thetaSourceConormalCurrent (mu : ThetaNonzeroSpectrum) :
    Module.End ℂ (ThetaRootBlock mu) :=
  nilpotentSocleCurrent (thetaRootNilpotentPart mu)

/-- Every nonzero source spectral point carries nonzero conormal current. -/
theorem thetaSourceConormalCurrent_ne_zero (mu : ThetaNonzeroSpectrum) :
    thetaSourceConormalCurrent mu ≠ 0 :=
  nilpotentSocleCurrent_ne_zero _ (finrank_ker_thetaRootNilpotentPart_eq_one mu)

/-- Exact source reconstruction: top socle range is the uniquely reconstructible eigenline. -/
theorem range_thetaSourceConormalCurrent (mu : ThetaNonzeroSpectrum) :
    LinearMap.range (thetaSourceConormalCurrent mu) =
      LinearMap.ker (thetaRootNilpotentPart mu) :=
  range_nilpotentSocleCurrent _ (thetaRootNilpotentPart_isNilpotent mu)
    (finrank_ker_thetaRootNilpotentPart_eq_one mu)

theorem finrank_range_thetaSourceConormalCurrent (mu : ThetaNonzeroSpectrum) :
    Module.finrank ℂ (LinearMap.range (thetaSourceConormalCurrent mu)) = 1 :=
  finrank_range_nilpotentSocleCurrent _ (thetaRootNilpotentPart_isNilpotent mu)
    (finrank_ker_thetaRootNilpotentPart_eq_one mu)

/-- Xi determinant multiplicity is exactly the dimension of the corresponding source root block. -/
theorem finrank_thetaRootBlock_at_XiSupport (rho : XiDivisorSupport) :
    Module.finrank ℂ (ThetaRootBlock (thetaSpectrumOfXiSupport rho)) =
      xiSupportMultiplicity rho := by
  exact finrank_maxGenEigenspace_thetaKernelOperator_eq_xiSupportMultiplicity rho

/-- Actual Xi multiplicity is the exponent defining the source conormal current. -/
theorem thetaSourceConormalCurrent_at_XiSupport_eq_pow (rho : XiDivisorSupport) :
    thetaSourceConormalCurrent (thetaSpectrumOfXiSupport rho) =
      thetaRootNilpotentPart (thetaSpectrumOfXiSupport rho) ^
        (xiSupportMultiplicity rho - 1) := by
  unfold thetaSourceConormalCurrent nilpotentSocleCurrent
  rw [finrank_thetaRootBlock_at_XiSupport]

/-- At a simple Xi zero, source conormal current is the identity on its root line. -/
theorem thetaSourceConormalCurrent_at_simple_XiSupport_eq_one
    (rho : XiDivisorSupport) (hsimple : xiSupportMultiplicity rho = 1) :
    thetaSourceConormalCurrent (thetaSpectrumOfXiSupport rho) = 1 := by
  rw [thetaSourceConormalCurrent_at_XiSupport_eq_pow, hsimple]
  simp

/-- At a multiple Xi zero, source conormal current is nonzero and square-zero. -/
theorem thetaSourceConormalCurrent_at_multiple_XiSupport_sq_eq_zero
    (rho : XiDivisorSupport) (hmultiple : 2 ≤ xiSupportMultiplicity rho) :
    thetaSourceConormalCurrent (thetaSpectrumOfXiSupport rho) ^ 2 = 0 := by
  apply nilpotentSocleCurrent_sq_eq_zero _
    (thetaRootNilpotentPart_isNilpotent (thetaSpectrumOfXiSupport rho))
  rw [finrank_thetaRootBlock_at_XiSupport]
  exact hmultiple

/-- Bounded realization of the source conormal current on its finite-dimensional Hilbert fibre. -/
def thetaSourceConormalCurrentCLM (mu : ThetaNonzeroSpectrum) :
    ThetaRootBlock mu →L[ℂ] ThetaRootBlock mu :=
  LinearMap.toContinuousLinearMap (thetaSourceConormalCurrent mu)

theorem thetaSourceConormalCurrentCLM_ne_zero (mu : ThetaNonzeroSpectrum) :
    thetaSourceConormalCurrentCLM mu ≠ 0 := by
  intro hzero
  apply thetaSourceConormalCurrent_ne_zero mu
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun T => T x) hzero
  simpa [thetaSourceConormalCurrentCLM] using hx

abbrev ThetaSourceConormalParityDouble (mu : ThetaNonzeroSpectrum) :=
  HilbertParityDouble (E := ThetaRootBlock mu)

/-- Faithful odd square-zero suspension of the source conormal current. -/
def thetaSourceConormalParityCharge (mu : ThetaNonzeroSpectrum) :
    ThetaSourceConormalParityDouble mu →L[ℂ] ThetaSourceConormalParityDouble mu :=
  hilbertParitySuspensionCharge (thetaSourceConormalCurrentCLM mu)

theorem thetaSourceConormalParityCharge_sq (mu : ThetaNonzeroSpectrum) :
    thetaSourceConormalParityCharge mu * thetaSourceConormalParityCharge mu = 0 :=
  hilbertParitySuspensionCharge_sq (thetaSourceConormalCurrentCLM mu)

theorem thetaSourceConormalParityCharge_ne_zero (mu : ThetaNonzeroSpectrum) :
    thetaSourceConormalParityCharge mu ≠ 0 := by
  intro hzero
  exact thetaSourceConormalCurrentCLM_ne_zero mu
    ((hilbertParitySuspensionCharge_eq_zero_iff
      (thetaSourceConormalCurrentCLM mu)).mp hzero)

/-- Positive Hodge observer generated from the source conormal charge. -/
def thetaSourceConormalHodgeHamiltonian (mu : ThetaNonzeroSpectrum) :
    ThetaSourceConormalParityDouble mu →L[ℂ] ThetaSourceConormalParityDouble mu :=
  paritySuspensionHodgeHamiltonian (thetaSourceConormalCurrentCLM mu)

theorem thetaSourceConormalHodgeHamiltonian_ne_zero (mu : ThetaNonzeroSpectrum) :
    thetaSourceConormalHodgeHamiltonian mu ≠ 0 :=
  (paritySuspensionHodgeHamiltonian_ne_zero_iff
    (thetaSourceConormalCurrentCLM mu)).2
      (thetaSourceConormalCurrentCLM_ne_zero mu)

theorem thetaSourceConormalHodgeHamiltonian_isSelfAdjoint
    (mu : ThetaNonzeroSpectrum) :
    IsSelfAdjoint (thetaSourceConormalHodgeHamiltonian mu) :=
  paritySuspensionHodgeHamiltonian_isSelfAdjoint
    (thetaSourceConormalCurrentCLM mu)

theorem re_inner_thetaSourceConormalHodgeHamiltonian_nonneg
    (mu : ThetaNonzeroSpectrum) (psi : ThetaSourceConormalParityDouble mu) :
    0 ≤ Complex.re
      (inner ℂ psi (thetaSourceConormalHodgeHamiltonian mu psi)) :=
  re_inner_paritySuspensionHodgeHamiltonian_nonneg
    (thetaSourceConormalCurrentCLM mu) psi

end

end RHTower.HedenmalmThetaSource
