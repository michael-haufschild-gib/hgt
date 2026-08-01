import Mathlib.Analysis.Distribution.Support
import GaloisForLFunctions.HTGeometry.ClockPrincipalSymbolCalibration

/-!
# Distribution kernel of the two-clock inverse residual

The two-mass local operator theorem identifies the inverse-response difference as a genuine
zeroth-order multiplication operator. This file constructs its classical distribution-kernel
fiber as the corresponding scalar multiple of a Dirac delta. It proves the exact action on every
test function and proves that its distributional support is contained in the diagonal point,
with equality whenever mass difference and endpoint gains are nonzero.

This is the precise distribution-theoretic content of “no off-diagonal support, no derivative of
delta, and no memory tail.” No distribution or support statement is postulated as an axiom.
-/

open Set TopologicalSpace
open scoped Distributions

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens E} {n : ℕ∞}

/-- Scalar multiplication cannot enlarge distributional support. -/
theorem dsupport_smul_distribution_subset (c : ℝ) (T : 𝓓'^{n}(Ω, ℝ)) :
    Distribution.dsupport (c • T) ⊆ Distribution.dsupport T := by
  apply Distribution.dsupport_subset_dsupport
  intro s _ hT u hu
  simp [hT u hu]

/-- Nonzero scalar multiplication preserves distributional support exactly. -/
theorem dsupport_smul_distribution_eq (c : ℝ) (hc : c ≠ 0) (T : 𝓓'^{n}(Ω, ℝ)) :
    Distribution.dsupport (c • T) = Distribution.dsupport T := by
  apply Set.Subset.antisymm
  · exact dsupport_smul_distribution_subset c T
  · have hT : T = c⁻¹ • (c • T) := by
      ext u
      simp [hc]
    have hsupp : Distribution.dsupport T =
        Distribution.dsupport (c⁻¹ • (c • T)) :=
      congrArg (fun S : 𝓓'^{n}(Ω, ℝ) ↦ Distribution.dsupport S) hT
    rw [hsupp]
    exact dsupport_smul_distribution_subset c⁻¹ (c • T)

/-- Distributional kernel fiber of an order-zero locality residual. -/
def clockLocalityKernel (calibration : E → ℝ) (x : E) : 𝓓'^{n}(Ω, ℝ) :=
  calibration x • Distribution.delta x

@[simp]
theorem clockLocalityKernel_apply (calibration : E → ℝ) (x : E)
    (f : 𝓓^{n}(Ω, ℝ)) :
    clockLocalityKernel calibration x f = calibration x * f x := by
  simp [clockLocalityKernel, Distribution.delta_apply]

/-- Every order-zero locality-kernel fiber is supported at its diagonal point. -/
theorem dsupport_clockLocalityKernel_subset [FiniteDimensional ℝ E]
    (calibration : E → ℝ) (x : E) (hx : x ∈ Ω) :
    Distribution.dsupport (clockLocalityKernel (Ω := Ω) (n := n) calibration x) ⊆ {x} := by
  calc
    Distribution.dsupport (clockLocalityKernel (Ω := Ω) (n := n) calibration x) ⊆
        Distribution.dsupport (Distribution.delta x : 𝓓'^{n}(Ω, ℝ)) := by
      exact dsupport_smul_distribution_subset _ _
    _ = {x} := Distribution.dsupport_delta x hx

/-- A nonzero order-zero locality-kernel fiber has support exactly at its diagonal point. -/
theorem dsupport_clockLocalityKernel_eq [FiniteDimensional ℝ E]
    (calibration : E → ℝ) (x : E) (hx : x ∈ Ω)
    (hcalibration : calibration x ≠ 0) :
    Distribution.dsupport (clockLocalityKernel (Ω := Ω) (n := n) calibration x) = {x} := by
  rw [clockLocalityKernel,
    dsupport_smul_distribution_eq (calibration x) hcalibration,
    Distribution.dsupport_delta x hx]

section TwoMass

variable {ι : Type*}

/-- Pointwise zeroth-order coefficient isolated by two mass channels. -/
def twoMassClockLocalityCoefficient
    (sourceGainInv : E → ℝ) (receiverGainInv : E → ScalarTwoJet ι ℝ)
    (μ₁ μ₂ : ℝ) (x : E) : ℝ :=
  (μ₁ - μ₂) * (sourceGainInv x * (receiverGainInv x).value)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Pointwise local operator difference has exactly the distribution-kernel coefficient. -/
theorem measuredClockInverseOperator_difference_eq_twoMassClockLocalityCoefficient
    [Fintype ι]
    (P : E → ScalarSecondOrderOperator ι ℝ)
    (sourceGainInv : E → ℝ) (receiverGainInv : E → ScalarTwoJet ι ℝ)
    (μ₁ μ₂ : ℝ) (x : E) :
    ScalarSecondOrderOperator.sub
        (ScalarSecondOrderOperator.measuredClockInverseOperator
          (P x) (sourceGainInv x) (receiverGainInv x) μ₁)
        (ScalarSecondOrderOperator.measuredClockInverseOperator
          (P x) (sourceGainInv x) (receiverGainInv x) μ₂) =
      ScalarSecondOrderOperator.zerothOrder
        (twoMassClockLocalityCoefficient sourceGainInv receiverGainInv μ₁ μ₂ x) := by
  exact ScalarSecondOrderOperator.measuredClockInverseOperator_difference
    (P x) (sourceGainInv x) (receiverGainInv x) μ₁ μ₂

/-- Honest distribution-kernel fiber of the two-mass inverse residual. -/
def twoMassClockLocalityKernel
    (sourceGainInv : E → ℝ) (receiverGainInv : E → ScalarTwoJet ι ℝ)
    (μ₁ μ₂ : ℝ) (x : E) : 𝓓'^{n}(Ω, ℝ) :=
  clockLocalityKernel
    (twoMassClockLocalityCoefficient sourceGainInv receiverGainInv μ₁ μ₂) x

@[simp]
theorem twoMassClockLocalityKernel_apply
    (sourceGainInv : E → ℝ) (receiverGainInv : E → ScalarTwoJet ι ℝ)
    (μ₁ μ₂ : ℝ) (x : E) (f : 𝓓^{n}(Ω, ℝ)) :
    twoMassClockLocalityKernel sourceGainInv receiverGainInv μ₁ μ₂ x f =
      twoMassClockLocalityCoefficient sourceGainInv receiverGainInv μ₁ μ₂ x * f x := by
  simp [twoMassClockLocalityKernel]

/-- Two-mass residual kernels have no off-diagonal support. -/
theorem dsupport_twoMassClockLocalityKernel_subset [FiniteDimensional ℝ E]
    (sourceGainInv : E → ℝ) (receiverGainInv : E → ScalarTwoJet ι ℝ)
    (μ₁ μ₂ : ℝ) (x : E) (hx : x ∈ Ω) :
    Distribution.dsupport
        (twoMassClockLocalityKernel (Ω := Ω) (n := n)
          sourceGainInv receiverGainInv μ₁ μ₂ x) ⊆ {x} := by
  exact dsupport_clockLocalityKernel_subset _ x hx

/-- With distinct masses and invertible gains, support is exactly the diagonal point. -/
theorem dsupport_twoMassClockLocalityKernel_eq [FiniteDimensional ℝ E]
    (sourceGainInv : E → ℝ) (receiverGainInv : E → ScalarTwoJet ι ℝ)
    {μ₁ μ₂ : ℝ} (hmass : μ₁ ≠ μ₂) (x : E) (hx : x ∈ Ω)
    (hsource : sourceGainInv x ≠ 0) (hreceiver : (receiverGainInv x).value ≠ 0) :
    Distribution.dsupport
        (twoMassClockLocalityKernel (Ω := Ω) (n := n)
          sourceGainInv receiverGainInv μ₁ μ₂ x) = {x} := by
  apply dsupport_clockLocalityKernel_eq _ x hx
  exact mul_ne_zero (sub_ne_zero.mpr hmass) (mul_ne_zero hsource hreceiver)

end TwoMass

end


end GaloisForLFunctions.HTGeometry
