import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaCharacteristicEntire

/-!
# Exact covariance source of Suzuki's finite characteristics

Suzuki's deficiency vectors were previously available only as Riesz representatives in the
moving energy Hilbert space `H(T_a)`.  This file identifies their literal interval densities.
For the canonical coercive metric, the physical density representing evaluation against
`exp(eps x)` is exactly

`C_a exp(eps x)`,

where `C_a` is the compact positive covariance of the completed prime--polar--Gamma restricted
Weil form.  Equivalently it is the unique solution of

`(A_a + (‖B_a‖ + 1)) v = exp(eps x)`.

Thus convergence of Suzuki's actual finite characteristics is not an abstract normal-family
selection problem: it is convergence of Fourier coordinates of these two explicit arithmetic
resolvent sources at `eps = ±1`.  All identities below are unconditional and division-free.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform LinearPMap
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- In closed-form coordinates, Suzuki's Riesz deficiency vector is the inverse shifted-form
Riesz operator applied to the physical exponential source. -/
theorem suzukiTaToFormCLM_rawDeficiency_eq_rieszInv
    (a : SuzukiPositiveAperture) (eps : ℝ) :
    suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps) =
      boundedPerturbedFormRieszInv
        (suzukiWeilIntervalFormEmbedding a)
        (suzukiWeilIntervalBoundedRemainder a)
        (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
        ((suzukiWeilIntervalFormEmbedding a).adjoint
          (suzukiTaExponentialL2 a eps)) := by
  let J := suzukiWeilIntervalFormEmbedding a
  let B := suzukiWeilIntervalBoundedRemainder a
  let hB := suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a
  let R := boundedPerturbedFormRiesz J B
  let Rinv := boundedPerturbedFormRieszInv J B hB
  apply (boundedPerturbedFormRieszEquiv J B hB).injective
  change R (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)) =
    R (Rinv (J.adjoint (suzukiTaExponentialL2 a eps)))
  have hinv : R (Rinv (J.adjoint (suzukiTaExponentialL2 a eps))) =
      J.adjoint (suzukiTaExponentialL2 a eps) := by
    exact (boundedPerturbedFormRieszEquiv J B hB).apply_symm_apply _
  rw [hinv]
  apply ext_inner_right ℂ
  intro v
  calc
    inner ℂ (R (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps))) v =
        inner ℂ (suzukiTaRawDeficiency a eps) (suzukiTaFromFormCLM a v) := by
          rw [inner_suzukiTa_eq]
          simp only [suzukiWeilIntervalForm, suzukiTaToFormCLM_fromForm,
            suzukiTaPhysicalEmbedding, ContinuousLinearMap.comp_apply]
          rw [boundedPerturbedFormRiesz_apply, inner_add_left, inner_add_left,
            inner_smul_left, J.adjoint_inner_left, J.adjoint_inner_left]
          simp only [J, B, Complex.conj_ofReal]
    _ = suzukiTaMoment a eps (suzukiTaFromFormCLM a v) :=
      suzukiTaRawDeficiency_inner a eps _
    _ = inner ℂ (suzukiTaExponentialL2 a eps) (J v) := by
      rfl
    _ = inner ℂ (J.adjoint (suzukiTaExponentialL2 a eps)) v := by
      rw [J.adjoint_inner_left]

/-- **Exact arithmetic source identity.**  The literal interval density of the finite Suzuki
deficiency vector is the completed restricted-Weil covariance applied to `exp(eps x)`. -/
theorem suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance
    (a : SuzukiPositiveAperture) (eps : ℝ) :
    suzukiTaPhysicalEmbedding a (suzukiTaRawDeficiency a eps) =
      suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a eps) := by
  rw [suzukiTaPhysicalEmbedding, suzukiWeilIntervalCovariance,
    boundedPerturbedFormCovariance, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    suzukiTaToFormCLM_rawDeficiency_eq_rieszInv]
  rfl

/-- The covariance source regarded as an actual vector in the represented interval operator's
domain. -/
def suzukiTaCovarianceDeficiencyDomain
    (a : SuzukiPositiveAperture) (eps : ℝ) :
    (suzukiWeilFriedrichsOperator a).domain :=
  ⟨suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a eps), by
    change suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a eps) ∈
      (closedDenseInverse (suzukiWeilIntervalCovariance a)).domain
    exact (closedDenseInverse_apply_C (suzukiWeilIntervalCovariance a)
      (suzukiWeilIntervalCovariance_injective a)
      (suzukiTaExponentialL2 a eps)).1⟩

/-- **Exact shifted source equation.**  Suzuki's physical deficiency density solves the
canonical resolvent equation for the actual finite completed Weil operator. -/
theorem suzukiTaCovarianceDeficiency_shiftEquation
    (a : SuzukiPositiveAperture) (eps : ℝ) :
    suzukiWeilFriedrichsOperator a
        (suzukiTaCovarianceDeficiencyDomain a eps) +
      (boundedPerturbedFormShift
          (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a eps) =
      suzukiTaExponentialL2 a eps := by
  change boundedPerturbedFriedrichsOperator
      (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
      (suzukiTaCovarianceDeficiencyDomain a eps) + _ = _
  rw [boundedPerturbedFriedrichsOperator_apply]
  change closedDenseInverse (suzukiWeilIntervalCovariance a)
        ⟨suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a eps), _⟩ -
      (boundedPerturbedFormShift
          (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a eps) +
      (boundedPerturbedFormShift
          (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a eps) = _
  rw [(closedDenseInverse_apply_C (suzukiWeilIntervalCovariance a)
    (suzukiWeilIntervalCovariance_injective a)
    (suzukiTaExponentialL2 a eps)).2]
  module

/-- Fourier-coordinate form of the source identity.  This is the exact finite object whose
cofinal behavior controls Suzuki's projective characteristic. -/
theorem suzukiTaPhysicalFourier_rawDeficiency_eq_covariance
    (a : SuzukiPositiveAperture) (eps : ℝ) (z : ℂ) :
    suzukiTaPhysicalFourier a (suzukiTaRawDeficiency a eps) z =
      suzukiCompactL2Fourier a.1
        (suzukiApertureZeroExtendL2
          (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a eps))) z := by
  rw [suzukiTaPhysicalFourier,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance]

end RHTower
