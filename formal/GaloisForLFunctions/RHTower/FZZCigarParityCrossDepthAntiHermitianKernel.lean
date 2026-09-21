import GaloisForLFunctions.RHTower.FZZCigarParityCrossDepthSymmetricKernelNoGo

/-!
# FZZ-P cross-depth anti-Hermitian source law

The literal neutral cross-depth covariance is conjugated by exchange of its two
coupling depths.  Consequently, orientation in any finite complex depth
source is neither an extra phase convention nor a property of the receiver:
it is exactly the pairing with the source kernel's exchange anti-Hermitian
part.

Proof-chain role:
`literal neutral covariance + source depth kernel -> anti-Hermitian source
current -> oriented replica--momentum Ward term -> FZZ-P source realization`.

This turns the open FZZ-P source burden into one exact question: derive a
source-fixed kernel whose anti-Hermitian current has nonzero pairing with the
literal covariance.  Real exchange-symmetric and factorized Gram kernels are
the zero-current special cases, not separate mechanisms.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Finite complex source-depth accumulation of literal neutral cross-depth covariance. -/
def fzzRadialCouplingFiniteComplexKernel
    (S : Finset ℝ) (K : ℝ → ℝ → ℂ) (v p : ℝ) : ℂ :=
  ∑ u₁ ∈ S, ∑ u₂ ∈ S,
    K u₁ u₂ * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p

/-- The source datum which survives exchange conjugation. -/
def fzzRadialCouplingDepthAntiHermitian
    (K : ℝ → ℝ → ℂ) (u₁ u₂ : ℝ) : ℂ :=
  K u₁ u₂ - star (K u₂ u₁)

/-- The anti-Hermitian source current is itself skew under depth exchange. -/
theorem star_fzzRadialCouplingDepthAntiHermitian
    (K : ℝ → ℝ → ℂ) (u₁ u₂ : ℝ) :
    star (fzzRadialCouplingDepthAntiHermitian K u₁ u₂) =
      -fzzRadialCouplingDepthAntiHermitian K u₂ u₁ := by
  unfold fzzRadialCouplingDepthAntiHermitian
  change (starRingEnd ℂ) (K u₁ u₂ - (starRingEnd ℂ) (K u₂ u₁)) = _
  rw [map_sub]
  simp only [starRingEnd_apply, star_star]
  ring

/-- Exact exchange classification: the non-real part of a finite FZZ-P depth
source is precisely its anti-Hermitian current paired with literal covariance. -/
theorem fzzRadialCouplingFiniteComplexKernel_sub_star
    (S : Finset ℝ) (K : ℝ → ℝ → ℂ) (v p : ℝ) :
    fzzRadialCouplingFiniteComplexKernel S K v p -
        star (fzzRadialCouplingFiniteComplexKernel S K v p) =
      ∑ u₁ ∈ S, ∑ u₂ ∈ S,
        fzzRadialCouplingDepthAntiHermitian K u₁ u₂ *
          fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p := by
  unfold fzzRadialCouplingFiniteComplexKernel
  change (∑ u₁ ∈ S, ∑ u₂ ∈ S,
      K u₁ u₂ * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) -
      (starRingEnd ℂ) (∑ u₁ ∈ S, ∑ u₂ ∈ S,
        K u₁ u₂ * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) = _
  have hstar : (starRingEnd ℂ) (∑ u₁ ∈ S, ∑ u₂ ∈ S,
      K u₁ u₂ * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) =
      ∑ u₁ ∈ S, ∑ u₂ ∈ S,
        (starRingEnd ℂ) (K u₂ u₁) *
          fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p := by
    simp only [map_sum, map_mul, starRingEnd_apply,
      star_fzzRadialCouplingCrossDepthCoherence]
    rw [Finset.sum_comm]
  rw [hstar]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u₁ hu₁
  apply Finset.sum_congr rfl
  intro u₂ hu₂
  unfold fzzRadialCouplingDepthAntiHermitian
  simp only [starRingEnd_apply]
  ring

/-- The Ward orientation is exactly twice the imaginary anti-Hermitian pairing. -/
theorem fzzRadialCouplingFiniteComplexKernel_twice_im
    (S : Finset ℝ) (K : ℝ → ℝ → ℂ) (v p : ℝ) :
    2 * (fzzRadialCouplingFiniteComplexKernel S K v p).im =
      (∑ u₁ ∈ S, ∑ u₂ ∈ S,
        fzzRadialCouplingDepthAntiHermitian K u₁ u₂ *
          fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p).im := by
  rw [← fzzRadialCouplingFiniteComplexKernel_sub_star]
  change 2 * (fzzRadialCouplingFiniteComplexKernel S K v p).im =
    (fzzRadialCouplingFiniteComplexKernel S K v p).im -
      -(fzzRadialCouplingFiniteComplexKernel S K v p).im
  ring

/-- Every finite Hermitian source-depth kernel is orientation-blind.  This
strictly extends the real exchange-symmetric kernel no-go to complex kernels. -/
theorem fzzRadialCouplingFiniteComplexKernel_im_eq_zero_of_depthHermitian
    (S : Finset ℝ) (K : ℝ → ℝ → ℂ) (v p : ℝ)
    (hK : ∀ u₁ u₂, K u₁ u₂ = star (K u₂ u₁)) :
    (fzzRadialCouplingFiniteComplexKernel S K v p).im = 0 := by
  have hanti (u₁ u₂ : ℝ) : fzzRadialCouplingDepthAntiHermitian K u₁ u₂ = 0 := by
    unfold fzzRadialCouplingDepthAntiHermitian
    rw [hK]
    ring
  have hsum : (∑ u₁ ∈ S, ∑ u₂ ∈ S,
      fzzRadialCouplingDepthAntiHermitian K u₁ u₂ *
        fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) = 0 := by
    apply Finset.sum_eq_zero
    intro u₁ hu₁
    apply Finset.sum_eq_zero
    intro u₂ hu₂
    rw [hanti]
    ring
  have h := fzzRadialCouplingFiniteComplexKernel_twice_im S K v p
  rw [hsum] at h
  norm_num at h
  linarith

/-- Exact FZZ-P source criterion for finite complex depth kernels. -/
theorem fzzRadialCouplingFiniteComplexKernel_im_ne_zero_iff
    (S : Finset ℝ) (K : ℝ → ℝ → ℂ) (v p : ℝ) :
    (fzzRadialCouplingFiniteComplexKernel S K v p).im ≠ 0 ↔
      (∑ u₁ ∈ S, ∑ u₂ ∈ S,
        fzzRadialCouplingDepthAntiHermitian K u₁ u₂ *
          fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p).im ≠ 0 := by
  rw [← fzzRadialCouplingFiniteComplexKernel_twice_im]
  constructor
  · intro h hzero
    apply h
    linarith
  · intro h hzero
    apply h
    rw [hzero]
    ring

end

end GaloisForLFunctions.RHTower
