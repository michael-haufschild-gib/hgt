import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtCompactOpen
import GaloisForLFunctions.HTGeometry.FiniteRankDeterminantCompletion
import GaloisForLFunctions.HTGeometry.FiniteRankTracePrescriptionInfinite
import GaloisForLFunctions.HTGeometry.BoundedDomainDivisorTransfer
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceDeterminantIdentity
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaIndexInfinite

/-!
# Signed source-operator completion of the theta determinant

The fixed theta source kernel already carries the normalized Xi divisor through its canonical
Hilbert--Carleman determinant.  A fixed trace-class ordinary determinant cannot carry this
genus-one divisor.  The correct ordinary Fredholm realization is therefore cofinal: truncate the
source kernel, then alter the kernel itself by a finite diagonal block whose signed trace cancels
the truncation trace exactly.  The correction has Hilbert--Schmidt cost tending to zero.

Every finite stage is an honest ordinary matrix determinant of the corrected source operator; no
zero-free scalar gauge is applied to its determinant.  Compact-open convergence then transports
the complete normalized-Xi divisor, with multiplicity, through every bounded aperture having a
zero-free frontier.
-/

open Filter Metric Set

namespace RHTower.HedenmalmThetaSource

open HilbertSchmidt GaloisForLFunctions.HTGeometry

noncomputable section

/-- Required properties of the `k`-th signed finite source correction. -/
def ThetaSourceSignedApproximationProperty (k : ℕ)
    (SK : Finset thetaIndex × (thetaIndex × thetaIndex → ℂ)) : Prop :=
  (∀ p : thetaIndex × thetaIndex, p ∉ SK.1 ×ˢ SK.1 → SK.2 p = 0) ∧
    IsHS SK.2 ∧
    hsNorm (SK.2 - (-thetaKernelMatrix)) < 1 / ((k : ℝ) + 1) ∧
    hsTraceDiag SK.2 = 0

/-- `k`-th corrected finite source operator.  Choice is only among objects produced by the explicit
trace-spreading construction in `FiniteRankTracePrescription`: source truncation plus a diagonal
block cancelling its trace. -/
noncomputable def thetaSourceSignedApproximation (k : ℕ) :
    {SK : Finset thetaIndex × (thetaIndex × thetaIndex → ℂ) //
      ThetaSourceSignedApproximationProperty k SK} :=
  Classical.choice <| by
    obtain ⟨s, K, hsupp, hHS, hnorm, htrace⟩ :=
      exists_finiteSupport_hsNorm_sub_lt_and_hsTraceDiag_eq_of_infinite
        isHS_neg_thetaKernelMatrix (0 : ℂ)
        (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
    exact ⟨⟨s, K⟩, hsupp, hHS, hnorm, htrace⟩

/-- Matrix aperture of the `k`-th corrected source operator. -/
noncomputable def thetaSourceSignedCutoff (k : ℕ) : Finset thetaIndex :=
  (thetaSourceSignedApproximation k).1.1

/-- Kernel of the `k`-th corrected source operator. -/
noncomputable def thetaSourceSignedKernel (k : ℕ) : thetaIndex × thetaIndex → ℂ :=
  (thetaSourceSignedApproximation k).1.2

theorem thetaSourceSignedKernel_spec (k : ℕ) :
    (∀ p : thetaIndex × thetaIndex,
      p ∉ (thetaSourceSignedCutoff k) ×ˢ (thetaSourceSignedCutoff k) →
        thetaSourceSignedKernel k p = 0) ∧
    IsHS (thetaSourceSignedKernel k) ∧
    hsNorm (thetaSourceSignedKernel k - (-thetaKernelMatrix)) < 1 / ((k : ℝ) + 1) ∧
    hsTraceDiag (thetaSourceSignedKernel k) = 0 := by
  exact (thetaSourceSignedApproximation k).2

theorem thetaSourceSignedKernel_support (k : ℕ) (p : thetaIndex × thetaIndex)
    (hp : p ∉ (thetaSourceSignedCutoff k) ×ˢ (thetaSourceSignedCutoff k)) :
    thetaSourceSignedKernel k p = 0 :=
  (thetaSourceSignedKernel_spec k).1 p hp

theorem isHS_thetaSourceSignedKernel (k : ℕ) : IsHS (thetaSourceSignedKernel k) :=
  (thetaSourceSignedKernel_spec k).2.1

/-- Exact signed cancellation is imposed on the operator, before taking its determinant. -/
theorem hsTraceDiag_thetaSourceSignedKernel (k : ℕ) :
    hsTraceDiag (thetaSourceSignedKernel k) = 0 :=
  (thetaSourceSignedKernel_spec k).2.2.2

theorem hsNorm_thetaSourceSignedKernel_sub_lt (k : ℕ) :
    hsNorm (thetaSourceSignedKernel k - (-thetaKernelMatrix)) < 1 / ((k : ℝ) + 1) :=
  (thetaSourceSignedKernel_spec k).2.2.1

/-- Honest ordinary Fredholm determinant of the corrected finite source operator. -/
noncomputable def thetaSourceSignedOrdinaryDet (k : ℕ) (z : ℂ) : ℂ :=
  ((1 : Matrix ↥(thetaSourceSignedCutoff k) ↥(thetaSourceSignedCutoff k) ℂ) -
    z • blockMatrix (thetaSourceSignedKernel k)
      (thetaSourceSignedCutoff k)).det

/-- Trace-zero correction makes the honest determinant equal the regularized determinant of the
modified kernel.  This is an operator correction, not a determinant gauge. -/
theorem thetaSourceSignedOrdinaryDet_eq_entireDet2 (k : ℕ) (z : ℂ) :
    thetaSourceSignedOrdinaryDet k z = entireDet2 (thetaSourceSignedKernel k) z := by
  rw [thetaSourceSignedOrdinaryDet,
    det_one_sub_smul_blockMatrix (isHS_thetaSourceSignedKernel k)
      (thetaSourceSignedKernel_support k) z,
    hsTraceDiag_thetaSourceSignedKernel]
  simp [completedDet2]

theorem differentiable_thetaSourceSignedOrdinaryDet (k : ℕ) :
    Differentiable ℂ (thetaSourceSignedOrdinaryDet k) := by
  rw [show thetaSourceSignedOrdinaryDet k = entireDet2 (thetaSourceSignedKernel k) by
    funext z
    exact thetaSourceSignedOrdinaryDet_eq_entireDet2 k z]
  exact differentiable_entireDet2 (isHS_thetaSourceSignedKernel k)

/-- Corrected finite source operators converge in Hilbert--Schmidt topology to the fixed
divisor-bearing theta source operator. -/
theorem thetaSourceSignedKernel_tendsto_source :
    Tendsto (fun k => hsNorm (thetaSourceSignedKernel k - (-thetaKernelMatrix)))
      atTop (nhds 0) := by
  exact squeeze_zero (fun k => hsNorm_nonneg _)
    (fun k => (hsNorm_thetaSourceSignedKernel_sub_lt k).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Signed source-operator Xi completion.**  Honest ordinary determinants of trace-zero,
finite-rank modifications of the source operator converge compact-open to normalized Xi. -/
theorem thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC :
    TendstoLocallyUniformly thetaSourceSignedOrdinaryDet
      (fun z => XiC z / XiC 0) atTop := by
  have hdet := tendstoLocallyUniformly_entireDet2_of_hsNorm_sub_tendsto_zero
    thetaSourceSignedKernel (-thetaKernelMatrix)
    isHS_thetaSourceSignedKernel isHS_neg_thetaKernelMatrix
    thetaSourceSignedKernel_tendsto_source
  rw [show thetaSourceSignedOrdinaryDet =
      (fun k z => entireDet2 (thetaSourceSignedKernel k) z) by
    funext k z
    exact thetaSourceSignedOrdinaryDet_eq_entireDet2 k z]
  rw [show (fun z => XiC z / XiC 0) = thetaSourceEntireDet2 by
    funext z
    exact (thetaSourceEntireDet2_eq_XiC_normalized z).symm]
  exact hdet

/-- Closed construction certificate: finite support, exact signed trace cancellation, source
operator convergence, and compact-open convergence of honest determinants to normalized Xi. -/
theorem thetaSourceSignedZeroMovingCorrection :
    (∀ k p, p ∉ (thetaSourceSignedCutoff k) ×ˢ (thetaSourceSignedCutoff k) →
      thetaSourceSignedKernel k p = 0) ∧
    (∀ k, IsHS (thetaSourceSignedKernel k)) ∧
    (∀ k, hsTraceDiag (thetaSourceSignedKernel k) = 0) ∧
    (∀ k z, thetaSourceSignedOrdinaryDet k z = entireDet2 (thetaSourceSignedKernel k) z) ∧
    Tendsto (fun k => hsNorm (thetaSourceSignedKernel k - (-thetaKernelMatrix)))
      atTop (nhds 0) ∧
    TendstoLocallyUniformly thetaSourceSignedOrdinaryDet
      (fun z => XiC z / XiC 0) atTop := by
  exact ⟨thetaSourceSignedKernel_support, isHS_thetaSourceSignedKernel,
    hsTraceDiag_thetaSourceSignedKernel, thetaSourceSignedOrdinaryDet_eq_entireDet2,
    thetaSourceSignedKernel_tendsto_source,
    thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC⟩

/-- Exact bounded-aperture divisor transport.  Once aperture frontier avoids Xi's divisor, every
sufficiently advanced corrected ordinary determinant has exactly same total zero multiplicity
inside aperture as normalized Xi, and no extra zeros there. -/
theorem thetaSourceSignedOrdinaryDet_eventually_divisor_XiC :
    ∀ Ω : Set ℂ, IsOpen Ω → Bornology.IsBounded Ω →
      (∀ z ∈ frontier Ω, XiC z ≠ 0) →
      ∃ A : Finset ℂ,
        (∀ z ∈ Ω, XiC z = 0 ↔ z ∈ A) ∧
        ∀ᶠ k : ℕ in atTop, ∃ Z : Finset ℂ,
          (∀ z ∈ Ω, thetaSourceSignedOrdinaryDet k z = 0 ↔ z ∈ Z) ∧
          (∑ z ∈ Z, zeroMult (thetaSourceSignedOrdinaryDet k) z) =
            ∑ a ∈ A, zeroMult (fun w => XiC w / XiC 0) a := by
  intro Ω hΩopen hΩbounded hfrontier
  have hnormzero : (fun z => XiC z / XiC 0) 0 ≠ 0 := by
    simp [XiC_zero_ne]
  have hfrontier' : ∀ z ∈ frontier Ω, XiC z / XiC 0 ≠ 0 := by
    intro z hz
    exact div_ne_zero (hfrontier z hz) XiC_zero_ne
  obtain ⟨A, hA, htransfer⟩ :=
    eventually_exists_zeroSet_boundedOpen_of_tendstoLocallyUniformly
      differentiable_thetaSourceSignedOrdinaryDet
      (XiC_differentiable.div_const (XiC 0))
      thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC
      hnormzero hΩopen hΩbounded hfrontier'
  refine ⟨A, ?_, htransfer⟩
  intro z hz
  simpa [XiC_zero_ne] using hA z hz

end

end RHTower.HedenmalmThetaSource
