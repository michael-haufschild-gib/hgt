import GaloisForLFunctions.HTGeometry.SimplePairedQuasiEllipticCollapse
import GaloisForLFunctions.HTGeometry.EllipticGammaTranslationCosetRankLaw

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] ellipticGammaTranslationCosetRankLawDomain
  ellipticGammaTranslationCosetRankLawComplexAlgebraAnalytic
  ellipticGammaTranslationCosetRankLawComplexAlgebraMero
  ellipticGammaTranslationCosetRankLawComplexDifferential
  ellipticGammaTranslationCosetRankLawMeroDifferential
  ellipticGammaTranslationCosetRankLawMeroCharZero
  ellipticGammaTranslationCosetRankLawEllipticDifferential
  ellipticGammaTranslationCosetRankLawEllipticDifferentialAlgebra
  ellipticGammaTranslationCosetRankLawCoordinateDifferential
  ellipticGammaTranslationCosetRankLawCoordinateDifferentialAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The defect family of a simple paired quasi-elliptic primitive is the elliptic-gamma external
defect family.** -/
theorem defectFamily_eq_ellipticGammaExternalDefectFamily
    {κ : Type*} (hfam : κ → ℂ)
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    {F : meroField (Set.univ : Set ℂ)} {uσ uτ : ℂ → ℂ}
    (hFone : addTranslationMeroEquiv 1 F = F)
    (hUσ : RealizesMero (addTranslationMeroEquiv σ F - F) uσ)
    (hσan : ∀ z ∉ thetaDivisor τ, AnalyticAt ℂ uσ z)
    (hσp : ∀ q ∈ thetaDivisor τ, HasPrincipalPart uσ q 1)
    (hσper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + 1) = uσ w)
    {kσ : ℂ} (hσinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + τ) = uσ w + kσ)
    (hUτ : RealizesMero (addTranslationMeroEquiv τ F - F) uτ)
    (hτan : ∀ z ∉ shiftedThetaDivisor σ ((τ - σ) / 2), AnalyticAt ℂ uτ z)
    (hτp : ∀ q ∈ shiftedThetaDivisor σ ((τ - σ) / 2), HasPrincipalPart uτ q 1)
    (hτper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + 1) = uτ w)
    {kτ : ℂ} (hτinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + σ) = uτ w + kτ) :
    (fun j => addTranslationMeroEquiv (hfam j) F - F)
      = ellipticGammaExternalDefectFamily hfam σ τ hσ hτ := by
  funext j
  exact defect_eq_ellipticGammaExternalLogDerivDefectMero hσ hτ hv hFone hUσ hσan hσp hσper
    hσinc hUτ hτan hτp hτper hτinc (hfam j)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The exact translation-coset matroid of a simple paired quasi-elliptic primitive.**  Its
translation defects represent the pointed collision matroid of rank-three period classes: the zero
class is the loop class and every nonzero class is one parallel class. -/
theorem pairedQuasiEllipticPrimitive_differentialMatroid
    {κ : Type*} (hfam : κ → ℂ)
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods σ τ))
    {F : meroField (Set.univ : Set ℂ)} {uσ uτ : ℂ → ℂ}
    (hFone : addTranslationMeroEquiv 1 F = F)
    (hUσ : RealizesMero (addTranslationMeroEquiv σ F - F) uσ)
    (hσan : ∀ z ∉ thetaDivisor τ, AnalyticAt ℂ uσ z)
    (hσp : ∀ q ∈ thetaDivisor τ, HasPrincipalPart uσ q 1)
    (hσper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + 1) = uσ w)
    {kσ : ℂ} (hσinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + τ) = uσ w + kσ)
    (hUτ : RealizesMero (addTranslationMeroEquiv τ F - F) uτ)
    (hτan : ∀ z ∉ shiftedThetaDivisor σ ((τ - σ) / 2), AnalyticAt ℂ uτ z)
    (hτp : ∀ q ∈ shiftedThetaDivisor σ ((τ - σ) / 2), HasPrincipalPart uτ q 1)
    (hτper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + 1) = uτ w)
    {kτ : ℂ} (hτinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + σ) = uτ w + kτ) :
    differentialFamilyMatroid (F := meromorphicEllipticCompositum σ τ)
        (fun j => addTranslationMeroEquiv (hfam j) F - F)
      = affinePointedCollisionMatroid (ellipticGammaPeriodClass σ τ ∘ hfam) 0 := by
  rw [defectFamily_eq_ellipticGammaExternalDefectFamily hfam hσ hτ hv hFone hUσ hσan hσp hσper
    hσinc hUτ hτan hτp hτper hτinc]
  exact (ellipticGammaTranslationCoset_differentialMatroids hfam σ τ hσ hτ hindependent).1

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] ellipticGammaTranslationCosetRankLawDomain
  ellipticGammaTranslationCosetRankLawComplexAlgebraAnalytic
  ellipticGammaTranslationCosetRankLawComplexAlgebraMero
  ellipticGammaTranslationCosetRankLawComplexDifferential
  ellipticGammaTranslationCosetRankLawMeroDifferential
  ellipticGammaTranslationCosetRankLawMeroCharZero
  ellipticGammaTranslationCosetRankLawEllipticDifferential
  ellipticGammaTranslationCosetRankLawEllipticDifferentialAlgebra
  ellipticGammaTranslationCosetRankLawCoordinateDifferential
  ellipticGammaTranslationCosetRankLawCoordinateDifferentialAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The exact finite-shift rank law for a simple paired quasi-elliptic primitive.**  On every
indexed subpacket the differential rank of its translation defects is the number of distinct
nonzero period classes the subpacket meets. -/
theorem pairedQuasiEllipticPrimitive_eRk
    {κ : Type*} (hfam : κ → ℂ)
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods σ τ))
    {F : meroField (Set.univ : Set ℂ)} {uσ uτ : ℂ → ℂ}
    (hFone : addTranslationMeroEquiv 1 F = F)
    (hUσ : RealizesMero (addTranslationMeroEquiv σ F - F) uσ)
    (hσan : ∀ z ∉ thetaDivisor τ, AnalyticAt ℂ uσ z)
    (hσp : ∀ q ∈ thetaDivisor τ, HasPrincipalPart uσ q 1)
    (hσper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + 1) = uσ w)
    {kσ : ℂ} (hσinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + τ) = uσ w + kσ)
    (hUτ : RealizesMero (addTranslationMeroEquiv τ F - F) uτ)
    (hτan : ∀ z ∉ shiftedThetaDivisor σ ((τ - σ) / 2), AnalyticAt ℂ uτ z)
    (hτp : ∀ q ∈ shiftedThetaDivisor σ ((τ - σ) / 2), HasPrincipalPart uτ q 1)
    (hτper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + 1) = uτ w)
    {kτ : ℂ} (hτinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + σ) = uτ w + kτ) (I : Set κ) :
    (differentialFamilyMatroid (F := meromorphicEllipticCompositum σ τ)
        (fun j => addTranslationMeroEquiv (hfam j) F - F)).eRk I
      = (((ellipticGammaPeriodClass σ τ ∘ hfam) '' I) ∩ {q | q ≠ 0}).encard := by
  rw [defectFamily_eq_ellipticGammaExternalDefectFamily hfam hσ hτ hv hFone hUσ hσan hσp hσper
    hσinc hUτ hτan hτp hτper hτinc]
  exact (ellipticGammaTranslationCoset_eRk hfam σ τ hσ hτ hindependent I).1

end

end GaloisForLFunctions.HTGeometry
