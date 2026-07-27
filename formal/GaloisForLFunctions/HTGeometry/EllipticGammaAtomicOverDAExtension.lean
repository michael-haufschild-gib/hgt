import GaloisForLFunctions.HTGeometry.EllipticCompositumMatroidTransport
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid

/-!
# Order-one atomic packets stay independent over any differentially algebraic extension

The bottom layer of the all-order multiple elliptic-gamma argument needs the order-one packets to
be differentially independent not only over `ℂ(z)` but over the differentially algebraic extension
`D` in which the higher faces live.  That upgrade is automatic: adjoining differentially algebraic
coefficients preserves differential independence, and the rational coordinate is itself
differentially algebraic over the constants.

* **`differentialIndependent_differentialAdjoin_of_rationalBase`** — differential independence over
  the embedded rational coordinate field survives adjunction of an arbitrary set of germs that are
  differentially algebraic over the constants;
* **`ellipticGammaExternalDefectFamily_differentialIndependent_daExtension`** and
  **`ellipticGammaExternalQuotientFamily_differentialIndependent_daExtension`** — hence every
  separated external-defect packet and its multiplicative counterpart is differentially independent
  over every such extension, in particular over the paired elliptic compositum and over any
  differential adjunction of lower-order structural germs.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

/-- **Differential independence over `ℂ(z)` survives any differentially algebraic extension.** -/
theorem differentialIndependent_differentialAdjoin_of_rationalBase {ι : Type*}
    {x : ι → meroField (Set.univ : Set ℂ)}
    (hx : DifferentialIndependent meromorphicRationalCoordinateField x)
    {G : Set (meroField (Set.univ : Set ℂ))}
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver ℂ g) :
    DifferentialIndependent (differentialAdjoin ℂ G) x :=
  DifferentialIndependent.extendScalarsDifferentialAdjoin
    ((differentialIndependent_meromorphicRationalCoordinateField_iff x).mp hx) hG

/-- **The order-one atomic packet is independent over every differentially algebraic extension.**
This is the bottom-layer input of the all-order multiple elliptic-gamma argument: separated
external-defect families of a genuine elliptic gamma are differentially independent over `ℂ(z)`,
hence over the differentially algebraic extension in which the higher faces live. -/
theorem ellipticGammaExternalDefectFamily_differentialIndependent_daExtension
    {kappa : Type*} (h : kappa → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i → ThetaTranslationNonresonant tau sigma (h j - h i))
    {G : Set (meroField (Set.univ : Set ℂ))}
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver ℂ g) :
    DifferentialIndependent (differentialAdjoin ℂ G)
      (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) :=
  differentialIndependent_differentialAdjoin_of_rationalBase
    (ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase
      h sigma tau hsigma htau hindependent hnonres hsep) hG

/-- The paired elliptic compositum is one such extension. -/
theorem ellipticGammaExternalDefectFamily_differentialIndependent_ellipticCompositum'
    {kappa : Type*} (h : kappa → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i → ThetaTranslationNonresonant tau sigma (h j - h i))
    {σ' τ' : ℂ} (hσ' : 0 < σ'.im) (hτ' : 0 < τ'.im) :
    DifferentialIndependent (meromorphicEllipticCompositum σ' τ')
      (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) := by
  have hind := ellipticGammaExternalDefectFamily_differentialIndependent_daExtension
    h sigma tau hsigma htau hindependent hnonres hsep
    (G := (meromorphicEllipticCompositum σ' τ' : Set (meroField (Set.univ : Set ℂ))))
    (fun g hg => differentialAlgebraicOver_complex_of_mem_meromorphicEllipticCompositum hσ' hτ' hg)
  rwa [differentialAdjoin_self_of_derivationClosed _
    (meromorphicEllipticCompositum_derivationClosed σ' τ')] at hind

end

end GaloisForLFunctions.HTGeometry
