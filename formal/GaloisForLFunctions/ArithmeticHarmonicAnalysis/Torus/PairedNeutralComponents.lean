import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralClopens
import GaloisForLFunctions.HTGeometry.Topology.NoetherianComponents
import GaloisForLFunctions.HTGeometry.Topology.ClopenComponents
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# The native connected components of a paired neutral quotient

For every ideal `J` of `K[hᵢ]`, the substitution `hᵢ ↦ zᵢwᵢ` induces a
homeomorphism from the connected-component space of the paired quotient
spectrum to that of the neutral quotient spectrum. Its forward map is the
actual map induced by contraction of prime ideals.

Both spectra are Noetherian. Their connected components are therefore clopen,
and the previously established clopen pullback isomorphism identifies the
components themselves. In particular, the full preimage of a neutral component
is one paired component, and both spaces have the same finite component count.
No primality, radicality, or properness assumption on `J` is needed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial TopologicalSpace
open GaloisForLFunctions.HTGeometry
open scoped PairedNeutral

attribute [local instance] NoetherianComponents.connectedComponents_discrete
attribute [local instance] NoetherianComponents.connectedComponents_finite

variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Paired substitution canonically identifies the native connected-component spaces. -/
def pairedNeutralComponentsHomeomorph (J : Ideal (MvPolynomial ι K)) :
    ConnectedComponents
        (PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) ≃ₜ
      ConnectedComponents (PrimeSpectrum (MvPolynomial ι K ⧸ J)) :=
  (ClopenComponents.componentsHomeomorphOfClopenOrderIso
    (pairedNeutralClopenOrderIso K J)).symm

/-- The component homeomorphism is induced by the actual neutral-coordinate map on spectra. -/
theorem pairedNeutralComponentsHomeomorph_eq_inducedMap (J : Ideal (MvPolynomial ι K)) :
    (pairedNeutralComponentsHomeomorph K J : _ → _) =
      (PrimeSpectrum.continuous_comap (algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)))).connectedComponentsMap :=
  ClopenComponents.componentsHomeomorph_symm_eq_inducedMap
    (pairedNeutralClopenOrderIso K J) _ (PrimeSpectrum.continuous_comap _)
    (pairedNeutralClopenOrderIso_apply K J)

/-- A prime's connected component is sent to the component of its contraction. -/
@[simp] theorem pairedNeutralComponentsHomeomorph_mk (J : Ideal (MvPolynomial ι K))
    (p : PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) :
    pairedNeutralComponentsHomeomorph K J (ConnectedComponents.mk p) =
      ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) p) :=
  ClopenComponents.componentsEquiv_symm_mk_of_pullback
    (pairedNeutralClopenOrderIso K J) _ (pairedNeutralClopenOrderIso_apply K J) p

/-- Pulling back a neutral connected component gives exactly one paired connected component. -/
theorem pairedNeutral_connectedComponent_preimage (J : Ideal (MvPolynomial ι K))
    (p : PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) :
    PrimeSpectrum.comap (algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) ⁻¹'
      connectedComponent (PrimeSpectrum.comap (algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) p) =
      connectedComponent p :=
  ClopenComponents.connectedComponent_preimage_eq
    (pairedNeutralClopenOrderIso K J) _ (pairedNeutralClopenOrderIso_apply K J) p

/-- The paired quotient spectrum has finitely many connected components. -/
theorem pairedNeutral_connectedComponents_finite (J : Ideal (MvPolynomial ι K)) :
    Finite (ConnectedComponents
      (PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)))) :=
  inferInstance

/-- The neutral quotient spectrum has finitely many connected components. -/
theorem neutral_connectedComponents_finite (J : Ideal (MvPolynomial ι K)) :
    Finite (ConnectedComponents (PrimeSpectrum (MvPolynomial ι K ⧸ J))) :=
  inferInstance

/-- Paired substitution preserves the exact finite number of connected components. -/
theorem card_pairedNeutral_connectedComponents (J : Ideal (MvPolynomial ι K)) :
    Nat.card (ConnectedComponents
        (PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)))) =
      Nat.card (ConnectedComponents (PrimeSpectrum (MvPolynomial ι K ⧸ J))) :=
  Nat.card_congr (pairedNeutralComponentsHomeomorph K J).toEquiv

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralComponentsHomeomorph
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralComponentsHomeomorph_eq_inducedMap
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutral_connectedComponent_preimage
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutral_connectedComponents_finite
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_pairedNeutral_connectedComponents
