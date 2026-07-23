import GaloisForLFunctions.HTGeometry.EllipticGammaArithmeticReflectionPhaseUniversalityLaw
import GaloisForLFunctions.HTGeometry.HomogeneousMultipleEllipticGammaLogDerivativeReflectionUniversalityLaw

/-!
# Arithmetic external/Ward phase universality for elliptic Gamma

The arithmetic period dichotomy and the shared-period external/Ward theorem have the same
independence input. Their closure gives an exhaustive phase law: independent period triples carry
the complete external and homogeneous Ward certificate, while dependent triples flatten into a
finite commensurable reflection factorization.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **Elliptic-Gamma arithmetic external/Ward phase universality law.** For every separated
external-shift family, an upper-half-plane period pair lies in exactly one of two phases:

* rational independence supplies external quotient-matroid freeness, elliptic defect
  differential atomicity, and the complete rank-two homogeneous product/log-derivative Ward
  certificate;
* rational dependence supplies a positive integral commensurability witness and exact reciprocal
  reflection of the finite residue-class factorization.
-/
theorem ellipticGamma_arithmeticExternalWardPhaseUniversality
    {κ : Type*} [DecidableEq κ]
    (s : Finset κ) (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i →
      ThetaTranslationNonresonant tau sigma (h j - h i)) :
    ((LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau) ∧
        EllipticGammaSharedPeriodExternalWardCertificate
          s h sigma tau hsigma htau) ∨
      Nonempty (EllipticGammaCommensurableReflectionCertificate sigma tau)) ∧
    ¬ ((LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau) ∧
        EllipticGammaSharedPeriodExternalWardCertificate
          s h sigma tau hsigma htau) ∧
      Nonempty (EllipticGammaCommensurableReflectionCertificate sigma tau)) := by
  have hphase :=
    ellipticGamma_arithmeticReflectionPhaseUniversality
      sigma tau hsigma htau
  constructor
  · rcases hphase.1 with hindependent | hcommensurable
    · left
      exact ⟨hindependent.independent,
        ellipticGamma_sharedPeriodExternalWardUniversality
          s h sigma tau hsigma htau hindependent.independent hnonres hsep⟩
    · exact Or.inr hcommensurable
  · rintro ⟨⟨hindependent, _hexternal⟩, hcommensurable⟩
    exact
      (ellipticGammaCommensurableReflectionCertificate_nonempty_iff
        sigma tau hsigma htau).1 hcommensurable hindependent

end

end GaloisForLFunctions

