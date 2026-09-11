import GaloisForLFunctions.HTGeometry.GomesTruncatedJetHorizonLogCalculus
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# A group section of actual unipotent horizon restriction

Logarithm, intrinsic zero extension and exponential lift every lower-horizon
unipotent gauge transformation. Since the coefficient extension is linear,
this lift is a group homomorphism and a right inverse to actual restriction.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Extend actual unipotent gauge transformations by extending their logarithmic coordinates. -/
def gomesTruncatedJetUnipotentHorizonSection (n r : ℕ) (z : ℂ) :
    gomesTruncatedJetUnipotentGroup n z →* gomesTruncatedJetUnipotentGroup (n + r) z :=
  (gomesTruncatedJetUnipotentLogEquiv (n + r) z).symm.toMonoidHom.comp
    ((AddMonoidHom.toMultiplicative (gomesTruncatedJetNilpotentHorizonSection n r z).toAddMonoidHom).comp
      (gomesTruncatedJetUnipotentLogEquiv n z).toMonoidHom)

/-- The actual group section is the literal exponential of the extended terminating logarithm. -/
theorem gomesTruncatedJetUnipotentHorizonSection_apply (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    gomesTruncatedJetUnipotentHorizonSection n r z u =
      gomesTruncatedJetUnipotentExponential (n + r) z
        (gomesTruncatedJetNilpotentHorizonSection n r z (gomesTruncatedJetUnipotentLogarithm n z u)) := by
  change (gomesTruncatedJetUnipotentLogEquiv (n + r) z).symm
    (Multiplicative.ofAdd
      (gomesTruncatedJetNilpotentHorizonSection n r z (gomesTruncatedJetUnipotentLogarithm n z u))) = _
  exact gomesTruncatedJetUnipotentLogEquiv_symm (n + r) z _

/-- Actual horizon restriction recovers every unipotent gauge transformation extended through logarithmic coordinates. -/
theorem gomesTruncatedJetUnipotentHorizon_section (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    gomesTruncatedJetUnipotentHorizon n r z (gomesTruncatedJetUnipotentHorizonSection n r z u) = u := by
  rw [gomesTruncatedJetUnipotentHorizonSection_apply, gomesTruncatedJetUnipotentHorizon_exponential,
    gomesTruncatedJetNilpotentHorizon_section, gomesTruncatedJetUnipotentExponential_logarithm]

/-- Every actual lower-horizon unipotent symmetry lifts through a group section. -/
theorem gomesTruncatedJetUnipotentHorizon_surjective (n r : ℕ) (z : ℂ) :
    Function.Surjective (gomesTruncatedJetUnipotentHorizon n r z) := by
  intro u
  exact ⟨gomesTruncatedJetUnipotentHorizonSection n r z u, gomesTruncatedJetUnipotentHorizon_section n r z u⟩

/-- The canonical logarithmic group section loses no lower-horizon unipotent symmetry. -/
theorem gomesTruncatedJetUnipotentHorizonSection_injective (n r : ℕ) (z : ℂ) :
    Function.Injective (gomesTruncatedJetUnipotentHorizonSection n r z) := by
  intro u v h
  have hr := congrArg (gomesTruncatedJetUnipotentHorizon n r z) h
  simpa only [gomesTruncatedJetUnipotentHorizon_section] using hr

/-- The logarithm of the canonical lifted symmetry is exactly its extended nilpotent coordinate. -/
theorem gomesTruncatedJetUnipotentHorizonSection_logarithm (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    gomesTruncatedJetUnipotentLogarithm (n + r) z (gomesTruncatedJetUnipotentHorizonSection n r z u) =
      gomesTruncatedJetNilpotentHorizonSection n r z (gomesTruncatedJetUnipotentLogarithm n z u) := by
  rw [gomesTruncatedJetUnipotentHorizonSection_apply, gomesTruncatedJetUnipotentLogarithm_exponential]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
