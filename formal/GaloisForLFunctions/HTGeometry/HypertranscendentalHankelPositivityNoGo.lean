import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.GammaBoseSpectralHankel

/-!
# Hypertranscendence does not force a Hankel sign violation

The digamma function is hypertranscendental, but after the natural alternating factorial
normalization its positive-order jets on every positive real base point are the moments of an
infinite positive reciprocal-energy spectrum.  Consequently every finite Hankel block of those
jets is positive definite.

This is an unconditional guardrail for RH source research: Hölder hypertranscendence by itself
cannot force a negative completed-source quadratic form.  Any such sign must use the coupled
prime--Gamma arithmetic source rather than the differential transcendence of the archimedean
factor alone.
-/

open GaloisForLFunctions

namespace HTGeometry

noncomputable section

/-- A function has a strict signed-jet Hankel tower when, at every positive real base point, the
alternating factorial normalization of its positive-order derivatives has positive-definite
Hankel matrices in every finite size. -/
def HasStrictSignedJetHankelTower (f : ℂ → ℂ) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ n : ℕ,
    (momentHankelMatrix
      (fun m : ℕ ↦
        (((-1 : ℂ) ^ (m + 2) * iteratedDeriv (m + 1) f (a : ℂ)) /
          ((m + 1).factorial : ℂ)).re)
      n).PosDef

/-- The hypertranscendental digamma function has a strict signed-jet Hankel tower. -/
theorem digamma_hasStrictSignedJetHankelTower :
    HasStrictSignedJetHankelTower Complex.digamma := by
  intro a ha n
  simpa only [HasStrictSignedJetHankelTower, signedNormalizedDigammaJet] using
    signedNormalizedDigammaJet_hankel_posDef ha n

/-- **Hölder/Hankel no-go.**  There exists a hypertranscendental function whose naturally signed
derivative moments have strictly positive Hankel blocks at every positive base point and every
finite rank.  Hence hypertranscendence alone is compatible with the strongest finite Hankel
positivity used by the filtered-source route. -/
theorem exists_hypertranscendental_hasStrictSignedJetHankelTower :
    ∃ f : ℂ → ℂ, Hypertranscendental f ∧ HasStrictSignedJetHankelTower f :=
  ⟨Complex.digamma, hypertranscendental_digamma,
    digamma_hasStrictSignedJetHankelTower⟩

end

end HTGeometry
