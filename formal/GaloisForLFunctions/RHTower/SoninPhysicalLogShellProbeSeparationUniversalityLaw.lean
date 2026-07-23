import GaloisForLFunctions.RHTower.SoninLogShellCocycle
import GaloisForLFunctions.RHTower.SoninSemilocalProbeUniversalSourceSeparationLaw

/-!
# Sonin physical log-shell probe separation universality

The intrinsic physical logarithmic-shell trace density is the exact unsquared semilocal prime
flux.  Consequently one finite test separates the projection-correction relative trace from every
nonzero Hilbert--Schmidt cyclic generator built from the actual shell cocycle.
-/

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- **Physical shell probe-universal source separation.**  One finite prime-power test separates
the failed projection-correction trace from every Hilbert--Schmidt cyclic tangent generator after
the abstract flux coefficient is replaced by its exact physical logarithmic-shell density. -/
theorem exists_finiteSoninSemilocalRelativeTrace_ne_everyHilbertSchmidtLogShellGenerator :
    ∃ f : SoninPrimePowerTest,
      ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (C : H →L[ℂ] H), IsHilbertSchmidt C → C ≠ 0 →
        canonicalFiniteSoninSemilocalRelativeTrace f ≠
          f.sum (fun pk w =>
            w * opTrace
              (normalizedHilbertSchmidtCentralTangentCarrier C
                soninPrimePowerLogShellTraceDensity pk)) := by
  obtain ⟨f, hf⟩ :=
    exists_finiteSoninSemilocalRelativeTrace_ne_everyHilbertSchmidtCyclicSourceGenerator
  refine ⟨f, ?_⟩
  intro H _ _ _ C hC hCne
  have hdensity :
      soninPrimePowerLogShellTraceDensity = soninSemilocalPrimeFluxCoefficient := by
    funext pk
    exact soninPrimePowerLogShellTraceDensity_eq_fluxCoefficient pk
  rw [hdensity]
  exact hf C hC hCne

end

end RHTower
