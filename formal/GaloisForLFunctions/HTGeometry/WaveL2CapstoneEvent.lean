import GaloisForLFunctions.HTGeometry.WaveL2Capstone
import GaloisForLFunctions.HTGeometry.WaveOperatorBridge

/-!
# The capstone in event coordinates

The uniqueness theorem whose hypotheses are square integrability and factor-wise domination of each
solution separately, stated on events: this is the form the clock programme quotes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section CapstoneEvent

variable {d : ℕ} {u₁ u₂ V : (Fin (d + 1) → ℝ) → ℝ}

/-- **Uniqueness for the corpus's clock equation, with every hypothesis on one solution at a
time.** -/
theorem eq_of_solvesPotentialWave_of_memLp_of_factorDominated
    (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (h₁ : L2Solution fun q => u₁ (eventCLM d q))
    (h₂ : L2Solution fun q => u₂ (eventCLM d q))
    (hd₁ : FactorDominated fun q => u₁ (eventCLM d q))
    (hd₂ : FactorDominated fun q => u₂ (eventCLM d q))
    (hs₁ : ∀ y : Fin (d + 1) → ℝ, SolvesPotentialWaveAt (kgWaveOp d) V u₁ y)
    (hs₂ : ∀ y : Fin (d + 1) → ℝ, SolvesPotentialWaveAt (kgWaveOp d) V u₂ y)
    (hVcont : Continuous V) {M : ℝ} (hM : ∀ y, |V y| ≤ M)
    (hval : ∀ x : Fin d → ℝ, u₁ (Fin.cons 0 x) = u₂ (Fin.cons 0 x))
    (hder : ∀ x : Fin d → ℝ,
      coordPartial 0 u₁ (Fin.cons 0 x) = coordPartial 0 u₂ (Fin.cons 0 x))
    (y : Fin (d + 1) → ℝ) : u₁ y = u₂ y := by
  have hev : ∀ x : Fin d → ℝ, eventCLM d ((0 : ℝ), x) = Fin.cons 0 x := by
    intro x
    rw [eventCLM_apply]
  have hvalc : ∀ x : Fin d → ℝ,
      (fun q : ℝ × (Fin d → ℝ) => u₁ (eventCLM d q)) ((0 : ℝ), x)
        = (fun q : ℝ × (Fin d → ℝ) => u₂ (eventCLM d q)) ((0 : ℝ), x) := by
    intro x
    show u₁ (eventCLM d ((0 : ℝ), x)) = u₂ (eventCLM d ((0 : ℝ), x))
    rw [hev x]
    exact hval x
  have hderc : ∀ x : Fin d → ℝ,
      waveDirDeriv (timeDir d) (fun q : ℝ × (Fin d → ℝ) => u₁ (eventCLM d q)) ((0 : ℝ), x)
        = waveDirDeriv (timeDir d) (fun q : ℝ × (Fin d → ℝ) => u₂ (eventCLM d q))
            ((0 : ℝ), x) := by
    intro x
    rw [waveDirDeriv_timeDir_comp_eventCLM hu₁, waveDirDeriv_timeDir_comp_eventCLM hu₂, hev x]
    exact hder x
  have hmain := eq_of_solvesWaveEq_of_memLp_of_factorDominated h₁ h₂ hd₁ hd₂
    (solvesWaveEq_comp_eventCLM hu₁ hs₁) (solvesWaveEq_comp_eventCLM hu₂ hs₂)
    (hVcont.comp (eventCLM d).continuous) (fun p => hM (eventCLM d p)) hvalc hderc
    (y 0) (Fin.tail y)
  have hres : u₁ (eventCLM d ((y 0, Fin.tail y) : ℝ × (Fin d → ℝ)))
      = u₂ (eventCLM d ((y 0, Fin.tail y) : ℝ × (Fin d → ℝ))) := hmain
  rwa [eventCLM_surjective y] at hres

end CapstoneEvent

end GaloisForLFunctions.HTGeometry
