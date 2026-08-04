import GaloisForLFunctions.HTGeometry.WaveOperatorBridge
import GaloisForLFunctions.HTGeometry.WaveTimeReflection

/-!
# Uniqueness for the corpus's clock equation

The energy layer is written in time-space coordinates; the corpus's clock equation is written on
events. The bridge identifies them, so the uniqueness theorem can be stated in the corpus's own
language: a smooth field with spatially compact support solving `□u + Vu = 0` for a bounded
continuous potential is determined by its value and its time derivative on the initial slice.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

section EventForm

variable {d : ℕ} {u₁ u₂ V : (Fin (d + 1) → ℝ) → ℝ} {K : Set (Fin d → ℝ)}

theorem tail_eventCLM (p : ℝ × (Fin d → ℝ)) : Fin.tail (eventCLM d p) = p.2 := by
  funext i
  show eventCLM d p i.succ = p.2 i
  rw [eventCLM_apply, Fin.cons_succ]

/-- **Uniqueness for the corpus's clock equation.** Two smooth solutions with spatially compact
support, the same bounded continuous potential and the same Cauchy data on the initial slice agree
at every event. -/
theorem eq_of_solvesPotentialWave_of_data_eq (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (hV : Continuous V) (hK : IsCompact K)
    (hzero₁ : ∀ y : Fin (d + 1) → ℝ, Fin.tail y ∉ K → u₁ y = 0)
    (hzero₂ : ∀ y : Fin (d + 1) → ℝ, Fin.tail y ∉ K → u₂ y = 0)
    (h₁ : ∀ y : Fin (d + 1) → ℝ, SolvesPotentialWaveAt (kgWaveOp d) V u₁ y)
    (h₂ : ∀ y : Fin (d + 1) → ℝ, SolvesPotentialWaveAt (kgWaveOp d) V u₂ y)
    {M : ℝ} (hM : ∀ y, |V y| ≤ M)
    (hval : ∀ x : Fin d → ℝ, u₁ (Fin.cons 0 x) = u₂ (Fin.cons 0 x))
    (hder : ∀ x : Fin d → ℝ,
      coordPartial 0 u₁ (Fin.cons 0 x) = coordPartial 0 u₂ (Fin.cons 0 x))
    (y : Fin (d + 1) → ℝ) : u₁ y = u₂ y := by
  have hcd₁ : ContDiff ℝ ∞ fun q : ℝ × (Fin d → ℝ) => u₁ (eventCLM d q) :=
    contDiff_comp_eventCLM hu₁
  have hcd₂ : ContDiff ℝ ∞ fun q : ℝ × (Fin d → ℝ) => u₂ (eventCLM d q) :=
    contDiff_comp_eventCLM hu₂
  have hzc₁ : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u₁ (eventCLM d p) = 0 := by
    intro p hp
    exact hzero₁ (eventCLM d p) (by rw [tail_eventCLM]; exact hp)
  have hzc₂ : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u₂ (eventCLM d p) = 0 := by
    intro p hp
    exact hzero₂ (eventCLM d p) (by rw [tail_eventCLM]; exact hp)
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
        = waveDirDeriv (timeDir d) (fun q : ℝ × (Fin d → ℝ) => u₂ (eventCLM d q)) ((0 : ℝ), x) := by
    intro x
    rw [waveDirDeriv_timeDir_comp_eventCLM hu₁, waveDirDeriv_timeDir_comp_eventCLM hu₂, hev x]
    exact hder x
  have hmain := eq_of_solvesWaveEq_of_data_eq_all hcd₁ hcd₂ (hV.comp (eventCLM d).continuous) hK
    hzc₁ hzc₂ (solvesWaveEq_comp_eventCLM hu₁ h₁) (solvesWaveEq_comp_eventCLM hu₂ h₂)
    (fun p => hM (eventCLM d p)) hvalc hderc (y 0) (Fin.tail y)
  rw [eventCLM_surjective y] at hmain
  exact hmain

end EventForm

end GaloisForLFunctions.HTGeometry
