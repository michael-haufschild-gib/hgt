import GaloisForLFunctions.HTGeometry.WaveEventCoordinates
import GaloisForLFunctions.HTGeometry.WaveEnergyFlux
import GaloisForLFunctions.HTGeometry.KleinGordonClockProbe
import GaloisForLFunctions.HTGeometry.ClockProbeSeparablePotential

/-!
# The corpus clock operator in time-space coordinates

The corpus writes the flat clock operator as the divergence-form d'Alembertian of the Minkowski
signature on `Fin (d + 1) → ℝ`; the energy layer writes it as `∂ₜ²u - Δu` on `ℝ × (Fin d → ℝ)`. For
a smooth field the first expands into second coordinate partial derivatives, the zeroth carrying the
sign, and the coordinate dictionary turns those into the directional derivatives of the pulled back
field.

So a solution of the corpus's potential wave equation is a solution of `SolvesWaveEq` in time-space
coordinates, and every probe the corpus constructs by Fourier synthesis inherits the energy estimate,
the uniqueness theorem and continuous dependence.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

section Bridge

variable {d : ℕ} {u V : (Fin (d + 1) → ℝ) → ℝ}

/-- **The flat clock operator in second coordinate partial derivatives.** -/
theorem kgWaveOp_eq_of_contDiff (hu : ContDiff ℝ ∞ u) (y : Fin (d + 1) → ℝ) :
    kgWaveOp d u y = -coordPartial 0 (coordPartial 0 u) y
      + ∑ i : Fin d, coordPartial i.succ (coordPartial i.succ u) y := by
  have hdiff : ∀ j : Fin (d + 1), DifferentiableAt ℝ (coordPartial j u) y :=
    fun j => differentiableAt_of_contDiff_infty (contDiff_coordPartial hu j) y
  rw [kgWaveOp, ofSignature_dalembert_of_differentiableAt (kgEps d) (kgEps_ne_zero d) hdiff,
    Fin.sum_univ_succ]
  have h0 : (kgEps d 0)⁻¹ = -1 := by
    rw [kgEps]
    norm_num
  have hs : ∀ i : Fin d, (kgEps d i.succ)⁻¹ = 1 := by
    intro i
    rw [kgEps, if_neg (Fin.succ_ne_zero i)]
    norm_num
  rw [h0, Finset.sum_congr rfl fun i _ => by rw [hs i, one_mul]]
  ring

/-- **A solution of the corpus's clock equation is a solution in time-space coordinates.** -/
theorem solvesWaveEq_comp_eventCLM (hu : ContDiff ℝ ∞ u)
    (h : ∀ y : Fin (d + 1) → ℝ, SolvesPotentialWaveAt (kgWaveOp d) V u y) :
    SolvesWaveEq (fun q => u (eventCLM d q)) (fun q => V (eventCLM d q)) := by
  intro p
  have heq : kgWaveOp d u (eventCLM d p) + V (eventCLM d p) * u (eventCLM d p) = 0 :=
    h (eventCLM d p)
  rw [kgWaveOp_eq_of_contDiff hu] at heq
  have htime := waveDirDeriv_timeDir_two_comp_eventCLM hu p
  have hspace : ∀ i : Fin d,
      waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) fun q => u (eventCLM d q)) p
        = coordPartial i.succ (coordPartial i.succ u) (eventCLM d p) :=
    fun i => waveDirDeriv_spaceDir_two_comp_eventCLM hu i p
  show waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) fun q => u (eventCLM d q)) p
    = (∑ i : Fin d, waveDirDeriv (spaceDir d i)
        (waveDirDeriv (spaceDir d i) fun q => u (eventCLM d q)) p)
      + V (eventCLM d p) * u (eventCLM d p)
  rw [htime, Finset.sum_congr rfl fun i _ => hspace i]
  linarith

/-! ## The converse, and the equivalence -/

/-- Every event is the image of a time and a spatial point. -/
theorem eventCLM_surjective (y : Fin (d + 1) → ℝ) :
    eventCLM d (y 0, Fin.tail y) = y := by
  rw [eventCLM_apply]
  exact Fin.cons_self_tail y

/-- **A solution in time-space coordinates is a solution of the corpus's clock equation.** -/
theorem solvesPotentialWaveAt_of_solvesWaveEq (hu : ContDiff ℝ ∞ u)
    (h : SolvesWaveEq (fun q => u (eventCLM d q)) (fun q => V (eventCLM d q)))
    (y : Fin (d + 1) → ℝ) : SolvesPotentialWaveAt (kgWaveOp d) V u y := by
  have hp := h (y 0, Fin.tail y)
  rw [waveDirDeriv_timeDir_two_comp_eventCLM hu,
    Finset.sum_congr rfl fun i _ => waveDirDeriv_spaceDir_two_comp_eventCLM hu i _] at hp
  simp only [eventCLM_surjective] at hp
  show kgWaveOp d u y + V y * u y = 0
  rw [kgWaveOp_eq_of_contDiff hu]
  linarith

/-- **The two formulations of the clock equation agree.** -/
theorem solvesWaveEq_comp_eventCLM_iff (hu : ContDiff ℝ ∞ u) :
    SolvesWaveEq (fun q => u (eventCLM d q)) (fun q => V (eventCLM d q))
      ↔ ∀ y : Fin (d + 1) → ℝ, SolvesPotentialWaveAt (kgWaveOp d) V u y :=
  ⟨fun h => solvesPotentialWaveAt_of_solvesWaveEq hu h,
    fun h => solvesWaveEq_comp_eventCLM hu h⟩

end Bridge

end GaloisForLFunctions.HTGeometry
