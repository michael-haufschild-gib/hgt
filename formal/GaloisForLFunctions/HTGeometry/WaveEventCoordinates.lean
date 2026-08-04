import GaloisForLFunctions.HTGeometry.WaveDirectionalCalculus

/-!
# The coordinate dictionary between time-space and event coordinates

The energy layer is written on `ℝ × (Fin d → ℝ)`, with time and space separated; the corpus's clock
operators are written on `Fin (d + 1) → ℝ`, with the time coordinate the zeroth entry. The linear
map `(t, x) ↦ Fin.cons t x` identifies the two, and carries the time direction to the zeroth
coordinate vector and the `i`-th spatial direction to the `(i+1)`-st. Hence the directional
derivatives of a pulled-back field are the coordinate partial derivatives of the field itself.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

section Coordinates

variable {d : ℕ} {u : (Fin (d + 1) → ℝ) → ℝ}

/-- The event of a time and a spatial point. -/
noncomputable def eventCLM (d : ℕ) : (ℝ × (Fin d → ℝ)) →L[ℝ] (Fin (d + 1) → ℝ) :=
  ContinuousLinearMap.pi fun j : Fin (d + 1) =>
    Fin.cases (motive := fun _ => (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ)
      (ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ))
      (fun i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ))) j

@[simp] theorem eventCLM_apply (p : ℝ × (Fin d → ℝ)) : eventCLM d p = Fin.cons p.1 p.2 := by
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ i => rfl

theorem eventCLM_timeDir : eventCLM d (timeDir d) = Pi.single (0 : Fin (d + 1)) (1 : ℝ) := by
  funext j
  rw [eventCLM_apply]
  induction j using Fin.cases with
  | zero => simp [timeDir]
  | succ i =>
    rw [Fin.cons_succ]
    have hne : (i.succ : Fin (d + 1)) ≠ 0 := Fin.succ_ne_zero i
    rw [Pi.single_eq_of_ne hne]
    simp [timeDir]

theorem eventCLM_spaceDir (i : Fin d) :
    eventCLM d (spaceDir d i) = Pi.single (i.succ : Fin (d + 1)) (1 : ℝ) := by
  funext j
  rw [eventCLM_apply]
  induction j using Fin.cases with
  | zero =>
    rw [Fin.cons_zero]
    have hne : (0 : Fin (d + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    rw [Pi.single_eq_of_ne hne]
    simp [spaceDir]
  | succ k =>
    rw [Fin.cons_succ]
    by_cases hk : k = i
    · subst hk
      simp [spaceDir]
    · have hks : (k.succ : Fin (d + 1)) ≠ i.succ := fun h => hk (Fin.succ_injective d h)
      rw [Pi.single_eq_of_ne hks]
      simp [spaceDir, Pi.single_eq_of_ne hk]

/-- The chain rule along the coordinate identification. -/
theorem waveDirDeriv_comp_eventCLM (hu : ContDiff ℝ ∞ u) (v p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv v (fun q => u (eventCLM d q)) p = fderiv ℝ u (eventCLM d p) (eventCLM d v) := by
  have hcomp : HasFDerivAt (fun q : ℝ × (Fin d → ℝ) => u (eventCLM d q))
      ((fderiv ℝ u (eventCLM d p)).comp (eventCLM d)) p :=
    (((contDiff_infty_iff_fderiv.mp hu).1 (eventCLM d p)).hasFDerivAt).comp p
      (eventCLM d).hasFDerivAt
  rw [waveDirDeriv, hcomp.fderiv]
  rfl

theorem waveDirDeriv_timeDir_comp_eventCLM (hu : ContDiff ℝ ∞ u) (p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv (timeDir d) (fun q => u (eventCLM d q)) p = coordPartial 0 u (eventCLM d p) := by
  rw [waveDirDeriv_comp_eventCLM hu, eventCLM_timeDir, coordPartial]

theorem waveDirDeriv_spaceDir_comp_eventCLM (hu : ContDiff ℝ ∞ u) (i : Fin d)
    (p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv (spaceDir d i) (fun q => u (eventCLM d q)) p
      = coordPartial i.succ u (eventCLM d p) := by
  rw [waveDirDeriv_comp_eventCLM hu, eventCLM_spaceDir, coordPartial]

theorem contDiff_comp_eventCLM (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ fun q : ℝ × (Fin d → ℝ) => u (eventCLM d q) :=
  hu.comp (eventCLM d).contDiff

/-- The second derivatives transport as well. -/
theorem waveDirDeriv_timeDir_two_comp_eventCLM (hu : ContDiff ℝ ∞ u) (p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) fun q => u (eventCLM d q)) p
      = coordPartial 0 (coordPartial 0 u) (eventCLM d p) := by
  have hfirst : (waveDirDeriv (timeDir d) fun q : ℝ × (Fin d → ℝ) => u (eventCLM d q))
      = fun q => coordPartial 0 u (eventCLM d q) := by
    funext q
    exact waveDirDeriv_timeDir_comp_eventCLM hu q
  rw [hfirst]
  exact waveDirDeriv_timeDir_comp_eventCLM (contDiff_coordPartial hu 0) p

theorem waveDirDeriv_spaceDir_two_comp_eventCLM (hu : ContDiff ℝ ∞ u) (i : Fin d)
    (p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) fun q => u (eventCLM d q)) p
      = coordPartial i.succ (coordPartial i.succ u) (eventCLM d p) := by
  have hfirst : (waveDirDeriv (spaceDir d i) fun q : ℝ × (Fin d → ℝ) => u (eventCLM d q))
      = fun q => coordPartial i.succ u (eventCLM d q) := by
    funext q
    exact waveDirDeriv_spaceDir_comp_eventCLM hu i q
  rw [hfirst]
  exact waveDirDeriv_spaceDir_comp_eventCLM (contDiff_coordPartial hu i.succ) i p

end Coordinates

end GaloisForLFunctions.HTGeometry
