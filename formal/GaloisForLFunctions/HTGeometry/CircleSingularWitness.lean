import GaloisForLFunctions.HTGeometry.FAndMRieszConsequences

/-!
# Measures singular to circle Lebesgue measure

The F. and M. Riesz layer and the pure-singular carrier layer are stated for a finite circle
measure singular to `circleLebesgue`, and no such measure was exhibited.  Circle Lebesgue measure
is the transport of the Haar probability measure of the additive circle, which has no atoms, so
every measure carried by a countable set is singular to it.

* **`circleLebesgue_singleton`** and the `NoAtoms` instance;
* **`mutuallySingular_circleLebesgue_of_countable`** — the criterion;
* **`mutuallySingular_dirac_circleLebesgue`** — the witness, and with it an unconditional instance
  of one-sided Fourier rigidity.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- Circle Lebesgue measure has no atoms: it is the transport of the additive Haar probability
measure, whose closed balls of radius zero are null. -/
theorem circleLebesgue_singleton (z : Circle) : circleLebesgue {z} = 0 := by
  classical
  set h := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero with hh
  have hmeas : Measurable h := h.continuous.measurable
  rw [circleLebesgue, Measure.map_apply hmeas (measurableSet_singleton z)]
  have hpre : h ⁻¹' {z} = {h.symm z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      rw [← hx]
      exact (h.symm_apply_apply x).symm
    · intro hx
      rw [hx]
      exact h.apply_symm_apply z
  rw [hpre]
  have hball := AddCircle.volume_closedBall (1 : ℝ) (x := h.symm z) 0
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hball
  simpa using hball

instance : NullSingletonClass circleLebesgue := ⟨circleLebesgue_singleton⟩

/-- **Every measure carried by a countable set is singular to circle Lebesgue measure.** -/
theorem mutuallySingular_circleLebesgue_of_countable {mu : Measure Circle} {s : Set Circle}
    (hs : s.Countable) (hmu : mu sᶜ = 0) : mu ⟂ₘ circleLebesgue :=
  ⟨sᶜ, hs.measurableSet.compl, hmu, by
    rw [compl_compl]
    exact hs.measure_zero circleLebesgue⟩

/-- A point mass is singular to circle Lebesgue measure. -/
theorem mutuallySingular_dirac_circleLebesgue (z : Circle) :
    (Measure.dirac z) ⟂ₘ circleLebesgue :=
  mutuallySingular_circleLebesgue_of_countable (Set.countable_singleton z) (by simp)

/-- **One-sided Fourier rigidity is attained.**  The point masses are singular to circle Lebesgue
measure, so the F. and M. Riesz conclusion holds on an explicit finite circle measure. -/
theorem oneSidedFourierRigid_dirac (z : Circle) :
    IsOneSidedFourierRigid (Measure.dirac z) :=
  oneSidedFourierRigid_of_mutuallySingular_circle (Measure.dirac z)
    (mutuallySingular_dirac_circleLebesgue z)

end

end GaloisForLFunctions.HTGeometry
