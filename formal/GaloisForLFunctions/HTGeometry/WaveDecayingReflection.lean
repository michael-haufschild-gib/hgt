import GaloisForLFunctions.HTGeometry.WaveDecayingCompactSupport
import GaloisForLFunctions.HTGeometry.WaveEnergyTwoSided

/-!
# Time reflection of a decaying solution

Reversing time carries a decaying solution to a decaying solution of the reflected potential: the
energy density is even in the time derivative, the slices are the reflected slices, and every
integrand of the hypothesis bundle changes at most by a sign. So the estimate holds on both sides of
the initial slice for decaying solutions too.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Reflection

variable {d : ℕ} {u V : ℝ × (Fin d → ℝ) → ℝ}

theorem slice_comp_timeReflect (t : ℝ) :
    slice (fun q => u (timeReflect d q)) t = slice u (-t) := rfl

theorem slice_dirDeriv_comp_timeReflect (hu : ContDiff ℝ ∞ u) (t : ℝ) :
    slice (waveDirDeriv (timeDir d) fun q => u (timeReflect d q)) t
      = fun x : Fin d → ℝ => -slice (waveDirDeriv (timeDir d) u) (-t) x := by
  funext x
  exact waveDirDeriv_timeDir_comp_timeReflect hu (t, x)

theorem coordPartial_neg_fun (f : (Fin d → ℝ) → ℝ) (i : Fin d) :
    coordPartial i (fun x : Fin d → ℝ => -f x) = fun x => -coordPartial i f x := by
  funext x
  rw [coordPartial, coordPartial, fderiv_fun_neg]
  rfl

theorem energyDensity_comp_timeReflect_fun (hu : ContDiff ℝ ∞ u) :
    energyDensity (fun q => u (timeReflect d q))
      = fun p : ℝ × (Fin d → ℝ) => energyDensity u (timeReflect d p) := by
  funext p
  exact energyDensity_comp_timeReflect hu p

/-- **A decaying solution reflects to a decaying solution.** -/
theorem DecayingSolution.comp_timeReflect (h : DecayingSolution u V) :
    DecayingSolution (fun q => u (timeReflect d q)) (fun q => V (timeReflect d q)) := by
  have hu := h.smooth
  have hslice := slice_dirDeriv_comp_timeReflect hu
  refine
    { smooth := contDiff_comp_timeReflect hu
      solves := solvesWaveEq_comp_timeReflect hu h.solves
      energyInt := fun t => ?_
      greenInt₁ := fun t i => ?_
      greenInt₂ := fun t i => ?_
      greenInt₃ := fun t i => ?_
      fluxInt := fun t => ?_
      dominated := fun t => ?_ }
  · refine (h.energyInt (-t)).congr (Filter.Eventually.of_forall fun x => ?_)
    exact (energyDensity_comp_timeReflect hu (t, x)).symm
  · refine ((h.greenInt₁ (-t) i).neg).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]
    rw [slice_comp_timeReflect, hslice]
    ring
  · refine ((h.greenInt₂ (-t) i).neg).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]
    rw [slice_comp_timeReflect, hslice, coordPartial_neg_fun]
    ring
  · refine ((h.greenInt₃ (-t) i).neg).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]
    rw [slice_comp_timeReflect, hslice]
    ring
  · refine ((h.fluxInt (-t)).neg).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]
    show -((V (-t, x) + 1) * (u (-t, x) * waveDirDeriv (timeDir d) u (-t, x)))
      = (V (timeReflect d (t, x)) + 1) * ((fun q => u (timeReflect d q)) (t, x)
        * waveDirDeriv (timeDir d) (fun q => u (timeReflect d q)) (t, x))
    rw [waveDirDeriv_timeDir_comp_timeReflect hu]
    show -((V (-t, x) + 1) * (u (-t, x) * waveDirDeriv (timeDir d) u (-t, x)))
      = (V (-t, x) + 1) * (u (-t, x) * -waveDirDeriv (timeDir d) u (-t, x))
    ring
  · obtain ⟨bound, hbint, hb⟩ := h.dominated (-t)
    refine ⟨bound, hbint, fun s hs x => ?_⟩
    have hval : waveDirDeriv (timeDir d) (energyDensity fun q => u (timeReflect d q)) (s, x)
        = -waveDirDeriv (timeDir d) (energyDensity u) (-s, x) := by
      rw [energyDensity_comp_timeReflect_fun hu,
        waveDirDeriv_timeDir_comp_timeReflect (contDiff_energyDensity hu)]
      rfl
    rw [hval, norm_neg]
    refine hb (-s) ?_ x
    rw [Metric.mem_ball, Real.dist_eq] at hs ⊢
    have : |-s - -t| = |s - t| := by
      rw [show -s - -t = -(s - t) by ring, abs_neg]
    rw [this]
    exact hs

/-- **The energy estimate for a decaying solution, on both sides of the initial slice.** -/
theorem waveEnergy_le_exp_abs_of_decaying (h : DecayingSolution u V) {M : ℝ}
    (hM : ∀ p, |V p| ≤ M) (t : ℝ) :
    waveEnergy u t ≤ waveEnergy u 0 * Real.exp ((M + 1) * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact waveEnergy_le_exp_of_decaying h hM ht
  · have hrefl := waveEnergy_le_exp_of_decaying h.comp_timeReflect
      (fun p => hM (timeReflect d p)) (t := -t) (by linarith)
    rw [waveEnergy_comp_timeReflect h.smooth, waveEnergy_comp_timeReflect h.smooth,
      neg_neg, neg_zero] at hrefl
    rw [abs_of_nonpos ht]
    exact hrefl

/-- **A decaying solution with vanishing initial energy vanishes at every time.** -/
theorem eq_zero_of_waveEnergy_zero_of_decaying_all (h : DecayingSolution u V) {M : ℝ}
    (hM : ∀ p, |V p| ≤ M) (h0 : waveEnergy u 0 = 0) (t : ℝ) (x : Fin d → ℝ) : u (t, x) = 0 := by
  rcases le_total 0 t with ht | ht
  · exact eq_zero_of_waveEnergy_zero_of_decaying h hM h0 ht x
  · have h0' : waveEnergy (fun q => u (timeReflect d q)) 0 = 0 := by
      rw [waveEnergy_comp_timeReflect h.smooth, neg_zero]
      exact h0
    have hvan := eq_zero_of_waveEnergy_zero_of_decaying h.comp_timeReflect
      (fun p => hM (timeReflect d p)) h0' (t := -t) (by linarith) x
    have hval : u (timeReflect d ((-t, x) : ℝ × (Fin d → ℝ))) = u (t, x) := by
      rw [timeReflect_apply, neg_neg]
    rw [hval] at hvan
    exact hvan

end Reflection

end GaloisForLFunctions.HTGeometry
