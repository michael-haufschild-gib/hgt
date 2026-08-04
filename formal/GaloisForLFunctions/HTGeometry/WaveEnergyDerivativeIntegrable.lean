import GaloisForLFunctions.HTGeometry.WaveEnergyDerivative

/-!
# Differentiating the energy without compact support

The last use of compact support in the energy layer is the dominating function for differentiation
under the integral sign. For a field vanishing outside a compact set that function is manufactured
from the supremum of the integrand there; for a decaying field — the kind a Fourier synthesis
produces — it has to be supplied. This file records the estimate in that form, which is the general
statement: everything else in the layer already runs on integrability alone.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Dominated

variable {d : ℕ} {u : ℝ × (Fin d → ℝ) → ℝ}

/-- **The energy is differentiable under a dominating hypothesis**, with no support hypothesis. -/
theorem hasDerivAt_waveEnergy_of_dominated (hu : ContDiff ℝ ∞ u) (t : ℝ)
    {bound : (Fin d → ℝ) → ℝ} (hbint : Integrable bound (volume : Measure (Fin d → ℝ)))
    (hb : ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
      ‖waveDirDeriv (timeDir d) (energyDensity u) (s, x)‖ ≤ bound x)
    (hFint : Integrable (fun x : Fin d → ℝ => energyDensity u (t, x))
      (volume : Measure (Fin d → ℝ))) :
    HasDerivAt (waveEnergy u)
      (∫ x : Fin d → ℝ, waveDirDeriv (timeDir d) (energyDensity u) (t, x)) t := by
  have hEcd : ContDiff ℝ ∞ (energyDensity u) := contDiff_energyDensity hu
  have hF'cont : Continuous (waveDirDeriv (timeDir d) (energyDensity u)) :=
    (contDiff_dirDeriv hEcd _).continuous
  have hFmeas : ∀ᶠ s in nhds t, AEStronglyMeasurable
      (fun x : Fin d → ℝ => energyDensity u (s, x)) (volume : Measure (Fin d → ℝ)) := by
    filter_upwards with s
    have hmap : Continuous fun x : Fin d → ℝ => ((s, x) : ℝ × (Fin d → ℝ)) := by fun_prop
    exact (hEcd.continuous.comp hmap).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ => waveDirDeriv (timeDir d) (energyDensity u) (t, x))
      (volume : Measure (Fin d → ℝ)) := by
    have hmap : Continuous fun x : Fin d → ℝ => ((t, x) : ℝ × (Fin d → ℝ)) := by fun_prop
    exact (hF'cont.comp hmap).aestronglyMeasurable
  have hbound : ∀ᵐ x : Fin d → ℝ ∂(volume : Measure (Fin d → ℝ)),
      ∀ s ∈ Metric.ball t 1,
        ‖waveDirDeriv (timeDir d) (energyDensity u) (s, x)‖ ≤ bound x := by
    filter_upwards with x
    intro s hs
    exact hb s hs x
  have hdiff : ∀ᵐ x : Fin d → ℝ ∂(volume : Measure (Fin d → ℝ)), ∀ s ∈ Metric.ball t 1,
      HasDerivAt (fun r : ℝ => energyDensity u (r, x))
        (waveDirDeriv (timeDir d) (energyDensity u) (s, x)) s := by
    filter_upwards with x
    intro s _
    exact hasDerivAt_timeSlice hEcd s x
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s : ℝ => fun x : Fin d → ℝ => energyDensity u (s, x))
    (F' := fun s : ℝ => fun x : Fin d → ℝ =>
      waveDirDeriv (timeDir d) (energyDensity u) (s, x))
    (bound := bound)
    (Metric.ball_mem_nhds t one_pos) hFmeas hFint hF'meas hbound hbint hdiff).2

end Dominated

end GaloisForLFunctions.HTGeometry
