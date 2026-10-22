import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonSpacetimeProbe

/-!
# The two-species scale law for an arbitrary smooth conformal factor

The corpus's two-species reconstruction consumes `OpenProbes` for the conformal potential of a
massive species. With the spacetime cut-off that hypothesis is discharged for *every* smooth
conformal factor, in every dimension and with no time-independence hypothesis: the conformal
potential of a massive species is a smooth function of the event, and every smooth potential has
probes on open regions.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

section Event

variable {d : ℕ}

/-- The event, split into its time coordinate and its point, as a continuous linear map. -/
noncomputable def kgEventCLM (d : ℕ) :
    (Fin (d + 1) → ℝ) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin d) :=
  (ContinuousLinearMap.proj 0).prod (kgSpatialCLM d)

theorem kgEventCLM_apply (y : Fin (d + 1) → ℝ) : kgEventCLM d y = (y 0, kgSpatial d y) := rfl

/-- A smooth function of the event is a smooth function of the chart. -/
theorem contDiff_comp_kgEvent {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y) := by
  have hfun : (fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y)) = P ∘ (kgEventCLM d) := by
    funext y
    rw [Function.comp_apply, kgEventCLM_apply]
  rw [hfun]
  exact hP.comp (kgEventCLM d).contDiff

end Event

/-! ## Probes for an arbitrary conformal factor -/

section Conformal

variable {d N : ℕ}

/-- **The massive species of an arbitrary smooth conformal factor has probes on open regions**, in
every dimension and with no time-independence hypothesis. -/
theorem openProbes_conformalPotential
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {σ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} (hσ : ContDiff ℝ ∞ σ) (massSq : ℝ) :
    OpenProbes (kgChart d).dalembert
      ((kgChart d).conformalPotential 0 massSq
        fun y : Fin (d + 1) → ℝ => σ (y 0, kgSpatial d y)) := by
  rw [conformalPotential_weight_zero, ← kgWaveOp_eq_dalembert]
  have hp : ContDiff ℝ ∞ fun p : ℝ × EuclideanSpace ℝ (Fin d) => massSq * Real.exp (2 * σ p) :=
    contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul hσ))
  exact openProbes_of_smooth_spacetime (N := N) hN hp

/-- **The two-species conformal clock scale law for an arbitrary smooth conformal factor.** The
massive species' probes are constructed, not assumed. -/
theorem twoSpecies_scale_reconstruction
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {σ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (kgChart d).dalembert
        ((kgChart d).conformalPotential 0 massSq fun y => σ (y 0, kgSpatial d y)) u W →
        SolvesPotentialWaveOn (kgChart d).dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (kgChart d).dalembert
        ((kgChart d).conformalPotential 0 0 fun y => σ (y 0, kgSpatial d y)) u W →
        SolvesPotentialWaveOn (kgChart d).dalembert other₂ u W)
    (x : Fin (d + 1) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ (x 0, kgSpatial d x)) :=
  scale_reconstruction_of_openProbes (kgChart d) 0 (contDiff_comp_kgEvent hσ) hmass
    (openProbes_conformalPotential (N := N) hN hσ massSq) h₁ h₂ x

end Conformal

end GaloisForLFunctions.HTGeometry
