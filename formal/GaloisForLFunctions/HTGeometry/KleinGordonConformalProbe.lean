import GaloisForLFunctions.HTGeometry.KleinGordonFourierDecay

/-!
# The two-species scale law for a static conformal factor

The corpus's two-species reconstruction consumes `OpenProbes` for the conformal potential of a
species. In two dimensions that hypothesis was already discharged by the analytic construction; in
higher dimensions it was the open core of the parent card.

For a conformal factor that does not depend on the time coordinate the hyperbolic construction
discharges it in *every* dimension: the potential of a massive species is then a smooth function of
the spatial point, and smooth static potentials have probes with no further hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace FourierTransform ContDiff

/-! ## The chart of the construction -/

/-- The spatial projection of the chart, as a continuous linear map. -/
noncomputable def kgSpatialCLM (d : ℕ) :
    (Fin (d + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ((2 * Real.pi)⁻¹ : ℝ) •
    (((EuclideanSpace.equiv (Fin d) ℝ).symm : (Fin d → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d)).comp
      (ContinuousLinearMap.pi fun i : Fin d => ContinuousLinearMap.proj i.succ))

theorem kgSpatialCLM_apply (d : ℕ) (y : Fin (d + 1) → ℝ) :
    kgSpatialCLM d y = kgSpatial d y := rfl

theorem contDiff_comp_kgSpatial {d : ℕ} {s : EuclideanSpace ℝ (Fin d) → ℝ}
    (hs : ContDiff ℝ ∞ s) : ContDiff ℝ ∞ fun y : Fin (d + 1) → ℝ => s (kgSpatial d y) := by
  have hfun : (fun y : Fin (d + 1) → ℝ => s (kgSpatial d y))
      = s ∘ (kgSpatialCLM d) := by
    funext y
    rw [Function.comp_apply, kgSpatialCLM_apply]
  rw [hfun]
  exact hs.comp (kgSpatialCLM d).contDiff

/-- The metric chart of the construction: the flat chart with the Minkowski signature. -/
noncomputable def kgChart (d : ℕ) : SmoothMetricChart (d + 1) :=
  (SmoothPseudoMetric.ofSignature (kgEps d) (kgEps_ne_zero d)).chart

theorem kgWaveOp_eq_dalembert (d : ℕ) : kgWaveOp d = (kgChart d).dalembert := rfl

/-! ## Probes for a static conformal factor -/

/-- **The massive species of a static conformal factor has probes on open regions**, in every
dimension. -/
theorem openProbes_conformalPotential_static {d N : ℕ}
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {s : EuclideanSpace ℝ (Fin d) → ℝ} (hs : ContDiff ℝ ∞ s) (massSq : ℝ) :
    OpenProbes (kgChart d).dalembert
      ((kgChart d).conformalPotential 0 massSq fun y : Fin (d + 1) → ℝ => s (kgSpatial d y)) := by
  rw [conformalPotential_weight_zero, ← kgWaveOp_eq_dalembert]
  have hp : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin d) => massSq * Real.exp (2 * s x) :=
    contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul hs))
  exact openProbes_of_static_smooth (N := N) hN hp

/-- **The two-species conformal clock scale law for a static conformal factor, in every
dimension.** The massive species' probes are constructed, not assumed. -/
theorem twoSpecies_scale_reconstruction_static {d N : ℕ}
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {s : EuclideanSpace ℝ (Fin d) → ℝ} (hs : ContDiff ℝ ∞ s) {massSq : ℝ} (hmass : massSq ≠ 0)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (kgChart d).dalembert
        ((kgChart d).conformalPotential 0 massSq fun y => s (kgSpatial d y)) u W →
        SolvesPotentialWaveOn (kgChart d).dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (kgChart d).dalembert
        ((kgChart d).conformalPotential 0 0 fun y => s (kgSpatial d y)) u W →
        SolvesPotentialWaveOn (kgChart d).dalembert other₂ u W)
    (x : Fin (d + 1) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * s (kgSpatial d x)) :=
  scale_reconstruction_of_openProbes (kgChart d) 0 (contDiff_comp_kgSpatial hs) hmass
    (openProbes_conformalPotential_static hN hs massSq) h₁ h₂ x

end GaloisForLFunctions.HTGeometry
