import GaloisForLFunctions.HTGeometry.KleinGordonRegularProbes
import GaloisForLFunctions.HTGeometry.ClockRegionalTwoSpecies

/-!
# Clock probes on a conformally flat chart

The hyperbolic construction produces probes on the flat chart. Conjugation by the conformal weight
carries them to any conformal rescaling of it, so every smooth potential on a conformally flat chart
has probes — and with them the two-species conformal scale law on that chart, in every dimension and
with no hypothesis on the conformal factor beyond smoothness.

The class covered is exactly the conformally flat spacetimes: every two-dimensional chart, and in
higher dimensions the cosmological ones.
-/

namespace GaloisForLFunctions.HTGeometry

open ExponentialSecondOrderClockCalculus

open scoped ContDiff

/-! ## The chart split is invertible -/

section Event

variable {d : ℕ}

/-- The inverse of the splitting of an event into its time coordinate and its point. -/
noncomputable def kgEventInvCLM (d : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin d)) →L[ℝ] (Fin (d + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin (d + 1) =>
    Fin.cases (motive := fun _ : Fin (d + 1) => (ℝ × EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ)
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin d)))
      (fun j : Fin d => (2 * Real.pi) •
        ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d)))))
      i

theorem kgEventInvCLM_apply_zero (p : ℝ × EuclideanSpace ℝ (Fin d)) :
    kgEventInvCLM d p 0 = p.1 := rfl

theorem kgEventInvCLM_apply_succ (p : ℝ × EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    kgEventInvCLM d p j.succ = 2 * Real.pi * p.2 j := rfl

theorem kgSpatial_apply (y : Fin (d + 1) → ℝ) (j : Fin d) :
    kgSpatial d y j = (2 * Real.pi)⁻¹ * y j.succ := rfl

/-- The splitting of an event into time and point is inverted by `kgEventInvCLM`. -/
theorem kgEventInvCLM_split (y : Fin (d + 1) → ℝ) :
    kgEventInvCLM d (y 0, kgSpatial d y) = y := by
  funext i
  refine Fin.cases ?_ ?_ i
  · exact kgEventInvCLM_apply_zero (y 0, kgSpatial d y)
  · intro j
    rw [kgEventInvCLM_apply_succ, kgSpatial_apply]
    have hpi : (2 * Real.pi) ≠ 0 := by
      have := Real.pi_pos
      positivity
    field_simp

/-- **Every smooth potential of the chart is a smooth potential of the event split.** -/
theorem contDiff_comp_kgEventInv {V : (Fin (d + 1) → ℝ) → ℝ} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ fun p : ℝ × EuclideanSpace ℝ (Fin d) => V (kgEventInvCLM d p) :=
  hV.comp (kgEventInvCLM d).contDiff

end Event

/-! ## Probes for every smooth potential of the flat chart -/

section FlatChart

variable {d N : ℕ}

/-- **Regular clock probes for every smooth potential on the flat chart**, stated intrinsically: no
product form of the potential is required. -/
theorem regularOpenProbes_of_smooth_chart
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {V : (Fin (d + 1) → ℝ) → ℝ} (hV : ContDiff ℝ ∞ V) :
    RegularOpenProbes (kgWaveOp d) V := by
  have hsplit : V = fun y : Fin (d + 1) → ℝ =>
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => V (kgEventInvCLM d p)) (y 0, kgSpatial d y) := by
    funext y
    show V y = V (kgEventInvCLM d (y 0, kgSpatial d y))
    rw [kgEventInvCLM_split y]
  rw [hsplit]
  exact regularOpenProbes_of_smooth_spacetime hN (contDiff_comp_kgEventInv hV)

end FlatChart

/-! ## Probes on a conformally rescaled chart -/

namespace SmoothMetricChart

section Conformal

variable {d : ℕ} (M : SmoothMetricChart d)

/-- The potential on the base chart that transfers to a prescribed potential on the rescaled one. -/
noncomputable def conformalPullbackPotential (sigma P : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => Real.exp (2 * sigma x) * P x -
    (conformalDimensionWeight d * M.dalembert sigma x +
      conformalDimensionWeight d ^ (2 : ℕ) * M.gradPair sigma sigma x)

theorem conformalTransferPotential_pullback (sigma P : (Fin d → ℝ) → ℝ) :
    M.conformalTransferPotential sigma (M.conformalPullbackPotential sigma P) = P := by
  funext x
  rw [conformalTransferPotential, conformalPullbackPotential]
  have hexp : Real.exp (-2 * sigma x) * Real.exp (2 * sigma x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    Real.exp (-2 * sigma x) *
          (Real.exp (2 * sigma x) * P x -
              (conformalDimensionWeight d * M.dalembert sigma x +
                conformalDimensionWeight d ^ (2 : ℕ) * M.gradPair sigma sigma x) +
            conformalDimensionWeight d * M.dalembert sigma x +
            conformalDimensionWeight d ^ (2 : ℕ) * M.gradPair sigma sigma x)
        = (Real.exp (-2 * sigma x) * Real.exp (2 * sigma x)) * P x := by ring
    _ = P x := by rw [hexp, one_mul]

theorem contDiff_conformalPullbackPotential {sigma P : (Fin d → ℝ) → ℝ}
    (hsigma : ContDiff ℝ ∞ sigma) (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (M.conformalPullbackPotential sigma P) := by
  refine ContDiff.sub ?_ ?_
  · exact (Real.contDiff_exp.comp (contDiff_const.mul hsigma)).mul hP
  · exact (contDiff_const.mul (M.contDiff_dalembert hsigma)).add
      (contDiff_const.mul (M.contDiff_gradPair hsigma hsigma))

end Conformal

end SmoothMetricChart

/-! ## The conformally flat case -/

section ConformallyFlat

variable {d N : ℕ}

/-- **Clock probes for every smooth potential on a conformally flat chart.** -/
theorem regularOpenProbes_conformalRescale_kgChart
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {P : (Fin (d + 1) → ℝ) → ℝ} (hP : ContDiff ℝ ∞ P) :
    RegularOpenProbes ((kgChart d).conformalRescale sigma hsigma).dalembert P := by
  have hbase : RegularOpenProbes (kgChart d).dalembert
      ((kgChart d).conformalPullbackPotential sigma P) := by
    rw [← kgWaveOp_eq_dalembert]
    exact regularOpenProbes_of_smooth_chart (N := N) hN
      ((kgChart d).contDiff_conformalPullbackPotential hsigma hP)
  have htransfer := regularOpenProbes_conformalRescale (kgChart d) hsigma hbase
  rwa [(kgChart d).conformalTransferPotential_pullback sigma P] at htransfer

/-- **The two-species conformal clock scale law on a conformally flat chart.** For an arbitrary
smooth conformal rescaling of the flat chart and an arbitrary smooth conformal factor on it, the
massive species' probes are constructed, not assumed. -/
theorem twoSpecies_scale_reconstruction_conformallyFlat
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {tau : (Fin (d + 1) → ℝ) → ℝ} (htau : ContDiff ℝ ∞ tau)
    {massSq : ℝ} (hmass : massSq ≠ 0)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn ((kgChart d).conformalRescale sigma hsigma).dalembert
        (((kgChart d).conformalRescale sigma hsigma).conformalPotential 0 massSq tau) u W →
        SolvesPotentialWaveOn ((kgChart d).conformalRescale sigma hsigma).dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn ((kgChart d).conformalRescale sigma hsigma).dalembert
        (((kgChart d).conformalRescale sigma hsigma).conformalPotential 0 0 tau) u W →
        SolvesPotentialWaveOn ((kgChart d).conformalRescale sigma hsigma).dalembert other₂ u W)
    (x : Fin (d + 1) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * tau x) := by
  have hpot : ContDiff ℝ ∞
      (((kgChart d).conformalRescale sigma hsigma).conformalPotential 0 massSq tau) := by
    rw [conformalPotential_weight_zero]
    exact contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul htau))
  exact scale_reconstruction_of_openProbes ((kgChart d).conformalRescale sigma hsigma) 0 htau hmass
    (regularOpenProbes_conformalRescale_kgChart (N := N) hN hsigma hpot).openProbes h₁ h₂ x

end ConformallyFlat

end GaloisForLFunctions.HTGeometry
