import GaloisForLFunctions.HTGeometry.HillSpeedChart

/-!
# The variable-speed chart carries clock probes, and its conformal orbit with them

The probes of the evolution are regular — their partial derivatives are differentiable — so they are
probes of the divergence-form operator of the speed chart, and the corpus's conformal transfer
carries them to every conformal rescaling of that chart.

Two species of different mass then reconstruct the conformal scale: the transferred potentials
differ by the mass difference times the inverse conformal factor, so their difference divided by the
mass difference *is* that factor. This is the two-species scale law on the conformal orbit of a
chart whose propagation speed varies in time.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section SpeedProbes

variable {d : ℕ} {m K C cmin : ℝ} {c dc : ℝ → ℝ}

/-- **The speed chart carries a regular clock probe at every event**, for the constant potential
`-m²`. -/
theorem regularOpenProbes_hillSpeedChart (hs : ContDiff ℝ ∞ c) (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) :
    RegularOpenProbes (hillSpeedChart d c hs).dalembert (fun _ => -(m ^ 2)) := by
  intro y₀
  obtain ⟨W, u, hopen, hmem, hreg, hsolve, hne⟩ :=
    exists_hillProbe_at (C := C) hm hc hcd hcpos hK hC hcmin hclow y₀
  refine ⟨W, hopen, hmem, u, hreg, fun y hy => ?_, hne⟩
  have hdiff : ∀ j : Fin (d + 1), DifferentiableAt ℝ (coordPartial j u) y :=
    fun j => hreg.coord j y hy
  show (hillSpeedChart d c hs).dalembert u y + -(m ^ 2) * u y = 0
  rw [hillSpeedChart_dalembert hs hdiff]
  exact hsolve y hy

/-- **The mass is determined by the probes**: any potential the probes also solve for is the
constant `-m²`. -/
theorem potential_eq_of_hillSpeedChart_probes (hs : ContDiff ℝ ∞ c) (hm : 0 < m)
    (hc : Continuous c) (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r)
    (hK : ∀ r, |dc r| ≤ K * c r) (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin)
    (hclow : ∀ r, cmin ≤ c r) {other : (Fin (d + 1) → ℝ) → ℝ}
    (h : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (hillSpeedChart d c hs).dalembert (fun _ => -(m ^ 2)) u W →
        SolvesPotentialWaveOn (hillSpeedChart d c hs).dalembert other u W) :
    other = fun _ => -(m ^ 2) :=
  potential_eq_of_openProbes
    (regularOpenProbes_hillSpeedChart (C := C) hs hm hc hcd hcpos hK hC hcmin hclow).openProbes h

/-! ## The conformal orbit -/

/-- **Every conformal rescaling of the speed chart carries the probes**, for the transferred
potential. -/
theorem regularOpenProbes_conformalRescale_hillSpeedChart (hs : ContDiff ℝ ∞ c) (hm : 0 < m)
    (hc : Continuous c) (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r)
    (hK : ∀ r, |dc r| ≤ K * c r) (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin)
    (hclow : ∀ r, cmin ≤ c r) {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) :
    RegularOpenProbes ((hillSpeedChart d c hs).conformalRescale sigma hsigma).dalembert
      ((hillSpeedChart d c hs).conformalTransferPotential sigma (fun _ => -(m ^ 2))) :=
  regularOpenProbes_conformalRescale (hillSpeedChart d c hs) hsigma
    (regularOpenProbes_hillSpeedChart (C := C) hs hm hc hcd hcpos hK hC hcmin hclow)

/-- Two species share the geometric part of the transferred potential, so their difference is the
mass difference weighted by the inverse conformal factor. -/
theorem conformalTransferPotential_sub {n : ℕ} (M : SmoothMetricChart n)
    (sigma V₁ V₂ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    M.conformalTransferPotential sigma V₁ x - M.conformalTransferPotential sigma V₂ x
      = Real.exp (-2 * sigma x) * (V₁ x - V₂ x) := by
  rw [SmoothMetricChart.conformalTransferPotential, SmoothMetricChart.conformalTransferPotential]
  ring

/-- **The two-species scale law on the conformal orbit of a variable-speed chart.**

Two clock species of different mass, each measured only through the potentials their probes solve
for, reconstruct the conformal factor of the rescaled speed chart pointwise. -/
theorem twoSpecies_scale_law_hillSpeedChart (hs : ContDiff ℝ ∞ c) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hmass : m₂ ^ 2 - m₁ ^ 2 ≠ 0)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn ((hillSpeedChart d c hs).conformalRescale sigma hsigma).dalembert
          ((hillSpeedChart d c hs).conformalTransferPotential sigma (fun _ => -(m₁ ^ 2))) u W →
        SolvesPotentialWaveOn ((hillSpeedChart d c hs).conformalRescale sigma hsigma).dalembert
          other₁ u W)
    (h₂ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn ((hillSpeedChart d c hs).conformalRescale sigma hsigma).dalembert
          ((hillSpeedChart d c hs).conformalTransferPotential sigma (fun _ => -(m₂ ^ 2))) u W →
        SolvesPotentialWaveOn ((hillSpeedChart d c hs).conformalRescale sigma hsigma).dalembert
          other₂ u W)
    (x : Fin (d + 1) → ℝ) :
    (other₁ x - other₂ x) / (m₂ ^ 2 - m₁ ^ 2) = Real.exp (-2 * sigma x) := by
  have e₁ : other₁ =
      (hillSpeedChart d c hs).conformalTransferPotential sigma (fun _ => -(m₁ ^ 2)) :=
    potential_eq_of_openProbes
      (regularOpenProbes_conformalRescale_hillSpeedChart (C := C) (cmin := cmin) hs hm₁ hc hcd
        hcpos hK hC hcmin hclow hsigma).openProbes h₁
  have e₂ : other₂ =
      (hillSpeedChart d c hs).conformalTransferPotential sigma (fun _ => -(m₂ ^ 2)) :=
    potential_eq_of_openProbes
      (regularOpenProbes_conformalRescale_hillSpeedChart (C := C) (cmin := cmin) hs hm₂ hc hcd
        hcpos hK hC hcmin hclow hsigma).openProbes h₂
  rw [e₁, e₂, conformalTransferPotential_sub]
  show Real.exp (-2 * sigma x) * (-(m₁ ^ 2) - -(m₂ ^ 2)) / (m₂ ^ 2 - m₁ ^ 2)
    = Real.exp (-2 * sigma x)
  have hfac : (-(m₁ ^ 2) - -(m₂ ^ 2)) = m₂ ^ 2 - m₁ ^ 2 := by ring
  rw [hfac, mul_div_assoc, div_self hmass, mul_one]

end SpeedProbes

end GaloisForLFunctions.HTGeometry
