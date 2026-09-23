import GaloisForLFunctions.HTGeometry.HillDrivenProbeAnywhere
import GaloisForLFunctions.HTGeometry.HillRegularProbes

/-!
# The two-species scale law of a variable-speed chart, with a potential

The probes of the driven evolution are regular, so they are probes of the divergence-form operator of
the speed chart, and the corpus's conformal transfer carries them to every conformal rescaling of
that chart.

Two species of different mass sharing one potential then reconstruct the conformal factor: the shared
potential cancels in the difference of the transferred potentials, and what is left is the mass
difference weighted by the inverse conformal factor.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped ContDiff

section ScaleLaw

variable {d K : ℕ}

/-- The same speed, with another mass. -/
noncomputable def HillSpeed.withMass (a : HillSpeed) (m : ℝ) (hm : 0 < m) : HillSpeed :=
  { a with mass := m, mass_pos := hm }

theorem HillSpeed.withMass_speed (a : HillSpeed) (m : ℝ) (hm : 0 < m) :
    (a.withMass m hm).speed = a.speed := rfl

theorem HillSpeed.withMass_mass (a : HillSpeed) (m : ℝ) (hm : 0 < m) :
    (a.withMass m hm).mass = m := rfl

/-- **The speed chart carries the driven probes**, for the potential of a real family. -/
theorem regularOpenProbes_hillSpeedChart_driven
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (hs : ContDiff ℝ ∞ a.speed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (hreal : IsRealFamily b) :
    RegularOpenProbes (hillSpeedChart d a.speed hs).dalembert
      (fun y => hillDrivenChartPotential b y - a.mass ^ (2 : ℕ)) := by
  intro y₀
  obtain ⟨W, u, hWopen, hWmem, hreg, hsolve, hne⟩ := exists_hillDrivenProbe_at hK a b hreal y₀
  refine ⟨W, hWopen, hWmem, u, hreg, fun y hy => ?_, hne⟩
  have hdiff : ∀ j : Fin (d + 1), DifferentiableAt ℝ (coordPartial j u) y :=
    fun j => hreg.coord j y hy
  show (hillSpeedChart d a.speed hs).dalembert u y +
    (hillDrivenChartPotential b y - a.mass ^ (2 : ℕ)) * u y = 0
  rw [hillSpeedChart_dalembert hs hdiff]
  exact hsolve y hy

/-- **Every conformal rescaling of the speed chart carries them too.** -/
theorem regularOpenProbes_conformalRescale_hillSpeedChart_driven
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (hs : ContDiff ℝ ∞ a.speed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (hreal : IsRealFamily b)
    {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) :
    RegularOpenProbes ((hillSpeedChart d a.speed hs).conformalRescale sigma hsigma).dalembert
      ((hillSpeedChart d a.speed hs).conformalTransferPotential sigma
        (fun y => hillDrivenChartPotential b y - a.mass ^ (2 : ℕ))) :=
  regularOpenProbes_conformalRescale (hillSpeedChart d a.speed hs) hsigma
    (regularOpenProbes_hillSpeedChart_driven hK a hs b hreal)

/-- **The two-species scale law on the conformal orbit of a variable-speed chart, with a shared
potential.**

Two clock species of different mass, propagating with the same speed and feeling the same potential,
reconstruct the conformal factor of the rescaled chart pointwise: the potential cancels in the
difference, the masses do not. -/
theorem twoSpecies_scale_law_hillDriven
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (hs : ContDiff ℝ ∞ a.speed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (hreal : IsRealFamily b)
    {m₂ : ℝ} (hm₂ : 0 < m₂) (hmass : m₂ ^ (2 : ℕ) - a.mass ^ (2 : ℕ) ≠ 0)
    {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          ((hillSpeedChart d a.speed hs).conformalRescale sigma hsigma).dalembert
          ((hillSpeedChart d a.speed hs).conformalTransferPotential sigma
            (fun y => hillDrivenChartPotential b y - a.mass ^ (2 : ℕ))) u W →
        SolvesPotentialWaveOn
          ((hillSpeedChart d a.speed hs).conformalRescale sigma hsigma).dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          ((hillSpeedChart d a.speed hs).conformalRescale sigma hsigma).dalembert
          ((hillSpeedChart d a.speed hs).conformalTransferPotential sigma
            (fun y => hillDrivenChartPotential b y - m₂ ^ (2 : ℕ))) u W →
        SolvesPotentialWaveOn
          ((hillSpeedChart d a.speed hs).conformalRescale sigma hsigma).dalembert other₂ u W)
    (x : Fin (d + 1) → ℝ) :
    (other₁ x - other₂ x) / (m₂ ^ (2 : ℕ) - a.mass ^ (2 : ℕ)) = Real.exp (-2 * sigma x) := by
  have hspeed : (a.withMass m₂ hm₂).speed = a.speed := rfl
  have e₁ : other₁ = (hillSpeedChart d a.speed hs).conformalTransferPotential sigma
      (fun y => hillDrivenChartPotential b y - a.mass ^ (2 : ℕ)) :=
    potential_eq_of_openProbes
      (regularOpenProbes_conformalRescale_hillSpeedChart_driven hK a hs b hreal hsigma).openProbes
      h₁
  have hsecond : RegularOpenProbes
      ((hillSpeedChart d a.speed hs).conformalRescale sigma hsigma).dalembert
      ((hillSpeedChart d a.speed hs).conformalTransferPotential sigma
        (fun y => hillDrivenChartPotential b y - m₂ ^ (2 : ℕ))) := by
    have h := regularOpenProbes_conformalRescale_hillSpeedChart_driven hK
      (a.withMass m₂ hm₂) hs b hreal hsigma
    exact h
  have e₂ : other₂ = (hillSpeedChart d a.speed hs).conformalTransferPotential sigma
      (fun y => hillDrivenChartPotential b y - m₂ ^ (2 : ℕ)) :=
    potential_eq_of_openProbes hsecond.openProbes h₂
  rw [e₁, e₂, conformalTransferPotential_sub]
  show Real.exp (-2 * sigma x) *
      ((hillDrivenChartPotential b x - a.mass ^ (2 : ℕ)) - (hillDrivenChartPotential b x - m₂ ^ (2 : ℕ))) /
        (m₂ ^ (2 : ℕ) - a.mass ^ (2 : ℕ)) = Real.exp (-2 * sigma x)
  have hfac : (hillDrivenChartPotential b x - a.mass ^ (2 : ℕ)) -
      (hillDrivenChartPotential b x - m₂ ^ (2 : ℕ)) = m₂ ^ (2 : ℕ) - a.mass ^ (2 : ℕ) := by ring
  rw [hfac, mul_div_assoc, div_self hmass, mul_one]

end ScaleLaw

end GaloisForLFunctions.HTGeometry
