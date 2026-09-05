import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaFrenetConservation
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTravelingPolar
import Mathlib.Tactic

/-!
# Stationary elastica compile to traveling NLS waves

This is the formal bridge asserted in paper Section IV.  A stationary Frenet elastica, a Hasimoto
phase with slope `c/(2D) + τ`, and the selected multiplier
`lambdaScale = -c²/(2D²)` automatically satisfy both scalar polar NLS balances.  The generic polar
compiler then produces an exact complex NLS solution.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Closed geometric and phase data for the paper's traveling Hasimoto construction. -/
structure HasimotoTravelingElasticaData
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  geometry : StationaryElasticaData V
  dispersion : ℝˣ
  speed : ℝ
  phase : ℝ → ℝ
  phase₁ : ℝ → ℝ
  phase₂ : ℝ → ℝ
  phase_deriv : ∀ s, HasDerivAt phase (phase₁ s) s
  phase₁_deriv : ∀ s, HasDerivAt phase₁ (phase₂ s) s
  phase_slope : ∀ s,
    phase₁ s = speed / (2 * (dispersion : ℝ)) + geometry.torsion s
  multiplier_selection :
    elasticaLambdaScale geometry = -speed ^ 2 / (2 * (dispersion : ℝ) ^ 2)

/-- Differentiating the Hasimoto phase law leaves exactly the torsion derivative. -/
theorem hasimoto_phase₂_eq_torsion₁
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : HasimotoTravelingElasticaData V) (s : ℝ) :
    H.phase₂ s = H.geometry.torsion₁ s := by
  have hslope : H.phase₁ = fun x =>
      H.speed / (2 * (H.dispersion : ℝ)) + H.geometry.torsion x := by
    funext x
    exact H.phase_slope x
  have hleft := H.phase₁_deriv s
  rw [hslope] at hleft
  have hright : HasDerivAt
      (fun x => H.speed / (2 * (H.dispersion : ℝ)) + H.geometry.torsion x)
      (H.geometry.torsion₁ s) s :=
    (H.geometry.torsion_deriv s).const_add _
  exact hleft.unique hright

/-- Forget geometry and retain the amplitude/phase jet used by the polar compiler. -/
noncomputable def HasimotoTravelingElasticaData.toPolarProfile
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : HasimotoTravelingElasticaData V) : TravelingPolarProfile where
  amplitude := H.geometry.curvature
  amplitude₁ := H.geometry.curvature₁
  amplitude₂ := H.geometry.curvature₂
  phase := H.phase
  phase₁ := H.phase₁
  phase₂ := H.phase₂
  amplitude_deriv := H.geometry.curvature_deriv
  amplitude₁_deriv := H.geometry.curvature₁_deriv
  phase_deriv := H.phase_deriv
  phase₁_deriv := H.phase₁_deriv

/-- Elastica normal equation and selected multiplier imply the real NLS balance. -/
theorem hasimoto_real_balance
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : HasimotoTravelingElasticaData V) (s : ℝ) :
    H.speed * H.geometry.curvature s * H.phase₁ s +
      (H.dispersion : ℝ) *
        (H.geometry.curvature₂ s -
          H.geometry.curvature s * H.phase₁ s ^ 2 +
          H.geometry.curvature s ^ 3 / 2) = 0 := by
  have hnormal := H.geometry.normal_euler s
  have hlagrange := stationaryElastica_lagrange_eq H.geometry s
  rw [hlagrange, H.multiplier_selection] at hnormal
  rw [H.phase_slope s]
  field_simp [H.dispersion.ne_zero] at hnormal ⊢
  nlinarith

/-- Elastica binormal equation implies the imaginary NLS balance. -/
theorem hasimoto_imaginary_balance
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : HasimotoTravelingElasticaData V) (s : ℝ) :
    -H.speed * H.geometry.curvature₁ s +
      (H.dispersion : ℝ) *
        (2 * H.geometry.curvature₁ s * H.phase₁ s +
          H.geometry.curvature s * H.phase₂ s) = 0 := by
  rw [H.phase_slope s, hasimoto_phase₂_eq_torsion₁ H s]
  have heuler := H.geometry.binormal_euler s
  field_simp [H.dispersion.ne_zero]
  linear_combination (H.dispersion : ℝ) * heuler

/-- Central Section IV bridge packaged for the generic polar NLS compiler. -/
noncomputable def HasimotoTravelingElasticaData.toPolarNLSData
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : HasimotoTravelingElasticaData V) : TravelingPolarNLSData where
  toTravelingPolarProfile := H.toPolarProfile
  dispersion := H.dispersion
  speed := H.speed
  real_balance := hasimoto_real_balance H
  imaginary_balance := hasimoto_imaginary_balance H

/-- Every selected stationary elastica is an exact traveling solution of Brizard's NLS. -/
theorem hasimotoTravelingElastica_solves
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : HasimotoTravelingElasticaData V) :
    SolvesNLS (H.dispersion : ℝ)
      (travelingPolarJet H.toPolarProfile H.speed) :=
  travelingPolarNLSData_solves H.toPolarNLSData

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
