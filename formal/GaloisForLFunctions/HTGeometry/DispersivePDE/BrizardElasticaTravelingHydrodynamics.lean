import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaHydrodynamics
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTravelingPhase
import Mathlib.Tactic

/-!
# Traveling elastica hydrodynamics and the missing boost current

The hydrodynamics discussion in arXiv:2607.21750 writes a traveling density `ρ(s-ct)` but uses
only `u=2Dτ`.  Its phase equation actually gives `u=c+2Dτ`.  For an arbitrary certified nonzero
curvature profile, this module proves that the additional flux `cρ` cancels time transport exactly.
It also records the residual left by the unboosted current.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Nonvanishing curvature profile with a certified first derivative. -/
structure CurvatureProfileJet where
  κ : ℝ → ℝˣ
  κ₁ : ℝ → ℝ
  hasDerivAt : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (κ y : ℝ)) (κ₁ x) x

noncomputable def travelingDensity
    (K : CurvatureProfileJet) (c t s : ℝ) : ℝ :=
  (K.κ (s - c * t) : ℝ) ^ 2

noncomputable def travelingDensityT
    (K : CurvatureProfileJet) (c t s : ℝ) : ℝ :=
  -2 * c * (K.κ (s - c * t) : ℝ) * K.κ₁ (s - c * t)

noncomputable def travelingDensityX
    (K : CurvatureProfileJet) (c t s : ℝ) : ℝ :=
  2 * (K.κ (s - c * t) : ℝ) * K.κ₁ (s - c * t)

theorem hasDerivAt_travelingDensity_time
    (K : CurvatureProfileJet) (c t s : ℝ) :
    HasDerivAt (fun r : ℝ => travelingDensity K c r s)
      (travelingDensityT K c t s) t := by
  have hinner : HasDerivAt (fun r : ℝ => s - c * r) (-c) t := by
    simpa using! ((hasDerivAt_id t).const_mul c).const_sub s
  have hκ := (K.hasDerivAt (s - c * t)).scomp t hinner
  have hsq := hκ.pow 2
  apply hsq.congr_deriv
  rw [travelingDensityT]
  simp only [Function.comp_apply, smul_eq_mul]
  ring

theorem hasDerivAt_travelingDensity_space
    (K : CurvatureProfileJet) (c t s : ℝ) :
    HasDerivAt (travelingDensity K c t) (travelingDensityX K c t s) s := by
  have hinner : HasDerivAt (fun y : ℝ => y - c * t) 1 s := by
    simpa using (hasDerivAt_id s).sub_const (c * t)
  have hκ := (K.hasDerivAt (s - c * t)).scomp s hinner
  have hsq := hκ.pow 2
  apply hsq.congr_deriv
  rw [travelingDensityX]
  simp only [Function.comp_apply, one_smul]
  ring

/-- Velocity dictated by the full traveling phase: drift plus Hasimoto torsion velocity. -/
noncomputable def travelingHydroVelocity
    (D k₀ : ℝ) (τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  c + fluidSpeed D k₀ τ₀ (K.κ (s - c * t))

noncomputable def travelingMassCurrent
    (D k₀ : ℝ) (τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  travelingDensity K c t s * travelingHydroVelocity D k₀ τ₀ c K t s

/-- Full current is transported density plus the conserved torsion flux. -/
theorem travelingMassCurrent_eq
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    travelingMassCurrent D k₀ τ₀ c K t s =
      c * travelingDensity K c t s + 2 * D * k₀ ^ 2 * τ₀ := by
  rw [travelingMassCurrent, travelingHydroVelocity]
  have hflux := density_mul_fluidSpeed D k₀ τ₀ (K.κ (s - c * t))
  simp only [travelingDensity, density] at hflux ⊢
  linear_combination hflux

theorem hasDerivAt_travelingMassCurrent_space
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    HasDerivAt (travelingMassCurrent D k₀ τ₀ c K t)
      (c * travelingDensityX K c t s) s := by
  have hfun : travelingMassCurrent D k₀ τ₀ c K t =
      fun y : ℝ => c * travelingDensity K c t y + 2 * D * k₀ ^ 2 * τ₀ := by
    funext y
    exact travelingMassCurrent_eq D k₀ τ₀ c K t y
  rw [hfun]
  exact (hasDerivAt_travelingDensity_space K c t s).const_mul c |>.add_const _

/-- Correct traveling continuity law with actual derivative certificates. -/
theorem travelingContinuityEquation
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    travelingDensityT K c t s + c * travelingDensityX K c t s = 0 ∧
      HasDerivAt (fun r : ℝ => travelingDensity K c r s)
        (travelingDensityT K c t s) t ∧
      HasDerivAt (travelingMassCurrent D k₀ τ₀ c K t)
        (c * travelingDensityX K c t s) s := by
  exact ⟨by rw [travelingDensityT, travelingDensityX]; ring,
    hasDerivAt_travelingDensity_time K c t s,
    hasDerivAt_travelingMassCurrent_space D k₀ τ₀ c K t s⟩

/-- Current obtained by omitting the traveling drift `c`. -/
noncomputable def unboostedMassCurrent
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) : ℝ :=
  travelingDensity K c t s * fluidSpeed D k₀ τ₀ (K.κ (s - c * t))

theorem unboostedMassCurrent_eq
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    unboostedMassCurrent D k₀ τ₀ c K t s = 2 * D * k₀ ^ 2 * τ₀ := by
  simpa [unboostedMassCurrent, travelingDensity, density] using
    density_mul_fluidSpeed D k₀ τ₀ (K.κ (s - c * t))

theorem hasDerivAt_unboostedMassCurrent_space
    (D k₀ τ₀ c : ℝ) (K : CurvatureProfileJet) (t s : ℝ) :
    HasDerivAt (unboostedMassCurrent D k₀ τ₀ c K t) 0 s := by
  have hfun : unboostedMassCurrent D k₀ τ₀ c K t =
      fun _ : ℝ => 2 * D * k₀ ^ 2 * τ₀ := by
    funext y
    exact unboostedMassCurrent_eq D k₀ τ₀ c K t y
  rw [hfun]
  exact hasDerivAt_const s _

/-- Exact continuity residual caused by omitting the drift flux. -/
theorem unboostedContinuityResidual
    (K : CurvatureProfileJet) (c t s : ℝ) :
    travelingDensityT K c t s + 0 = -c * travelingDensityX K c t s := by
  rw [travelingDensityT, travelingDensityX]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
