import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaCylindricalGap
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTravelingHydrodynamics
import Mathlib.Tactic

/-!
# Exact radial antiderivative

The radial formula in Section VI is certified for every curvature jet staying above the cylindrical
angular floor.  Its derivative is exactly the paper's radial equation, and its square is identified
with the already formalized cylindrical-frame gap.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def radialGap (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) : ℝ :=
  (κ : ℝ) ^ 2 - (k₀ : ℝ) ^ 2 * spatialOmegaSq γ ν

theorem radialGap_eq_curvatureSq_mul_cylindricalGap
    (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) :
    radialGap k₀ γ ν κ =
      (κ : ℝ) ^ 2 * (1 - spatialCcoefSq k₀ γ ν κ) := by
  rw [radialGap, one_sub_spatialCcoefSq]
  field_simp [κ.ne_zero]

theorem radialGap_pos_iff_cylindricalRegular
    (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) :
    0 < radialGap k₀ γ ν κ ↔ 0 < 1 - spatialCcoefSq k₀ γ ν κ := by
  rw [radialGap_eq_curvatureSq_mul_cylindricalGap]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero κ.ne_zero)

theorem radialGap_initial_pos (k₀ : ℝˣ) (γ ν : ℝ) :
    0 < radialGap k₀ γ ν k₀ := by
  rw [show radialGap k₀ γ ν k₀ =
      (k₀ : ℝ) ^ 2 * (1 - spatialOmegaSq γ ν) by
    rw [radialGap]
    ring]
  exact mul_pos (sq_pos_of_ne_zero k₀.ne_zero) (one_sub_spatialOmegaSq_pos γ ν)

/-- Curvature jet whose whole radial square root stays in the regular cylindrical chart. -/
structure RadialCurvatureProfile (k₀ : ℝˣ) (γ ν : ℝ) extends CurvatureProfileJet where
  radialGap_pos : ∀ x : ℝ, 0 < radialGap k₀ γ ν (κ x)

noncomputable def spatialRadiusSq (k₀ : ℝˣ) (γ ν : ℝ) : ℝ :=
  Real.sqrt (spatialRadiusFourth k₀ γ ν)

theorem spatialRadiusSq_pos (k₀ : ℝˣ) (γ ν : ℝ) :
    0 < spatialRadiusSq k₀ γ ν :=
  Real.sqrt_pos.mpr (spatialRadiusFourth_pos k₀ γ ν)

theorem spatialRadiusSq_sq (k₀ : ℝˣ) (γ ν : ℝ) :
    spatialRadiusSq k₀ γ ν ^ 2 = spatialRadiusFourth k₀ γ ν := by
  exact Real.sq_sqrt (spatialRadiusFourth_pos k₀ γ ν).le

noncomputable def radialPosition
    (k₀ : ℝˣ) (γ ν : ℝ) (K : RadialCurvatureProfile k₀ γ ν) (s : ℝ) : ℝ :=
  spatialRadiusSq k₀ γ ν * Real.sqrt (radialGap k₀ γ ν (K.κ s))

noncomputable def radialPositionX
    (k₀ : ℝˣ) (γ ν : ℝ) (K : RadialCurvatureProfile k₀ γ ν) (s : ℝ) : ℝ :=
  spatialRadiusSq k₀ γ ν * (K.κ s : ℝ) * K.κ₁ s /
    Real.sqrt (radialGap k₀ γ ν (K.κ s))

theorem hasDerivAt_radialGap
    (k₀ : ℝˣ) (γ ν : ℝ) (K : RadialCurvatureProfile k₀ γ ν) (s : ℝ) :
    HasDerivAt (fun x => radialGap k₀ γ ν (K.κ x))
      (2 * (K.κ s : ℝ) * K.κ₁ s) s := by
  have h := (K.hasDerivAt s).pow 2 |>.sub_const
    ((k₀ : ℝ) ^ 2 * spatialOmegaSq γ ν)
  apply h.congr_deriv
  ring

/-- The claimed square-root radial solution differentiates to paper equation (93). -/
theorem hasDerivAt_radialPosition
    (k₀ : ℝˣ) (γ ν : ℝ) (K : RadialCurvatureProfile k₀ γ ν) (s : ℝ) :
    HasDerivAt (radialPosition k₀ γ ν K) (radialPositionX k₀ γ ν K s) s := by
  have hg := hasDerivAt_radialGap k₀ γ ν K s
  have hs := hg.sqrt (ne_of_gt (K.radialGap_pos s))
  have h := hs.const_mul (spatialRadiusSq k₀ γ ν)
  apply h.congr_deriv
  rw [radialPositionX]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (K.radialGap_pos s))]

theorem radialPosition_sq
    (k₀ : ℝˣ) (γ ν : ℝ) (K : RadialCurvatureProfile k₀ γ ν) (s : ℝ) :
    radialPosition k₀ γ ν K s ^ 2 =
      spatialRadiusFourth k₀ γ ν * radialGap k₀ γ ν (K.κ s) := by
  rw [radialPosition, mul_pow, spatialRadiusSq_sq,
    Real.sq_sqrt (K.radialGap_pos s).le]

theorem radialPosition_sq_eq_cylindricalGap
    (k₀ : ℝˣ) (γ ν : ℝ) (K : RadialCurvatureProfile k₀ γ ν) (s : ℝ) :
    radialPosition k₀ γ ν K s ^ 2 =
      spatialRadiusFourth k₀ γ ν * (K.κ s : ℝ) ^ 2 *
        (1 - spatialCcoefSq k₀ γ ν (K.κ s)) := by
  rw [radialPosition_sq, radialGap_eq_curvatureSq_mul_cylindricalGap]
  ring

theorem radialGap_torsionless (k₀ : ℝˣ) (γ : ℝ) (κ : ℝˣ) :
    radialGap k₀ γ 0 κ = (κ : ℝ) ^ 2 := by
  have hΩ : spatialOmegaSq γ 0 = 0 := (spatialOmegaSq_eq_zero_iff γ 0).2 rfl
  rw [radialGap, hΩ, mul_zero, sub_zero]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
