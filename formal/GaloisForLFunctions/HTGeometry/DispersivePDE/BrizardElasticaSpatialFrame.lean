import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSpatialOmega
import Mathlib.Tactic

/-!
# Squared Frenet-frame normalization for the spatial elastica

Section VI of arXiv:2607.21750 defines coefficients `A,B,C` for the conserved vertical vector and
states `A²+B²+C²=1`, using the curvature first integral.  Working directly with squared
coefficients avoids arbitrary square-root choices.  The exact normalization follows algebraically
for every nonzero curvature and scale.  At the initial curvature `κ=k₀`, the three contributions
are `1-Ω²`, `0`, and `Ω²`, identifying the paper's `Ω` as the initial binormal weight.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- The fourth power of the paper's spatial normalization radius `ℛ`. -/
noncomputable def spatialRadiusFourth (k₀ : ℝˣ) (γ ν : ℝ) : ℝ :=
  16 / ((k₀ : ℝ) ^ 4 * ((2 + γ ^ 2) ^ 2 + 4 * ν ^ 2))

theorem spatialRadiusFourth_pos (k₀ : ℝˣ) (γ ν : ℝ) :
    0 < spatialRadiusFourth k₀ γ ν := by
  rw [spatialRadiusFourth]
  exact div_pos (by norm_num)
    (mul_pos ((show Even 4 by decide).pow_pos k₀.ne_zero)
      (spatialOmegaSq_den_pos γ ν))

/-- Squared tangent coefficient from equations (613)--(620). -/
noncomputable def spatialAcoefSq (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) : ℝ :=
  spatialRadiusFourth k₀ γ ν *
    ((κ : ℝ) ^ 2 + γ ^ 2 * (k₀ : ℝ) ^ 2 / 2) ^ 2 / 4

/-- Squared normal coefficient, with `κ'²` replaced by paper equation (59). -/
noncomputable def spatialBcoefSq (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) : ℝ :=
  spatialRadiusFourth k₀ γ ν * curvatureEnergy k₀ γ ν κ

/-- Squared binormal coefficient after substituting `ν=2τ₀/k₀`. -/
noncomputable def spatialCcoefSq (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) : ℝ :=
  spatialRadiusFourth k₀ γ ν * (k₀ : ℝ) ^ 6 * ν ^ 2 / (4 * (κ : ℝ) ^ 2)

/-- Equation `A²+B²+C²=1`, recovered exactly from the curvature first integral. -/
theorem spatial_frame_sq_sum (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) :
    spatialAcoefSq k₀ γ ν κ + spatialBcoefSq k₀ γ ν κ +
      spatialCcoefSq k₀ γ ν κ = 1 := by
  rw [spatialAcoefSq, spatialBcoefSq, spatialCcoefSq, spatialRadiusFourth,
    curvatureEnergy]
  field_simp [k₀.ne_zero, κ.ne_zero, ne_of_gt (spatialOmegaSq_den_pos γ ν)]
  ring

theorem spatialBcoefSq_initial (k₀ : ℝˣ) (γ ν : ℝ) :
    spatialBcoefSq k₀ γ ν k₀ = 0 := by
  rw [spatialBcoefSq, curvatureEnergy]
  field_simp [k₀.ne_zero]
  ring

theorem spatialCcoefSq_initial (k₀ : ℝˣ) (γ ν : ℝ) :
    spatialCcoefSq k₀ γ ν k₀ = spatialOmegaSq γ ν := by
  rw [spatialCcoefSq, spatialRadiusFourth, spatialOmegaSq]
  field_simp [k₀.ne_zero, ne_of_gt (spatialOmegaSq_den_pos γ ν)]
  ring

theorem spatialAcoefSq_initial (k₀ : ℝˣ) (γ ν : ℝ) :
    spatialAcoefSq k₀ γ ν k₀ = 1 - spatialOmegaSq γ ν := by
  rw [spatialAcoefSq, spatialRadiusFourth, one_sub_spatialOmegaSq]
  field_simp [k₀.ne_zero, ne_of_gt (spatialOmegaSq_den_pos γ ν)]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
