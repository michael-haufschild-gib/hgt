import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherPoleGap
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaGalileanOrbit
import Mathlib.Tactic

/-!
# Galilean propagation of Brizard's breather profiles

The velocity substitution following equation (36) is exactly the existing Brizard Galilean action
at parameter `v=u/2`.  This module transports regularity, magnitude, reflection centers, global
peak bounds, and periodic/Floquet laws to both moving breather families.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Dimensionless velocity convention printed after equation (36). -/
noncomputable def dimensionlessGalileanField (u : ℝ) (q : ℝ → ℝ → ℂ) (τ ξ : ℝ) : ℂ :=
  q τ (ξ - u * τ) * linearPhase (-(u ^ 2) / 4) (u / 2) τ ξ

theorem dimensionlessGalileanField_eq_galileanField (u : ℝ) (q : ℝ → ℝ → ℂ) :
    dimensionlessGalileanField u q = galileanField 1 (u / 2) q := by
  funext τ ξ
  rw [dimensionlessGalileanField, galileanField]
  congr 2 <;> ring

theorem norm_dimensionlessGalileanField (u : ℝ) (q : ℝ → ℝ → ℂ) (τ ξ : ℝ) :
    ‖dimensionlessGalileanField u q τ ξ‖ = ‖q τ (ξ - u * τ)‖ := by
  rw [dimensionlessGalileanField, norm_mul, norm_linearPhase, mul_one]

theorem dimensionlessGalileanField_zero (q : ℝ → ℝ → ℂ) :
    dimensionlessGalileanField 0 q = q := by
  rw [dimensionlessGalileanField_eq_galileanField]
  funext τ ξ
  simpa using galileanField_zero 1 q τ ξ

theorem dimensionlessGalileanField_add (u v : ℝ) (q : ℝ → ℝ → ℂ) :
    dimensionlessGalileanField u (dimensionlessGalileanField v q) =
      dimensionlessGalileanField (u + v) q := by
  rw [dimensionlessGalileanField_eq_galileanField,
    dimensionlessGalileanField_eq_galileanField,
    dimensionlessGalileanField_eq_galileanField]
  funext τ ξ
  rw [galileanField_add]
  congr 3
  ring

noncomputable def movingAkhmedievBreather (u : ℝ) (φ : BreatherAngle) (ξ τ : ℝ) : ℂ :=
  dimensionlessGalileanField u (fun t x => akhmedievBreather φ x t) τ ξ

noncomputable def movingMaBreather (u : ℝ) (φ : MaAngle) (ξ τ : ℝ) : ℂ :=
  dimensionlessGalileanField u (fun t x => maBreather φ x t) τ ξ

theorem norm_movingAkhmedievBreather (u : ℝ) (φ : BreatherAngle) (ξ τ : ℝ) :
    ‖movingAkhmedievBreather u φ ξ τ‖ =
      ‖akhmedievBreather φ (ξ - u * τ) τ‖ := by
  exact norm_dimensionlessGalileanField u _ τ ξ

theorem norm_movingMaBreather (u : ℝ) (φ : MaAngle) (ξ τ : ℝ) :
    ‖movingMaBreather u φ ξ τ‖ = ‖maBreather φ (ξ - u * τ) τ‖ := by
  exact norm_dimensionlessGalileanField u _ τ ξ

theorem movingAkhmedievBreather_regular (u : ℝ) (φ : BreatherAngle) (ξ τ : ℝ) :
    0 < akhmedievDenominator φ (ξ - u * τ) τ :=
  akhmedievDenominator_pos φ _ _

theorem movingMaBreather_regular (u : ℝ) (φ : MaAngle) (ξ τ : ℝ) :
    0 < maDenominator φ (ξ - u * τ) τ :=
  maDenominator_pos φ _ _

/-- Moving Akhmediev magnitude retains its spatial period. -/
theorem norm_movingAkhmedievBreather_periodic (u : ℝ) (φ : BreatherAngle) (ξ τ : ℝ) :
    ‖movingAkhmedievBreather u φ (ξ + akhmedievSpatialPeriod φ) τ‖ =
      ‖movingAkhmedievBreather u φ ξ τ‖ := by
  rw [norm_movingAkhmedievBreather, norm_movingAkhmedievBreather]
  have harg : ξ + akhmedievSpatialPeriod φ - u * τ =
      (ξ - u * τ) + akhmedievSpatialPeriod φ := by ring
  rw [harg, akhmedievBreather_periodic]

/-- The moving Ma magnitude is periodic along the spacetime screw displacement `(uT,T)`. -/
theorem norm_movingMaBreather_screw_periodic (u : ℝ) (φ : MaAngle) (ξ τ : ℝ) :
    ‖movingMaBreather u φ (ξ + u * maTemporalPeriod φ)
        (τ + maTemporalPeriod φ)‖ = ‖movingMaBreather u φ ξ τ‖ := by
  rw [norm_movingMaBreather, norm_movingMaBreather]
  have harg : ξ + u * maTemporalPeriod φ - u * (τ + maTemporalPeriod φ) =
      ξ - u * τ := by ring
  rw [harg, norm_maBreather_periodic]

/-- The Akhmediev magnitude remains mirror-symmetric about moving center `ξ=uτ`. -/
theorem norm_movingAkhmedievBreather_reflection (u : ℝ) (φ : BreatherAngle) (δ τ : ℝ) :
    ‖movingAkhmedievBreather u φ (u * τ - δ) τ‖ =
      ‖movingAkhmedievBreather u φ (u * τ + δ) τ‖ := by
  rw [norm_movingAkhmedievBreather, norm_movingAkhmedievBreather]
  have hleft : u * τ - δ - u * τ = -δ := by ring
  have hright : u * τ + δ - u * τ = δ := by ring
  rw [hleft, hright, norm_akhmedievBreather_space_neg]

/-- The Ma magnitude remains mirror-symmetric about moving center `ξ=uτ`. -/
theorem norm_movingMaBreather_reflection (u : ℝ) (φ : MaAngle) (δ τ : ℝ) :
    ‖movingMaBreather u φ (u * τ - δ) τ‖ =
      ‖movingMaBreather u φ (u * τ + δ) τ‖ := by
  rw [norm_movingMaBreather, norm_movingMaBreather]
  have hleft : u * τ - δ - u * τ = -δ := by ring
  have hright : u * τ + δ - u * τ = δ := by ring
  rw [hleft, hright, norm_maBreather_space_neg]

theorem norm_movingAkhmedievBreather_le_center
    (u : ℝ) (φ : BreatherAngle) (ξ τ : ℝ) :
    ‖movingAkhmedievBreather u φ ξ τ‖ ≤ ‖akhmedievBreather φ 0 0‖ := by
  rw [norm_movingAkhmedievBreather]
  exact norm_akhmedievBreather_le_center φ _ _

theorem norm_movingMaBreather_le_center (u : ℝ) (φ : MaAngle) (ξ τ : ℝ) :
    ‖movingMaBreather u φ ξ τ‖ ≤ ‖maBreather φ 0 0‖ := by
  rw [norm_movingMaBreather]
  exact norm_maBreather_le_center φ _ _

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
