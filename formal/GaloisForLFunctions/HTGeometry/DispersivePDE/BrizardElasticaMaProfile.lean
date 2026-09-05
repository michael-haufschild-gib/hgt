import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAkhmedievProfile
import Mathlib.Tactic

/-!
# Regularity and temporal quasiperiodicity of the printed Ma breather

Paper equation (36) has a positive real denominator for every positive breather angle.  Its
rational core is periodic with the stated period, and its norm is periodic, but the complex field
also contains the carrier `exp(iτ)`.  Consequently the field is only quasiperiodic in general.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open GaloisForLFunctions.HTGeometry.FDNLS

/-- Nondegenerate Ma angle range `φ>0`. -/
abbrev MaAngle := {φ : ℝ // 0 < φ}

noncomputable def maOmega (φ : MaAngle) : ℝ := Real.sinh (2 * (φ : ℝ))

noncomputable def maWaveNumber (φ : MaAngle) : ℝ :=
  Real.sqrt 2 * Real.sinh (φ : ℝ)

noncomputable def maDenominator (φ : MaAngle) (ξ τ : ℝ) : ℝ :=
  Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * ξ) -
    Real.cos (maOmega φ * τ)

/-- Real/imaginary expansion of `cosh φ cosh(pξ)-cos(Ωτ-2iφ)`. -/
noncomputable def maNumerator (φ : MaAngle) (ξ τ : ℝ) : ℂ :=
  ((Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * ξ) -
      Real.cos (maOmega φ * τ) * Real.cosh (2 * (φ : ℝ)) : ℝ) : ℂ) -
    Complex.I *
      ((Real.sin (maOmega φ * τ) * Real.sinh (2 * (φ : ℝ)) : ℝ) : ℂ)

noncomputable def maCore (φ : MaAngle) (ξ τ : ℝ) : ℂ :=
  -(maNumerator φ ξ τ / (maDenominator φ ξ τ : ℂ))

noncomputable def maBreather (φ : MaAngle) (ξ τ : ℝ) : ℂ :=
  maCore φ ξ τ * linearPhase 1 0 τ ξ / (Real.sqrt 2 : ℂ)

theorem maAngle_one_lt_cosh (φ : MaAngle) : 1 < Real.cosh (φ : ℝ) := by
  exact Real.one_lt_cosh.mpr (ne_of_gt φ.property)

/-- Paper equation (36)'s denominator is globally positive. -/
theorem maDenominator_pos (φ : MaAngle) (ξ τ : ℝ) :
    0 < maDenominator φ ξ τ := by
  have hx := Real.one_le_cosh (maWaveNumber φ * ξ)
  have hmul : Real.cosh (φ : ℝ) ≤
      Real.cosh (φ : ℝ) * Real.cosh (maWaveNumber φ * ξ) := by
    simpa using mul_le_mul_of_nonneg_left hx (Real.cosh_pos (φ : ℝ)).le
  have hcos := Real.cos_le_one (maOmega φ * τ)
  rw [maDenominator]
  linarith [maAngle_one_lt_cosh φ]

theorem maOmega_pos (φ : MaAngle) : 0 < maOmega φ := by
  rw [maOmega, Real.sinh_pos_iff]
  linarith [φ.property]

theorem maWaveNumber_pos (φ : MaAngle) : 0 < maWaveNumber φ := by
  rw [maWaveNumber]
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num))
    (Real.sinh_pos_iff.mpr φ.property)

/-- Period of the rational Ma core and of the field magnitude. -/
noncomputable def maTemporalPeriod (φ : MaAngle) : ℝ :=
  2 * Real.pi / maOmega φ

theorem maOmega_mul_period (φ : MaAngle) :
    maOmega φ * maTemporalPeriod φ = 2 * Real.pi := by
  rw [maTemporalPeriod]
  field_simp [ne_of_gt (maOmega_pos φ)]

theorem maDenominator_periodic (φ : MaAngle) (ξ τ : ℝ) :
    maDenominator φ ξ (τ + maTemporalPeriod φ) = maDenominator φ ξ τ := by
  rw [maDenominator, maDenominator]
  have harg : maOmega φ * (τ + maTemporalPeriod φ) =
      maOmega φ * τ + 2 * Real.pi := by
    rw [mul_add, maOmega_mul_period]
  rw [harg, Real.cos_add_two_pi]

theorem maNumerator_periodic (φ : MaAngle) (ξ τ : ℝ) :
    maNumerator φ ξ (τ + maTemporalPeriod φ) = maNumerator φ ξ τ := by
  rw [maNumerator, maNumerator]
  have harg : maOmega φ * (τ + maTemporalPeriod φ) =
      maOmega φ * τ + 2 * Real.pi := by
    rw [mul_add, maOmega_mul_period]
  rw [harg, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem maCore_periodic (φ : MaAngle) (ξ τ : ℝ) :
    maCore φ ξ (τ + maTemporalPeriod φ) = maCore φ ξ τ := by
  rw [maCore, maCore, maNumerator_periodic, maDenominator_periodic]

theorem staggerPhase_add_coordinate (r a b : ℝ) :
    staggerPhase r (a + b) = staggerPhase r a * staggerPhase r b := by
  simp only [staggerPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem linearPhase_coordinate_add (ω k t₁ t₂ x₁ x₂ : ℝ) :
    linearPhase ω k (t₁ + t₂) (x₁ + x₂) =
      linearPhase ω k t₁ x₁ * linearPhase ω k t₂ x₂ := by
  rw [linearPhase, linearPhase, linearPhase, staggerPhase_add_coordinate,
    staggerPhase_add_coordinate]
  ring

/-- Exact Floquet law: one envelope period multiplies the field by its carrier phase. -/
theorem maBreather_quasiperiodic (φ : MaAngle) (ξ τ : ℝ) :
    maBreather φ ξ (τ + maTemporalPeriod φ) =
      maBreather φ ξ τ * linearPhase 1 0 (maTemporalPeriod φ) 0 := by
  rw [maBreather, maBreather, maCore_periodic]
  rw [show ξ = ξ + 0 by ring, linearPhase_coordinate_add]
  ring_nf

/-- Unlike the complex field, the observable magnitude has the stated temporal period. -/
theorem norm_maBreather_periodic (φ : MaAngle) (ξ τ : ℝ) :
    ‖maBreather φ ξ (τ + maTemporalPeriod φ)‖ = ‖maBreather φ ξ τ‖ := by
  rw [maBreather_quasiperiodic, norm_mul, norm_linearPhase, mul_one]

theorem ma_center_real_ratio (φ : MaAngle) :
    -(Real.cosh (φ : ℝ) - Real.cosh (2 * (φ : ℝ))) /
        (Real.cosh (φ : ℝ) - 1) = 1 + 2 * Real.cosh (φ : ℝ) := by
  have hden : Real.cosh (φ : ℝ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (maAngle_one_lt_cosh φ))
  field_simp [hden]
  rw [Real.cosh_two_mul, Real.sinh_sq]
  ring

/-- Exact center value of equation (36), retaining its printed background normalization. -/
theorem maBreather_center (φ : MaAngle) :
    maBreather φ 0 0 =
      (((1 + 2 * Real.cosh (φ : ℝ)) / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [maBreather, maCore]
  simp only [maNumerator, maDenominator, mul_zero, Real.cosh_zero, Real.cos_zero,
    Real.sin_zero, mul_one, zero_mul, sub_zero, linearPhase, staggerPhase, neg_zero,
    Complex.ofReal_zero, Complex.exp_zero, one_mul]
  norm_cast
  rw [← neg_div, ma_center_real_ratio]

theorem norm_maBreather_center (φ : MaAngle) :
    ‖maBreather φ 0 0‖ =
      (1 + 2 * Real.cosh (φ : ℝ)) / Real.sqrt 2 := by
  rw [maBreather_center, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  exact div_pos (by linarith [Real.cosh_pos (φ : ℝ)])
    (Real.sqrt_pos.mpr (by norm_num))

/-- A closed positive angle whose envelope period is exactly `π`. -/
noncomputable def resonantMaAngle : MaAngle :=
  ⟨Real.arsinh 2 / 2, by
    have h : 0 < Real.arsinh (2 : ℝ) := by
      rw [← Real.sinh_pos_iff]
      simp
    positivity⟩

theorem resonantMaOmega : maOmega resonantMaAngle = 2 := by
  rw [maOmega, resonantMaAngle]
  convert Real.sinh_arsinh 2 using 1
  ring_nf

theorem resonantMaTemporalPeriod : maTemporalPeriod resonantMaAngle = Real.pi := by
  rw [maTemporalPeriod, resonantMaOmega]
  ring

theorem resonantMaCarrier :
    linearPhase 1 0 (maTemporalPeriod resonantMaAngle) 0 = -1 := by
  rw [resonantMaTemporalPeriod]
  rw [linearPhase]
  simp only [neg_zero]
  rw [show staggerPhase 0 0 = 1 by simp [staggerPhase], mul_one,
    staggerPhase]
  convert Complex.exp_pi_mul_I using 1
  congr 1
  push_cast
  ring

/-- Closed counterexample to literal field periodicity in the paper's stated Ma angle range. -/
theorem resonantMaBreather_not_periodic :
    maBreather resonantMaAngle 0 (0 + maTemporalPeriod resonantMaAngle) ≠
      maBreather resonantMaAngle 0 0 := by
  have hcenter : maBreather resonantMaAngle 0 0 ≠ 0 := by
    rw [maBreather_center]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (div_pos
      (by linarith [Real.cosh_pos (resonantMaAngle : ℝ)])
      (Real.sqrt_pos.mpr (by norm_num))))
  rw [maBreather_quasiperiodic, resonantMaCarrier]
  intro h
  apply hcenter
  exact CharZero.neg_eq_self_iff.mp (by simpa using h)

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
