import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaMaProfile
import Mathlib.Tactic

/-!
# Exact reflection symmetries of Brizard's breather profiles

The displayed Akhmediev and Ma profiles are mirror-symmetric about their localization centers.
Spatial reflection fixes each full field.  Time reflection is complex conjugation, so magnitude is
even in both coordinates despite the carrier phase.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open GaloisForLFunctions.HTGeometry.FDNLS

theorem linearPhase_one_zero_time_neg (τ ξ : ℝ) :
    linearPhase 1 0 (-τ) ξ = (starRingEnd ℂ) (linearPhase 1 0 τ ξ) := by
  simp only [linearPhase, staggerPhase, map_mul, map_neg, ← Complex.exp_conj,
    Complex.conj_I, Complex.conj_ofReal]
  congr 1 <;> norm_num

theorem akhmedievDenominator_space_neg (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievDenominator φ (-ξ) τ = akhmedievDenominator φ ξ τ := by
  simp [akhmedievDenominator, Real.cos_neg]

theorem akhmedievDenominator_time_neg (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievDenominator φ ξ (-τ) = akhmedievDenominator φ ξ τ := by
  simp [akhmedievDenominator, Real.cosh_neg]

theorem akhmedievNumerator_space_neg (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievNumerator φ (-ξ) τ = akhmedievNumerator φ ξ τ := by
  simp [akhmedievNumerator, Real.cos_neg]

theorem akhmedievNumerator_time_neg (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievNumerator φ ξ (-τ) =
      (starRingEnd ℂ) (akhmedievNumerator φ ξ τ) := by
  simp only [akhmedievNumerator, mul_neg, Real.cosh_neg, Real.sinh_neg,
    map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem akhmedievBreather_space_neg (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievBreather φ (-ξ) τ = akhmedievBreather φ ξ τ := by
  rw [akhmedievBreather, akhmedievBreather, akhmedievNumerator_space_neg,
    akhmedievDenominator_space_neg]
  simp [linearPhase, staggerPhase]

theorem akhmedievBreather_time_neg (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievBreather φ ξ (-τ) =
      (starRingEnd ℂ) (akhmedievBreather φ ξ τ) := by
  rw [akhmedievBreather, akhmedievBreather, akhmedievNumerator_time_neg,
    akhmedievDenominator_time_neg, linearPhase_one_zero_time_neg]
  simp only [map_div₀, map_mul, map_neg, Complex.conj_ofReal]

theorem norm_akhmedievBreather_space_neg (φ : BreatherAngle) (ξ τ : ℝ) :
    ‖akhmedievBreather φ (-ξ) τ‖ = ‖akhmedievBreather φ ξ τ‖ := by
  rw [akhmedievBreather_space_neg]

theorem norm_akhmedievBreather_time_neg (φ : BreatherAngle) (ξ τ : ℝ) :
    ‖akhmedievBreather φ ξ (-τ)‖ = ‖akhmedievBreather φ ξ τ‖ := by
  rw [akhmedievBreather_time_neg]
  exact Complex.norm_conj _

theorem maDenominator_space_neg (φ : MaAngle) (ξ τ : ℝ) :
    maDenominator φ (-ξ) τ = maDenominator φ ξ τ := by
  simp [maDenominator, Real.cosh_neg]

theorem maDenominator_time_neg (φ : MaAngle) (ξ τ : ℝ) :
    maDenominator φ ξ (-τ) = maDenominator φ ξ τ := by
  simp [maDenominator, Real.cos_neg]

theorem maNumerator_space_neg (φ : MaAngle) (ξ τ : ℝ) :
    maNumerator φ (-ξ) τ = maNumerator φ ξ τ := by
  simp [maNumerator, Real.cosh_neg]

theorem maNumerator_time_neg (φ : MaAngle) (ξ τ : ℝ) :
    maNumerator φ ξ (-τ) = (starRingEnd ℂ) (maNumerator φ ξ τ) := by
  simp only [maNumerator, mul_neg, Real.cos_neg, Real.sin_neg,
    map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem maBreather_space_neg (φ : MaAngle) (ξ τ : ℝ) :
    maBreather φ (-ξ) τ = maBreather φ ξ τ := by
  rw [maBreather, maBreather, maCore, maCore, maNumerator_space_neg,
    maDenominator_space_neg]
  simp [linearPhase, staggerPhase]

theorem maBreather_time_neg (φ : MaAngle) (ξ τ : ℝ) :
    maBreather φ ξ (-τ) = (starRingEnd ℂ) (maBreather φ ξ τ) := by
  rw [maBreather, maBreather, maCore, maCore, maNumerator_time_neg,
    maDenominator_time_neg, linearPhase_one_zero_time_neg]
  simp only [map_div₀, map_mul, map_neg, Complex.conj_ofReal]

theorem norm_maBreather_space_neg (φ : MaAngle) (ξ τ : ℝ) :
    ‖maBreather φ (-ξ) τ‖ = ‖maBreather φ ξ τ‖ := by
  rw [maBreather_space_neg]

theorem norm_maBreather_time_neg (φ : MaAngle) (ξ τ : ℝ) :
    ‖maBreather φ ξ (-τ)‖ = ‖maBreather φ ξ τ‖ := by
  rw [maBreather_time_neg]
  exact Complex.norm_conj _

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
