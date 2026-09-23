import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAWeights
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalAParameters
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Critical weights at fixed charge and coupling

The limiting positive quadratic root fixes the critical effective-charge
weight. Its coupling shape lies in the already proved critical interval,
so an explicit angle transfers the actual critical state without changing
its conserved electric charge or Gauss–Bonnet coupling.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeACriticalB (φ : ℝ) : ℝ := 12 * (1 + egbFixedChargeAFraction φ)
def egbFixedChargeACriticalDiscriminant (φ : ℝ) : ℝ :=
  egbFixedChargeACriticalB φ ^ (2 : ℕ) + 192 * egbFixedChargeAFraction φ

def egbFixedChargeACriticalWeight (φ : ℝ) : ℝ :=
  4 / (egbFixedChargeACriticalB φ + sqrt (egbFixedChargeACriticalDiscriminant φ))
def egbFixedChargeACriticalCouplingWeight (φ : ℝ) : ℝ :=
  egbFixedChargeAFraction φ * egbFixedChargeACriticalWeight φ

def egbFixedChargeACriticalAngle (φ : ℝ) : ℝ :=
  arcsin (sqrt (egbFixedChargeACriticalCouplingWeight φ / egbCriticalAMaxShape))

theorem egbFixedChargeACriticalB_pos (φ : ℝ) : 0 < egbFixedChargeACriticalB φ := by
  have hρ := (egbFixedChargeAFraction_bounds φ).1
  unfold egbFixedChargeACriticalB
  positivity

theorem egbFixedChargeACriticalDiscriminant_pos (φ : ℝ) : 0 < egbFixedChargeACriticalDiscriminant φ := by
  have hρ := (egbFixedChargeAFraction_bounds φ).1
  have hB := egbFixedChargeACriticalB_pos φ
  unfold egbFixedChargeACriticalDiscriminant
  positivity

theorem egbFixedChargeACriticalWeight_pos (φ : ℝ) : 0 < egbFixedChargeACriticalWeight φ := by
  have hB := egbFixedChargeACriticalB_pos φ
  unfold egbFixedChargeACriticalWeight
  positivity

theorem egbFixedChargeACriticalWeight_quadratic (φ : ℝ) :
    12 * egbFixedChargeAFraction φ * egbFixedChargeACriticalWeight φ ^ (2 : ℕ) +
      6 * (1 + egbFixedChargeAFraction φ) * egbFixedChargeACriticalWeight φ - 1 = 0 := by
  have hB := egbFixedChargeACriticalB_pos φ
  have hs : sqrt (egbFixedChargeACriticalDiscriminant φ) ^ (2 : ℕ) =
      egbFixedChargeACriticalB φ ^ (2 : ℕ) + 192 * egbFixedChargeAFraction φ :=
    sq_sqrt (egbFixedChargeACriticalDiscriminant_pos φ).le
  unfold egbFixedChargeACriticalWeight
  field_simp
  unfold egbFixedChargeACriticalB at hs ⊢
  linear_combination -hs

theorem egbFixedChargeACriticalCouplingWeight_bounds (φ : ℝ) :
    0 ≤ egbFixedChargeACriticalCouplingWeight φ ∧
      egbFixedChargeACriticalCouplingWeight φ ≤ egbFixedChargeACriticalWeight φ := by
  have hs := egbFixedChargeACriticalWeight_pos φ
  have hρ := egbFixedChargeAFraction_bounds φ
  unfold egbFixedChargeACriticalCouplingWeight
  exact ⟨mul_nonneg hρ.1 hs.le, by nlinarith [mul_nonneg (sub_nonneg.mpr hρ.2) hs.le]⟩

/-- The limiting root satisfies the critical effective-charge balance exactly. -/
theorem egbFixedChargeACriticalWeight_balance (φ : ℝ) :
    6 * egbFixedChargeACriticalWeight φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) =
      1 - 6 * egbFixedChargeACriticalCouplingWeight φ := by
  have h := egbFixedChargeACriticalWeight_quadratic φ
  unfold egbFixedChargeACriticalCouplingWeight
  linear_combination h

theorem egbFixedChargeACriticalCouplingWeight_lt_sixth (φ : ℝ) :
    egbFixedChargeACriticalCouplingWeight φ < 1 / 6 := by
  have hs := egbFixedChargeACriticalWeight_pos φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hp : 0 < 6 * egbFixedChargeACriticalWeight φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) := by positivity
  have h := egbFixedChargeACriticalWeight_balance φ
  linarith

theorem egbFixedChargeACriticalCouplingWeight_le_max (φ : ℝ) :
    egbFixedChargeACriticalCouplingWeight φ ≤ egbCriticalAMaxShape := by
  have hb := egbFixedChargeACriticalCouplingWeight_bounds φ
  have hbalance := egbFixedChargeACriticalWeight_balance φ
  have hq : 12 * egbFixedChargeACriticalCouplingWeight φ ^ (2 : ℕ) + 12 * egbFixedChargeACriticalCouplingWeight φ - 1 ≤ 0 := by
    have he : 12 * egbFixedChargeACriticalCouplingWeight φ ^ (2 : ℕ) + 12 * egbFixedChargeACriticalCouplingWeight φ - 1 =
        (egbFixedChargeACriticalCouplingWeight φ - egbFixedChargeACriticalWeight φ) *
          (12 * egbFixedChargeACriticalCouplingWeight φ + 6) := by
      linear_combination hbalance
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb.2) (by linarith [hb.1])
  have hm := egbCriticalAMaxShape_quadratic
  have hmp := egbCriticalAMaxShape_bounds.1
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hp := mul_pos (sub_pos.mpr hlt)
    (show 0 < 12 * (egbFixedChargeACriticalCouplingWeight φ + egbCriticalAMaxShape) + 12 by linarith [hb.1])
  nlinarith

theorem egbFixedChargeACriticalAngle_shape (φ : ℝ) :
    egbCriticalAShape (egbFixedChargeACriticalAngle φ) = egbFixedChargeACriticalCouplingWeight φ := by
  have hm := egbCriticalAMaxShape_bounds.1
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hr : 0 ≤ egbFixedChargeACriticalCouplingWeight φ / egbCriticalAMaxShape := div_nonneg hb hm.le
  have hu : egbFixedChargeACriticalCouplingWeight φ / egbCriticalAMaxShape ≤ 1 :=
    (div_le_one hm).2 (egbFixedChargeACriticalCouplingWeight_le_max φ)
  have hs := sqrt_nonneg (egbFixedChargeACriticalCouplingWeight φ / egbCriticalAMaxShape)
  unfold egbCriticalAShape egbFixedChargeACriticalAngle
  rw [sin_arcsin (by linarith) (sqrt_le_one.mpr hu), sq_sqrt hr]
  field_simp

theorem egbFixedChargeACriticalWeight_formula (φ : ℝ) :
    egbFixedChargeACriticalWeight φ = (1 - 6 * egbFixedChargeACriticalCouplingWeight φ) /
      (6 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  apply (eq_div_iff (show 6 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ≠ 0 by positivity)).2
  linear_combination egbFixedChargeACriticalWeight_balance φ

end GaloisForLFunctions.HTGeometry
