import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceRadialUnit

/-! Exact horizon-factor transport to the original tortoise exponential. -/
open Set
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section

def horizonCoordinate (t : ℝ) : ℝ := 1-radialUnit t^(2 : ℕ)

theorem horizonCoordinate_interior (t : ℝ) (ht : t < 0) : horizonCoordinate t ∈ Ioo 0 1 := by
  have hu := radialUnit_bounds t ht
  unfold horizonCoordinate
  constructor <;> nlinarith

/-- The compact horizon coordinate carries the exact original tortoise exponential. -/
theorem horizonCoordinate_factor (t : ℝ) :
    horizonCoordinate t = (Real.exp t*(1+radialUnit t))^(2 : ℕ) := by
  have hc : Real.cosh t ≠ 0 := ne_of_gt (Real.cosh_pos t)
  have he : Real.exp t*(Real.cosh t-Real.sinh t) = 1 := by
    rw [Real.cosh_sub_sinh,← Real.exp_add]
    simp
  have hp : Real.exp t*(1+radialUnit t) = (Real.cosh t)⁻¹ := by
    unfold radialUnit
    field_simp
    nlinarith [he]
  rw [hp]
  unfold horizonCoordinate radialUnit
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

/-- The actual power factor is an exponential in tortoise time times a compact-radius factor. -/
theorem horizonPower_tortoise (w : ℂ) (t : ℝ) (ht : t < 0) :
    power (w/2) (horizonCoordinate t) =
      Complex.exp (w*(t:ℂ))*power w (1+radialUnit t) := by
  have hz := (horizonCoordinate_interior t ht).1
  have hu := radialUnit_add_one_pos t
  have hlog : Real.log (horizonCoordinate t) = 2*t+2*Real.log (1+radialUnit t) := by
    rw [horizonCoordinate_factor,Real.log_pow,
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hu),Real.log_exp]
    ring
  unfold power
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hu)),
    ← Complex.ofReal_log hz.le,← Complex.ofReal_log hu.le,← Complex.exp_add,hlog]
  congr 1
  push_cast
  ring

end
end RHTower.D4BMJointSource
