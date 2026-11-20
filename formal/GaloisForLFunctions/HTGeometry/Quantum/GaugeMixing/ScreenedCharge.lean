import GaloisForLFunctions.HTGeometry.PlasmaDischargePhotoelectricLaws
import Mathlib.Analysis.Real.Sqrt

/-!
# Kinetic mixing and momentum-dependent charge

Naydenov (arXiv:2611.22807, Section 2.1) identifies the millicharge with
the visible projection of the dark source. Completing the two-field
quadratic form gives the exact projection at positive squared momentum,
including the suppression from the dark mass term.
-/

namespace GaloisForLFunctions.HTGeometry.GaugeMixing

noncomputable section

abbrev Mixing := Set.Ioo (-1 : ℝ) 1
abbrev MomentumSq := Set.Ioi (0 : ℝ)
abbrev MassSq := Set.Ici (0 : ℝ)

/-- Momentum-space factor that suppresses a massive dark source. -/
def momentumFraction (p : MomentumSq) (m : MassSq) : ℝ :=
  (p : ℝ) / ((p : ℝ) + (m : ℝ))

private theorem scale_pos (p : MomentumSq) (m : MassSq) : 0 < (p : ℝ) + (m : ℝ) :=
  add_pos_of_pos_of_nonneg p.2 m.2

theorem momentumFraction_pos (p : MomentumSq) (m : MassSq) :
    0 < momentumFraction p m :=
  div_pos p.2 (scale_pos p m)

theorem momentumFraction_le_one (p : MomentumSq) (m : MassSq) :
    momentumFraction p m ≤ 1 := by
  rw [momentumFraction, div_le_iff₀ (scale_pos p m), one_mul]
  linarith only [show 0 ≤ (m : ℝ) from m.2]

theorem momentumFraction_eq_one_iff (p : MomentumSq) (m : MassSq) :
    momentumFraction p m = 1 ↔ (m : ℝ) = 0 := by
  rw [momentumFraction, div_eq_iff (scale_pos p m).ne', one_mul]
  constructor <;> intro h <;> linarith only [h]

/-- Shift of the dark field by the visible field in the diagonal coordinates. -/
def screenedMixing (e : Mixing) (p : MomentumSq) (m : MassSq) : ℝ :=
  (e : ℝ) * momentumFraction p m

/-- Schur complement of the dark mode in the kinetic and mass quadratic form. -/
def visibleCoefficient (e : Mixing) (p : MomentumSq) (m : MassSq) : ℝ :=
  (p : ℝ) * (1 - (e : ℝ) * screenedMixing e p m)

/-- Completing the square preserves a strictly positive visible response. -/
theorem visibleCoefficient_lower (e : Mixing) (p : MomentumSq) (m : MassSq) :
    0 < (p : ℝ) * (1 - (e : ℝ)^2) ∧
      (p : ℝ) * (1 - (e : ℝ)^2) ≤ visibleCoefficient e p m := by
  have hlo : 0 < 1 + (e : ℝ) := by linarith only [show -1 < (e : ℝ) from e.2.1]
  have hhi : 0 < 1 - (e : ℝ) := sub_pos.mpr e.2.2
  have hpos : 0 < 1 - (e : ℝ)^2 := by nlinarith only [mul_pos hhi hlo]
  refine ⟨mul_pos p.2 hpos, ?_⟩
  unfold visibleCoefficient screenedMixing
  apply mul_le_mul_of_nonneg_left _ p.2.le
  have hs := mul_le_mul_of_nonneg_left (momentumFraction_le_one p m) (sq_nonneg (e : ℝ))
  nlinarith only [hs]

/-- The two-field quadratic form at a single squared momentum. -/
def modeEnergy (e : Mixing) (p : MomentumSq) (m : MassSq) (x y : ℝ) : ℝ :=
  (p : ℝ) * (x^2 + y^2 - 2 * (e : ℝ) * x * y) + (m : ℝ) * y^2

theorem modeEnergy_eq_completedSquare
    (e : Mixing) (p : MomentumSq) (m : MassSq) (x y : ℝ) :
    modeEnergy e p m x y = visibleCoefficient e p m * x^2 +
      ((p : ℝ) + (m : ℝ)) * (y - screenedMixing e p m * x)^2 := by
  unfold modeEnergy visibleCoefficient screenedMixing momentumFraction
  field_simp [(scale_pos p m).ne']
  ring

/-- The normalized visible and dark amplitudes have unit kinetic coefficients. -/
def canonicalFields (e : Mixing) (p : MomentumSq) (m : MassSq) (x y : ℝ) : ℝ × ℝ :=
  (Real.sqrt (visibleCoefficient e p m) * x,
    Real.sqrt ((p : ℝ) + (m : ℝ)) * (y - screenedMixing e p m * x))

theorem modeEnergy_eq_canonicalFields (e : Mixing) (p : MomentumSq) (m : MassSq) (x y : ℝ) :
    modeEnergy e p m x y =
      (canonicalFields e p m x y).1^2 + (canonicalFields e p m x y).2^2 := by
  rw [modeEnergy_eq_completedSquare]
  simp only [canonicalFields, mul_pow, Real.sq_sqrt (scale_pos p m).le,
    Real.sq_sqrt ((visibleCoefficient_lower e p m).1.trans_le
      (visibleCoefficient_lower e p m).2).le]

/-- Coupling of a source to the canonically normalized visible amplitude. -/
def visibleCoupling (e : Mixing) (p : MomentumSq) (m : MassSq) (g h : ℝ) : ℝ :=
  (g + h * screenedMixing e p m) / Real.sqrt (visibleCoefficient e p m)

/-- The source term in the original basis is exactly the sum of its
couplings to the canonically normalized fields. -/
theorem source_eq_canonicalFields (e : Mixing) (p : MomentumSq) (m : MassSq)
    (g h x y : ℝ) :
    g * x + h * y =
      visibleCoupling e p m g h * (canonicalFields e p m x y).1 +
      (h / Real.sqrt ((p : ℝ) + (m : ℝ))) * (canonicalFields e p m x y).2 := by
  have hA : 0 < visibleCoefficient e p m :=
    (visibleCoefficient_lower e p m).1.trans_le (visibleCoefficient_lower e p m).2
  simp only [visibleCoupling, canonicalFields]
  field_simp [(Real.sqrt_pos.mpr hA).ne', (Real.sqrt_pos.mpr (scale_pos p m)).ne']
  ring

/-- Dividing the induced visible coupling by the visible reference charge
cancels their common field normalization. -/
theorem chargeRatio_eq_screened (e : Mixing) (p : MomentumSq) (m : MassSq)
    (g : Set.Ioi (0 : ℝ)) (h : ℝ) :
    visibleCoupling e p m 0 h / visibleCoupling e p m g 0 =
      momentumFraction p m * ((e : ℝ) * h / (g : ℝ)) := by
  have hA : 0 < visibleCoefficient e p m :=
    (visibleCoefficient_lower e p m).1.trans_le (visibleCoefficient_lower e p m).2
  simp only [visibleCoupling, screenedMixing, zero_mul, add_zero, zero_add]
  field_simp [g.2.ne', (Real.sqrt_pos.mpr hA).ne']
  ring

/-- A nonzero mass strictly suppresses a nonzero induced charge. -/
theorem chargeRatio_abs_eq_unscreened_iff (e : Mixing) (p : MomentumSq) (m : MassSq)
    (g : Set.Ioi (0 : ℝ)) (h : ℝ) :
    |visibleCoupling e p m 0 h / visibleCoupling e p m g 0| =
        |(e : ℝ) * h / (g : ℝ)| ↔ (m : ℝ) = 0 ∨ (e : ℝ) * h = 0 := by
  rw [chargeRatio_eq_screened, abs_mul, abs_of_pos (momentumFraction_pos p m)]
  set q := (e : ℝ) * h / (g : ℝ) with hq
  by_cases hz : q = 0
  · have hh : (e : ℝ) * h = 0 := (div_eq_zero_iff.mp (hq ▸ hz)).resolve_right g.2.ne'
    simp only [hz, abs_zero, mul_zero, hh, or_true]
  · have hh : (e : ℝ) * h ≠ 0 := by
      intro h'
      apply hz
      rw [hq, h', zero_div]
    simp only [hh, or_false]
    rw [← momentumFraction_eq_one_iff p m]
    constructor
    · intro he
      apply mul_right_cancel₀ (abs_ne_zero.mpr hz)
      simpa only [one_mul] using he
    · intro he
      rw [he, one_mul]

/-- Inserting the screened charge magnitude rescales the corpus's pair length
by the same momentum fraction. -/
theorem bjerrumPairLength_screened (p : MomentumSq) (m : MassSq)
    (q r d T : ℝ) :
    bjerrumPairLength q (r + Real.log (momentumFraction p m)) d T =
      momentumFraction p m * bjerrumPairLength q r d T := by
  unfold bjerrumPairLength
  rw [show q + (r + Real.log (momentumFraction p m)) - d - T =
    Real.log (momentumFraction p m) + (q + r - d - T) by ring,
    Real.exp_add, Real.exp_log (momentumFraction_pos p m)]

#print axioms visibleCoefficient_lower
#print axioms modeEnergy_eq_canonicalFields
#print axioms source_eq_canonicalFields
#print axioms chargeRatio_eq_screened
#print axioms chargeRatio_abs_eq_unscreened_iff
#print axioms bjerrumPairLength_screened

end

end GaloisForLFunctions.HTGeometry.GaugeMixing
