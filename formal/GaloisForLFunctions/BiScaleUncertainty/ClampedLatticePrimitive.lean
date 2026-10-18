import GaloisForLFunctions.BiScaleUncertainty.ClampedRampLatticeSum
import GaloisForLFunctions.RHTower.EulerDeletionRemainderFirstCoefficient

/-! A bounded primitive for the exact collar remainder. The mean cancels
between the two dilation scales, including every integer join. -/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower.DeletionMixedRefinement
noncomputable section
set_option autoImplicit false

theorem clampedLatticeRemainder_eq_neg_bernoulli {y : ℝ} (hy : 0 ≤ y) :
    clampedLatticeRemainder y = -_root_.RHTower.bernoulliPeriodic y := by
  unfold clampedLatticeRemainder _root_.RHTower.bernoulliPeriodic
  rw [natCast_floor_eq_intCast_floor hy]
  unfold Int.fract
  ring

/-- The public integral definition gives the derivative through all integer
joins, without assuming differentiability of the fractional-part function. -/
theorem bernoulliCenteredPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt bernoulliCenteredPrimitive (_root_.RHTower.bernoulliPeriodic x+1/12) x := by
  have hb : Continuous _root_.RHTower.bernoulliPeriodic := by
    have hc : Continuous (fun y : ℝ => (y^2-y)/2) := by fun_prop
    exact hc.continuousOn.comp_fract'' (by norm_num)
  have hc : Continuous (fun y : ℝ => _root_.RHTower.bernoulliPeriodic y+1/12) :=
    hb.add continuous_const
  change HasDerivAt (fun z : ℝ => ∫ y in (0 : ℝ)..z,
    _root_.RHTower.bernoulliPeriodic y+1/12) (_root_.RHTower.bernoulliPeriodic x+1/12) x
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

def clampedLatticePrimitive (ε a y : ℝ) : ℝ :=
  bernoulliCenteredPrimitive (a*y)/a-
    bernoulliCenteredPrimitive (a*(1+ε)*y)/(a*(1+ε))

theorem clampedLatticePrimitive_abs_le {ε a : ℝ} (hε : 0 ≤ ε) (ha : 0 < a) (y : ℝ) :
    |clampedLatticePrimitive ε a y| ≤ 2/a := by
  have hA : 0 < a*(1+ε) := by positivity
  have h1 := abs_bernoulliCenteredPrimitive_le (a*y)
  have h2 := abs_bernoulliCenteredPrimitive_le (a*(1+ε)*y)
  unfold clampedLatticePrimitive
  calc
    _ ≤ |bernoulliCenteredPrimitive (a*y)/a|+
        |bernoulliCenteredPrimitive (a*(1+ε)*y)/(a*(1+ε))| := abs_sub _ _
    _ = |bernoulliCenteredPrimitive (a*y)|/a+
        |bernoulliCenteredPrimitive (a*(1+ε)*y)|/(a*(1+ε)) := by
      rw [abs_div, abs_div, abs_of_pos ha, abs_of_pos hA]
    _ ≤ 1/a+1/(a*(1+ε)) := add_le_add
      (div_le_div_of_nonneg_right h1 ha.le) (div_le_div_of_nonneg_right h2 hA.le)
    _ ≤ 1/a+1/a := add_le_add le_rfl
      (one_div_le_one_div_of_le ha (show a ≤ a*(1+ε) by nlinarith))
    _ = _ := by ring

/-- The actual collar difference is the derivative of a uniformly bounded
function. The constant means cancel exactly. -/
theorem clampedLatticePrimitive_hasDerivAt {ε a y : ℝ}
    (hε : 0 ≤ ε) (ha : 0 < a) (hy : 0 < y) :
    HasDerivAt (clampedLatticePrimitive ε a)
      (clampedLatticeRemainder (a*(1+ε)*y)-clampedLatticeRemainder (a*y)) y := by
  have hA : 0 < a*(1+ε) := by positivity
  have h1 := (bernoulliCenteredPrimitive_hasDerivAt (a*y)).comp y
    ((hasDerivAt_id y).const_mul a)
  have h2 := (bernoulliCenteredPrimitive_hasDerivAt (a*(1+ε)*y)).comp y
    ((hasDerivAt_id y).const_mul (a*(1+ε)))
  unfold clampedLatticePrimitive
  convert (h1.div_const a).sub (h2.div_const (a*(1+ε))) using 1 <;> try rfl
  rw [clampedLatticeRemainder_eq_neg_bernoulli (by positivity),
    clampedLatticeRemainder_eq_neg_bernoulli (by positivity)]
  field_simp
  ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
