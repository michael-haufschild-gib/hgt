import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational grids near the identity

Distinct positive rational units approach one on a common cyclic lattice. Their
orbit lengths are explicit, and reciprocal denominators are bounded by distance
from one.
-/

open Filter Topology
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- A nonzero integral numerator difference bounds the reciprocal rational denominator. -/
theorem inv_den_le_abs_sub_one (q : ℚ) (hq : q ≠ 1) :
    1 / (q.den : ℝ) ≤ |(q : ℝ) - 1| := by
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hdiff : q.num - (q.den : ℤ) ≠ 0 := by
    intro h
    apply hq
    rw [← Rat.num_div_den q, sub_eq_zero.mp h, Int.cast_natCast,
      div_self (by exact_mod_cast q.den_pos.ne' : (q.den : ℚ) ≠ 0)]
  have hgap : (1 : ℝ) ≤ |(q.num : ℝ) - (q.den : ℝ)| := by
    exact_mod_cast Int.one_le_abs hdiff
  have hrat : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Rat.mul_den_eq_num q
  apply (div_le_iff₀ hden).mpr
  calc
    1 ≤ |(q.num : ℝ) - (q.den : ℝ)| := hgap
    _ = |((q : ℝ) - 1) * (q.den : ℝ)| := by
      congr 1
      nlinarith only [hrat]
    _ = |(q : ℝ) - 1| * (q.den : ℝ) := by rw [abs_mul, abs_of_pos hden]

/-- Distinct positive rational units approaching one along a common integral grid. -/
def nearIdentityUnit (N i : ℕ) : ℚˣ :=
  Units.mk0 (1 + (i : ℚ) / ((N : ℚ) + 1)) (by positivity)

theorem nearIdentityUnit_pos (N i : ℕ) : 0 < (nearIdentityUnit N i : ℚ) := by
  simp only [nearIdentityUnit, Units.val_mk0]
  positivity

theorem nearIdentityUnit_injective (N : ℕ) : Function.Injective (nearIdentityUnit N) := by
  intro i j h
  have hv := congrArg (fun v : ℚˣ => (v : ℚ)) h
  simp only [nearIdentityUnit, Units.val_mk0] at hv
  have hd : (N : ℚ) + 1 ≠ 0 := by positivity
  have hc : (i : ℚ) = (j : ℚ) := by
    field_simp at hv
    linarith only [hv]
  exact_mod_cast hc

theorem tendsto_nearIdentityUnit (i : ℕ) :
    Tendsto (fun N : ℕ => ((nearIdentityUnit N i : ℚ) : ℝ)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [nearIdentityUnit, Units.val_mk0, Rat.cast_add, Rat.cast_one, Rat.cast_div,
    Rat.cast_natCast, div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv, mul_zero, add_zero] using
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv) :
      Tendsto (fun N : ℕ => 1 + (i : ℝ) * ((N : ℝ) + 1)⁻¹) atTop (𝓝 (1 + (i : ℝ) * 0)))

theorem tendsto_nearIdentityRatio (a b : ℕ) :
    Tendsto (fun N => ((((nearIdentityUnit N a)⁻¹ * nearIdentityUnit N b : ℚˣ) : ℚ) : ℝ))
      atTop (𝓝 1) := by
  simpa only [Units.val_mul, Units.val_inv_eq_inv_val, Rat.cast_mul, Rat.cast_inv,
    inv_one, mul_one] using
    ((tendsto_nearIdentityUnit a).inv₀ one_ne_zero).mul (tendsto_nearIdentityUnit b)

/-- A common step whose denominator grows faster than each near-identity grid numerator. -/
def nearIdentityStep (N : ℕ) : ℚ := ((N : ℚ) + 1)⁻¹ ^ 2

theorem nearIdentityUnit_eq_nat_mul_step (N i : ℕ) :
    (nearIdentityUnit N i : ℚ) = (((N + 1) * (N + 1 + i) : ℕ) : ℚ) *
      nearIdentityStep N := by
  have hd : (N : ℚ) + 1 ≠ 0 := by positivity
  simp only [nearIdentityUnit, Units.val_mk0, nearIdentityStep, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp [hd]

/-- The common step divided by a grid point is an inverse positive integer. -/
theorem nearIdentityStep_div (N i : ℕ) :
    nearIdentityStep N / (nearIdentityUnit N i : ℚ) =
      ((((N + 1) * (N + 1 + i) : ℕ) : ℚ))⁻¹ := by
  have hm : ((N + 1) * (N + 1 + i) : ℕ) ≠ 0 := by positivity
  have hb : nearIdentityStep N ≠ 0 := by unfold nearIdentityStep; positivity
  rw [nearIdentityUnit_eq_nat_mul_step]
  field_simp [hb, Nat.cast_ne_zero.mpr hm]

/-- The cyclic orbit length on the common grid is its explicit positive integer multiple. -/
theorem nearIdentityStep_div_den (N i : ℕ) :
    (nearIdentityStep N / (nearIdentityUnit N i : ℚ)).den = (N + 1) * (N + 1 + i) := by
  rw [nearIdentityStep_div, Rat.inv_natCast_den, if_neg (by positivity)]

#print axioms inv_den_le_abs_sub_one
#print axioms nearIdentityStep_div_den
end GaloisForLFunctions.BiarithmeticGeometry
