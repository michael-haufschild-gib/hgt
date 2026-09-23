import GaloisForLFunctions.RHTower.EulerDeletionSignatureWordExpansion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The literal coprime deletion polygon has trivial signature through degree four

For coprime moduli `P = p+1` and `Q = q+1` the chronological deletion polygon of
`EulerDeletionJointPolygonMoment` closes after one common period.  This file proves that
**every** iterated-integral coefficient of that closed polygon, of word length one to four,
vanishes exactly.

The only arithmetic input is the already proved vanishing of all polynomial one-form
circulations of coefficient degree at most three, which comes from the CRT factorization of
the segment densities.  The passage from those seven circulations to all thirty word
coefficients is the low-degree shuffle calculus of `EulerDeletionSignatureWordExpansion`:
each circulation is identified with an explicit combination of word coefficients by induction
on the number of segments, and the shuffle relations then force each coefficient separately.
No path-signature theorem, no log-signature statement and no external result is imported.

Consequently the chronological exponential jets of one full coprime period vanish through
order four in every complex algebra, for arbitrary noncommuting generators.  This is the exact
input needed for the fifth-order block remainder; it carries no RH implication.
-/

open scoped BigOperators
namespace RHTower.DeletionPolygonSignature
open RHTower.SignatureWords RHTower.DeletionJointPolygon
noncomputable section

theorem position_step (p n : ℕ) :
    position p (n+1) 0 = position p n 0 + velocity p n := by
  rw [← segment_endpoint p n]
  simp [position]

theorem position_eq (p n : ℕ) (t : ℝ) :
    position p n t = position p n 0 + t * velocity p n := by
  simp [position]

theorem prefixSum_velocity (p n : ℕ) : prefixSum (velocity p) n = position p n 0 := by
  induction n with
  | zero => simp [prefixSum, position]
  | succ n ih => rw [prefixSum_succ, ih, position_step]

/-- Partial circulation of a monomial one-form against the first coordinate. -/
def momX (p q a b n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, ∫ t in (0:ℝ)..1,
    position p m t ^ a * position q m t ^ b * velocity p m

/-- Partial circulation of a monomial one-form against the second coordinate. -/
def momY (p q a b n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, ∫ t in (0:ℝ)..1,
    position q m t ^ b * position p m t ^ a * velocity q m

theorem momX_succ (p q a b n : ℕ) : momX p q a b (n+1) =
    momX p q a b n + ∫ t in (0:ℝ)..1,
      position p n t ^ a * position q n t ^ b * velocity p n :=
  Finset.sum_range_succ _ _

theorem momY_succ (p q a b n : ℕ) : momY p q a b (n+1) =
    momY p q a b n + ∫ t in (0:ℝ)..1,
      position q n t ^ b * position p n t ^ a * velocity q n :=
  Finset.sum_range_succ _ _

theorem momX_circulation (p q a b : ℕ) : momX p q a b ((p+1)*(q+1)) = circulation p q a b :=
  (circulation_eq_segment_sum p q a b).symm

theorem momY_circulation (p q a b : ℕ) : momY p q a b ((q+1)*(p+1)) = circulation q p b a :=
  (circulation_eq_segment_sum q p b a).symm

private theorem integral_cubic (c0 c1 c2 c3 : ℝ) :
    (∫ t in (0:ℝ)..1, (c0 + c1*t + c2*t^(2 : ℕ) + c3*t^(3 : ℕ))) = c0 + c1/2 + c2/3 + c3/4 := by
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, integral_pow]
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num
  ring

theorem mom_xy (p q n : ℕ) :
    momY p q 1 0 n = pathCoef (velocity p) (velocity q) n [false, true] := by
  induction n with
  | zero => simp [momY, pathCoef]
  | succ n ih =>
    have hint : ∀ t : ℝ, position q n t ^ (0 : ℕ) * position p n t ^ (1 : ℕ) * velocity q n =
        (position p n 0 * velocity q n) + (velocity p n * velocity q n) * t + 0*t^(2 : ℕ) + 0*t^(3 : ℕ) := by
      intro t; rw [position_eq p n t, position_eq q n t]; ring
    rw [momY_succ, ih, pathCoef_succ_two]
    simp only [hint, integral_cubic, coef_x, prefixSum_velocity, letterVal_false, letterVal_true]
    ring

theorem mom_yx (p q n : ℕ) :
    momX p q 0 1 n = pathCoef (velocity p) (velocity q) n [true, false] := by
  induction n with
  | zero => simp [momX, pathCoef]
  | succ n ih =>
    have hint : ∀ t : ℝ, position p n t ^ (0 : ℕ) * position q n t ^ (1 : ℕ) * velocity p n =
        (position q n 0 * velocity p n) + (velocity q n * velocity p n) * t + 0*t^(2 : ℕ) + 0*t^(3 : ℕ) := by
      intro t; rw [position_eq p n t, position_eq q n t]; ring
    rw [momX_succ, ih, pathCoef_succ_two]
    simp only [hint, integral_cubic, coef_y, prefixSum_velocity, letterVal_false, letterVal_true]
    ring

theorem mom_xxy (p q n : ℕ) :
    momY p q 2 0 n = 2 * pathCoef (velocity p) (velocity q) n [false, false, true] := by
  induction n with
  | zero => simp [momY, pathCoef]
  | succ n ih =>
    have hint : ∀ t : ℝ, position q n t ^ (0 : ℕ) * position p n t ^ (2 : ℕ) * velocity q n =
        ((position p n 0)^(2 : ℕ) * velocity q n) +
        (2 * position p n 0 * velocity p n * velocity q n) * t +
        ((velocity p n)^(2 : ℕ) * velocity q n) * t^(2 : ℕ) + 0*t^(3 : ℕ) := by
      intro t; rw [position_eq p n t, position_eq q n t]; ring
    rw [momY_succ, ih, pathCoef_succ_three]
    simp only [hint, integral_cubic, coef_x, coef_xx, prefixSum_velocity,
      letterVal_false, letterVal_true]
    ring

theorem mom_yyx (p q n : ℕ) :
    momX p q 0 2 n = 2 * pathCoef (velocity p) (velocity q) n [true, true, false] := by
  induction n with
  | zero => simp [momX, pathCoef]
  | succ n ih =>
    have hint : ∀ t : ℝ, position p n t ^ (0 : ℕ) * position q n t ^ (2 : ℕ) * velocity p n =
        ((position q n 0)^(2 : ℕ) * velocity p n) +
        (2 * position q n 0 * velocity q n * velocity p n) * t +
        ((velocity q n)^(2 : ℕ) * velocity p n) * t^(2 : ℕ) + 0*t^(3 : ℕ) := by
      intro t; rw [position_eq p n t, position_eq q n t]; ring
    rw [momX_succ, ih, pathCoef_succ_three]
    simp only [hint, integral_cubic, coef_y, coef_yy, prefixSum_velocity,
      letterVal_false, letterVal_true]
    ring

theorem mom_xxxy (p q n : ℕ) :
    momY p q 3 0 n = 6 * pathCoef (velocity p) (velocity q) n [false, false, false, true] := by
  induction n with
  | zero => simp [momY, pathCoef]
  | succ n ih =>
    have hint : ∀ t : ℝ, position q n t ^ (0 : ℕ) * position p n t ^ (3 : ℕ) * velocity q n =
        ((position p n 0)^(3 : ℕ) * velocity q n) +
        (3 * (position p n 0)^(2 : ℕ) * velocity p n * velocity q n) * t +
        (3 * position p n 0 * (velocity p n)^(2 : ℕ) * velocity q n) * t^(2 : ℕ) +
        ((velocity p n)^(3 : ℕ) * velocity q n) * t^(3 : ℕ) := by
      intro t; rw [position_eq p n t, position_eq q n t]; ring
    rw [momY_succ, ih, pathCoef_succ_four]
    simp only [hint, integral_cubic, coef_x, coef_xx, coef_xxx, prefixSum_velocity,
      letterVal_false, letterVal_true]
    ring

theorem mom_yyyx (p q n : ℕ) :
    momX p q 0 3 n = 6 * pathCoef (velocity p) (velocity q) n [true, true, true, false] := by
  induction n with
  | zero => simp [momX, pathCoef]
  | succ n ih =>
    have hint : ∀ t : ℝ, position p n t ^ (0 : ℕ) * position q n t ^ (3 : ℕ) * velocity p n =
        ((position q n 0)^(3 : ℕ) * velocity p n) +
        (3 * (position q n 0)^(2 : ℕ) * velocity q n * velocity p n) * t +
        (3 * position q n 0 * (velocity q n)^(2 : ℕ) * velocity p n) * t^(2 : ℕ) +
        ((velocity q n)^(3 : ℕ) * velocity p n) * t^(3 : ℕ) := by
      intro t; rw [position_eq p n t, position_eq q n t]; ring
    rw [momX_succ, ih, pathCoef_succ_four]
    simp only [hint, integral_cubic, coef_y, coef_yy, coef_yyy, prefixSum_velocity,
      letterVal_false, letterVal_true]
    ring

theorem mom_xxyy (p q n : ℕ) :
    momY p q 2 1 n = 2 * (pathCoef (velocity p) (velocity q) n [false, false, true, true] +
      pathCoef (velocity p) (velocity q) n [false, true, false, true] +
      pathCoef (velocity p) (velocity q) n [true, false, false, true]) := by
  induction n with
  | zero => simp [momY, pathCoef]
  | succ n ih =>
    have hint : ∀ t : ℝ, position q n t ^ (1 : ℕ) * position p n t ^ (2 : ℕ) * velocity q n =
        ((position p n 0)^(2 : ℕ) * position q n 0 * velocity q n) +
        ((2 * position p n 0 * velocity p n * position q n 0 +
          (position p n 0)^(2 : ℕ) * velocity q n) * velocity q n) * t +
        (((velocity p n)^(2 : ℕ) * position q n 0 +
          2 * position p n 0 * velocity p n * velocity q n) * velocity q n) * t^(2 : ℕ) +
        ((velocity p n)^(2 : ℕ) * velocity q n * velocity q n) * t^(3 : ℕ) := by
      intro t; rw [position_eq p n t, position_eq q n t]; ring
    have h5 := shuffle_x_y (velocity p) (velocity q) n
    have h8 := shuffle_x_xy (velocity p) (velocity q) n
    have h9 := shuffle_x_yx (velocity p) (velocity q) n
    simp only [prefixSum_velocity] at h5 h8 h9
    rw [momY_succ, ih, pathCoef_succ_four, pathCoef_succ_four, pathCoef_succ_four]
    simp only [hint, integral_cubic, coef_x, coef_y, coef_xx, prefixSum_velocity,
      letterVal_false, letterVal_true]
    linear_combination (-(velocity q n)) * h8 + (-(velocity q n)) * h9 +
      (-(velocity q n) * (velocity p n + position p n 0)) * h5


section Vanishing
variable {p q : ℕ}

theorem period_x (p q : ℕ) : position p ((p+1)*(q+1)) 0 = 0 := (common_period_closed p q).1

theorem period_y (p q : ℕ) : position q ((p+1)*(q+1)) 0 = 0 := (common_period_closed p q).2

private theorem period_comm (p q : ℕ) : (q+1)*(p+1) = (p+1)*(q+1) := mul_comm _ _

theorem coef_x_zero (p q : ℕ) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false] = 0 := by
  rw [coef_x, prefixSum_velocity, period_x]

theorem coef_y_zero (p q : ℕ) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true] = 0 := by
  rw [coef_y, prefixSum_velocity, period_y]

theorem coef_xx_zero (p q : ℕ) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, false] = 0 := by
  rw [coef_xx, prefixSum_velocity, period_x]; norm_num

theorem coef_yy_zero (p q : ℕ) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, true] = 0 := by
  rw [coef_yy, prefixSum_velocity, period_y]; norm_num

theorem coef_xxx_zero (p q : ℕ) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, false, false] = 0 := by
  rw [coef_xxx, prefixSum_velocity, period_x]; norm_num

theorem coef_yyy_zero (p q : ℕ) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, true, true] = 0 := by
  rw [coef_yyy, prefixSum_velocity, period_y]; norm_num

theorem coef_xxxx_zero (p q : ℕ) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, false, false, false] = 0 := by
  rw [coef_xxxx, prefixSum_velocity, period_x]; norm_num

theorem coef_yyyy_zero (p q : ℕ) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, true, true, true] = 0 := by
  rw [coef_yyyy, prefixSum_velocity, period_y]; norm_num

theorem coef_xy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, true] = 0 := by
  rw [← mom_xy p q, ← period_comm, momY_circulation]
  exact circulation_low_degree hpq.symm 0 1 (by norm_num)

theorem coef_yx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, false] = 0 := by
  rw [← mom_yx p q, momX_circulation]
  exact circulation_low_degree hpq 0 1 (by norm_num)

theorem coef_xxy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, false, true] = 0 := by
  have h : (2:ℝ) * pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, false, true] = 0 := by
    rw [← mom_xxy p q, ← period_comm, momY_circulation]
    exact circulation_low_degree hpq.symm 0 2 (by norm_num)
  linarith

theorem coef_yyx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, true, false] = 0 := by
  have h : (2:ℝ) * pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, true, false] = 0 := by
    rw [← mom_yyx p q, momX_circulation]
    exact circulation_low_degree hpq 0 2 (by norm_num)
  linarith

theorem coef_xxxy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, false, false, true] = 0 := by
  have h : (6:ℝ) * pathCoef (velocity p) (velocity q) ((p+1)*(q+1))
      [false, false, false, true] = 0 := by
    rw [← mom_xxxy p q, ← period_comm, momY_circulation]
    exact circulation_low_degree hpq.symm 0 3 (by norm_num)
  linarith

theorem coef_yyyx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, true, true, false] = 0 := by
  have h : (6:ℝ) * pathCoef (velocity p) (velocity q) ((p+1)*(q+1))
      [true, true, true, false] = 0 := by
    rw [← mom_yyyx p q, momX_circulation]
    exact circulation_low_degree hpq 0 3 (by norm_num)
  linarith

/-- The mixed degree-four circulation, the last arithmetic input. -/
theorem mixed_quartic_zero (hpq : (p+1).Coprime (q+1)) :
    (2:ℝ) * (pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, false, true, true] +
      pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, true, false, true] +
      pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, false, false, true]) = 0 := by
  rw [← mom_xxyy p q, ← period_comm, momY_circulation]
  exact circulation_low_degree hpq.symm 1 2 (by norm_num)

theorem coef_xyx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, true, false] = 0 := by
  have h := shuffle_x_xy (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_x, zero_mul, coef_xxy_zero hpq] at h
  linarith

theorem coef_yxx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, false, false] = 0 := by
  have h := shuffle_x_yx (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_x, zero_mul, coef_xyx_zero hpq] at h
  linarith

theorem coef_yxy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, false, true] = 0 := by
  have h := shuffle_y_yx (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_y, zero_mul, coef_yyx_zero hpq] at h
  linarith

theorem coef_xyy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, true, true] = 0 := by
  have h := shuffle_y_xy (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_y, zero_mul, coef_yxy_zero hpq] at h
  linarith

theorem coef_xxyx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, false, true, false] = 0 := by
  have h := shuffle_x_xxy (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_x, zero_mul, coef_xxxy_zero hpq] at h
  linarith

theorem coef_xyxx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, true, false, false] = 0 := by
  have h := shuffle_x_xyx (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_x, zero_mul, coef_xxyx_zero hpq] at h
  linarith

theorem coef_yxxx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, false, false, false] = 0 := by
  have h := shuffle_x_yxx (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_x, zero_mul, coef_xyxx_zero hpq] at h
  linarith

theorem coef_yyxy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, true, false, true] = 0 := by
  have h := shuffle_y_yyx (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_y, zero_mul, coef_yyyx_zero hpq] at h
  linarith

theorem coef_yxyy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, false, true, true] = 0 := by
  have h := shuffle_y_yxy (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_y, zero_mul, coef_yyxy_zero hpq] at h
  linarith

theorem coef_xyyy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, true, true, true] = 0 := by
  have h := shuffle_y_xyy (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_y, zero_mul, coef_yxyy_zero hpq] at h
  linarith

theorem coef_xxyy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, false, true, true] = 0 := by
  have h := shuffle_y_xxy (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_y, zero_mul] at h
  have hm := mixed_quartic_zero hpq
  linarith

theorem coef_xyxy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, true, false, true] = 0 := by
  have h := shuffle_xy_xy (velocity p) (velocity q) ((p+1)*(q+1))
  rw [coef_xy_zero hpq, mul_zero, coef_xxyy_zero hpq] at h
  linarith

theorem coef_yxxy_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, false, false, true] = 0 := by
  have hm := mixed_quartic_zero hpq
  rw [coef_xxyy_zero hpq, coef_xyxy_zero hpq] at hm
  linarith

theorem coef_xyyx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [false, true, true, false] = 0 := by
  have h := shuffle_x_xyy (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_x, zero_mul, coef_xxyy_zero hpq, coef_xyxy_zero hpq] at h
  linarith

theorem coef_yxyx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, false, true, false] = 0 := by
  have h := shuffle_x_yxy (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_x, zero_mul, coef_xyxy_zero hpq, coef_yxxy_zero hpq] at h
  linarith

theorem coef_yyxx_zero (hpq : (p+1).Coprime (q+1)) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) [true, true, false, false] = 0 := by
  have h := shuffle_x_yyx (velocity p) (velocity q) ((p+1)*(q+1))
  rw [prefixSum_velocity, period_x, zero_mul, coef_xyyx_zero hpq, coef_yxyx_zero hpq] at h
  linarith

/-- Every signature coefficient of the literal coprime deletion polygon vanishes through
degree four, over one full common period. -/
theorem pathCoef_period_eq_zero (hpq : (p+1).Coprime (q+1)) (w : Word)
    (h1 : 1 ≤ w.length) (h4 : w.length ≤ 4) :
    pathCoef (velocity p) (velocity q) ((p+1)*(q+1)) w = 0 := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
  · exact absurd h1 (by norm_num)
  · cases a
    · exact coef_x_zero p q
    · exact coef_y_zero p q
  · cases a <;> cases b
    · exact coef_xx_zero p q
    · exact coef_xy_zero hpq
    · exact coef_yx_zero hpq
    · exact coef_yy_zero p q
  · cases a <;> cases b <;> cases c
    · exact coef_xxx_zero p q
    · exact coef_xxy_zero hpq
    · exact coef_xyx_zero hpq
    · exact coef_xyy_zero hpq
    · exact coef_yxx_zero hpq
    · exact coef_yxy_zero hpq
    · exact coef_yyx_zero hpq
    · exact coef_yyy_zero p q
  · cases a <;> cases b <;> cases c <;> cases d
    · exact coef_xxxx_zero p q
    · exact coef_xxxy_zero hpq
    · exact coef_xxyx_zero hpq
    · exact coef_xxyy_zero hpq
    · exact coef_xyxx_zero hpq
    · exact coef_xyxy_zero hpq
    · exact coef_xyyx_zero hpq
    · exact coef_xyyy_zero hpq
    · exact coef_yxxx_zero hpq
    · exact coef_yxxy_zero hpq
    · exact coef_yxyx_zero hpq
    · exact coef_yxyy_zero hpq
    · exact coef_yyxx_zero hpq
    · exact coef_yyxy_zero hpq
    · exact coef_yyyx_zero hpq
    · exact coef_yyyy_zero p q
  · exfalso
    simp only [List.length_cons] at h4
    omega

end Vanishing


section JetExport
variable {p q : ℕ}

/-- The chronological jets of the literal coprime deletion block vanish through order four,
for arbitrary noncommuting generators in every complex algebra. -/
theorem jet_deletion_velocity_eq_zero {A : Type*} [Ring A] [Algebra ℂ A]
    (hpq : (p+1).Coprime (q+1)) (X Y : A) (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    DeletionJointExponential.jet ((List.range ((p+1)*(q+1))).map
      (fun m => ((velocity p m : ℝ) : ℂ) • X + ((velocity q m : ℝ) : ℂ) • Y)) k = 0 :=
  jet_eq_zero_of_pathCoef _ _ X Y _ k
    (fun w hw => pathCoef_period_eq_zero hpq w (by omega) (by omega))

/-- The same vanishing for the literal source velocities of the analytic development. -/
theorem jet_sourceVelocity_eq_zero {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (hpq : (p+1).Coprime (q+1)) (X Y : A) (k : ℕ)
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    DeletionJointExponential.jet ((List.range ((p+1)*(q+1))).map
      (fun m => DeletionJointExponential.sourceVelocity (p+1) (q+1) m X Y)) k = 0 := by
  have hcast : ∀ z : ℤ, ((z : ℝ) : ℂ) = (z : ℂ) := fun z => by push_cast; ring
  have hv : ((List.range ((p+1)*(q+1))).map
      (fun m => DeletionJointExponential.sourceVelocity (p+1) (q+1) m X Y))
      = (List.range ((p+1)*(q+1))).map
        (fun m => ((velocity p m : ℝ) : ℂ) • X + ((velocity q m : ℝ) : ℂ) • Y) := by
    refine List.map_congr_left (fun m _ => ?_)
    simp only [DeletionJointExponential.sourceVelocity, velocity, hcast]
  rw [hv]
  exact jet_deletion_velocity_eq_zero hpq X Y k hk1 hk4

end JetExport
end
end RHTower.DeletionPolygonSignature
