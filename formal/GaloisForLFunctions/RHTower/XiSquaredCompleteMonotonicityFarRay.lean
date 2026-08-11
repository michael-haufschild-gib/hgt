import GaloisForLFunctions.RHTower.SquaredXiCompleteMonotonicity
import GaloisForLFunctions.RHTower.XiResolventUnconditionalSector

/-!
# Unbounded-order complete monotonicity of the Xi radial field on the quadratic far ray

The squared radial field `g y = xi' (1/2 + sqrt y) / (2 sqrt y xi (1/2 + sqrt y))` carries two
unconditional alternating-derivative sign laws proved by different cone mechanisms:

* the fixed eighty-four sector (off-line quartet height gap) gives `(-1)^n g^(n) y > 0` for all
  `n ≤ 18` and every `y > 0`;
* the degree-dependent aperture of the resolvent sector tower gives the same sign for **every**
  order `n` once `y ≥ (n+1)^2`.

This file proves the second law and records the union.  The bridge is the identity
`xiShiftedReciprocalSquare v q = xiResolventPoint v q` — the Möbius-translated reciprocal-square
atom is the resolvent coordinate — which also transports divisor conjugation invariance: every
resolvent moment is a real number.

Under RH the sign law holds at every order and every `y > 0`; unconditionally it now holds on
`{n ≤ 18} ∪ {y ≥ (n+1)^2}`.  The failure of complete monotonicity, were RH false, is thereby
confined to the complementary wedge `n ≥ 19`, `0 < y < (n+1)^2` of the order–base-point plane.
-/

open Complex

namespace RHTower

noncomputable section

/-- The Möbius-translated reciprocal-square atom is the resolvent coordinate. -/
theorem xiShiftedReciprocalSquare_eq_xiResolventPoint {v : ℝ} (hv : 0 ≤ v) (q : XiZeroCopy) :
    xiShiftedReciprocalSquare v q = xiResolventPoint v q := by
  rw [xiShiftedReciprocalSquare_eq_inv hv, xiResolventPoint, xiSquaredNode]
  rw [add_comm]

/-- The shifted reciprocal moments are the resolvent moments. -/
theorem xiShiftedReciprocalMoment_eq_xiResolventMoment {v : ℝ} (hv : 0 ≤ v) (n : ℕ) :
    xiShiftedReciprocalMoment v n = xiResolventMoment n v := by
  rw [xiShiftedReciprocalMoment, xiResolventMoment]
  exact tsum_congr fun q => by
    rw [xiShiftedReciprocalSquare_eq_xiResolventPoint hv]

/-- **Every resolvent moment is a real number**: divisor conjugation invariance transported
through the atom identification. -/
theorem xiResolventMoment_im_eq_zero {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    (xiResolventMoment n X).im = 0 := by
  rw [← xiShiftedReciprocalMoment_eq_xiResolventMoment hX]
  exact xiShiftedReciprocalMoment_im_eq_zero hX n

/-- Far-ray moment positivity in the shifted-reciprocal chart. -/
theorem re_xiShiftedReciprocalMoment_pos_of_sq_le {y : ℝ} {n : ℕ}
    (hy : ((n : ℝ) + 1) ^ 2 ≤ y) :
    0 < (xiShiftedReciprocalMoment y n).re := by
  have hy0 : (0 : ℝ) ≤ y := le_trans (by positivity) hy
  rw [xiShiftedReciprocalMoment_eq_xiResolventMoment hy0]
  exact xiResolventMoment_re_pos_of_add_one_sq_le n hy

/-- **Unbounded-order complete monotonicity on the quadratic far ray**: for every derivative
order `n` the alternating sign law for the Xi radial field holds unconditionally at every squared
base point `y ≥ (n+1)^2`. -/
theorem alternating_iteratedDeriv_squaredXiRadialField_pos_of_sq_le {y : ℝ} {n : ℕ}
    (hy : ((n : ℝ) + 1) ^ 2 ≤ y) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n squaredXiRadialField y := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) hy
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [iteratedDeriv_squaredXiRadialField n hy0,
    show (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * (n.factorial : ℝ) / 2 *
        (xiShiftedReciprocalMoment y n).re)
      = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) / 2 * (xiShiftedReciprocalMoment y n).re) by ring,
    hsq, one_mul]
  exact mul_pos (by positivity) (re_xiShiftedReciprocalMoment_pos_of_sq_le hy)

/-- **The unconditional complete-monotonicity domain**: every order through eighteen on the whole
positive ray, and every order on the quadratic far ray.  A failure of complete monotonicity —
which RH forbids everywhere — is confined to the wedge `n ≥ 19`, `y < (n+1)^2`. -/
theorem alternating_iteratedDeriv_squaredXiRadialField_pos_of_le_or_far {y : ℝ} {n : ℕ}
    (hy : 0 < y) (h : n ≤ 18 ∨ ((n : ℝ) + 1) ^ 2 ≤ y) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n squaredXiRadialField y := by
  rcases h with h | h
  · exact alternating_iteratedDeriv_squaredXiRadialField_pos hy h
  · exact alternating_iteratedDeriv_squaredXiRadialField_pos_of_sq_le h

end

end RHTower
