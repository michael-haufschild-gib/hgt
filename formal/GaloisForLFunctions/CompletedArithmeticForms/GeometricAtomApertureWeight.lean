import GaloisForLFunctions.HTGeometry.GeometricPhaseConvexity
import GaloisForLFunctions.CompletedArithmeticForms.TwoAtomApertureWeight

/-!
# Convex aperture cancellation along a geometric atom chain

Damped clipped aperture weights have nonnegative second differences and
a strictly positive initial difference. The geometric-phase identity
therefore cancels all unequal pairs at each positive common center.
-/

open Complex Finset
open _root_.HTGeometry
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower

/-- The damped convex payment leaves an explicit positive reserve. -/
theorem thetaCenterTailWeight_chain_reserve {a h p s : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ 2 * thetaCuspCenterTailWeight a (max 0 s) ≤
      thetaCuspCenterTailWeight a (max 0 s) -
        2 * p * thetaCuspCenterTailWeight a (max 0 (s - h)) +
        p ^ 2 * thetaCuspCenterTailWeight a (max 0 (s - 2 * h)) := by
  by_cases hs : s ≤ 0
  · have hs1 : s - h ≤ 0 := by linarith only [hs, hh]
    have hs2 : s - 2 * h ≤ 0 := by linarith only [hs, hh]
    simp only [max_eq_left hs, max_eq_left hs1, max_eq_left hs2,
      thetaCuspCenterTailWeight, mul_zero, Real.sinh_zero, Real.cosh_zero,
      zero_mul, add_zero, sub_zero, le_refl]
  · have hs0 : 0 ≤ s := (lt_of_not_ge hs).le
    have hmid := thetaCenterTailWeight_two_atom_payment ha hh hs0
      (show (0 : ℝ) ≤ 1 by norm_num) (le_refl (1 : ℝ))
    norm_num only [mul_one, one_pow, one_mul] at hmid
    have hmono := thetaCenterTailWeight_mono ha
      (le_max_left 0 (s - 2 * h)) (max_le hs0 (by linarith only [hh]))
    have h1 := mul_nonneg hp (sub_nonneg.mpr hmid)
    have h2 := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hp1)) (sub_nonneg.mpr hmono)
    rw [max_eq_right hs0]
    nlinarith only [h1, h2]

/-- Geometric damping of the clipped aperture weight at the total atom exponent. -/
def geometricApertureWeight (a h p s : ℝ) (k : ℕ) : ℝ :=
  p ^ k * thetaCuspCenterTailWeight a (max 0 (s - (k : ℝ) * h))

theorem geometricApertureWeight_secondDifference {a h p : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) (k : ℕ) :
    0 ≤ geometricApertureWeight a h p s k -
      2 * geometricApertureWeight a h p s (k + 1) +
      geometricApertureWeight a h p s (k + 2) := by
  have hreserve := thetaCenterTailWeight_chain_reserve ha hh hp hp1 (s := s - (k : ℝ) * h)
  have hw := thetaCuspCenterTailWeight_nonneg ha (le_max_left 0 (s - (k : ℝ) * h))
  have hd : 0 ≤ thetaCuspCenterTailWeight a (max 0 (s - (k : ℝ) * h)) -
      2 * p * thetaCuspCenterTailWeight a (max 0 (s - (k : ℝ) * h - h)) +
      p ^ 2 * thetaCuspCenterTailWeight a (max 0 (s - (k : ℝ) * h - 2 * h)) :=
    (mul_nonneg (sq_nonneg _) hw).trans hreserve
  have hm := mul_nonneg (pow_nonneg hp k) hd
  unfold geometricApertureWeight
  push_cast
  rw [pow_succ, pow_add,
    show s - ((k : ℝ) + 1) * h = s - (k : ℝ) * h - h by ring,
    show s - ((k : ℝ) + 2) * h = s - (k : ℝ) * h - 2 * h by ring]
  nlinarith only [hm]

theorem geometricApertureWeight_initial_pos {a h p s : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hp : 0 ≤ p) (hp1 : p < 1) (hs : 0 < s) :
    0 < geometricApertureWeight a h p s 0 -
      2 * geometricApertureWeight a h p s 1 +
      geometricApertureWeight a h p s 2 := by
  have hreserve := thetaCenterTailWeight_chain_reserve ha.le hh hp hp1.le (s := s)
  rw [max_eq_right hs.le] at hreserve
  have hstrict := mul_pos (sq_pos_of_pos (sub_pos.mpr hp1))
    (thetaCuspCenterTailWeight_pos ha hs)
  have hpos := hstrict.trans_le hreserve
  simpa only [geometricApertureWeight, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, zero_mul, one_mul, sub_zero, max_eq_right hs.le, mul_assoc] using hpos

theorem geometricApertureWeight_zero {a h p s : ℝ} {k : ℕ} (hs : s ≤ (k : ℝ) * h) :
    geometricApertureWeight a h p s k = 0 := by
  simp only [geometricApertureWeight, max_eq_left (sub_nonpos.mpr hs),
    thetaCuspCenterTailWeight, mul_zero, Real.sinh_zero, Real.cosh_zero,
    zero_mul, add_zero]

/-- All geometric atom pairs cancel strictly at each positive common center. -/
theorem geometricAperture_phase_sum_pos {z : ℂ} (hz : ‖z‖ = 1)
    {a h p s : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hp : 0 ≤ p) (hp1 : p < 1)
    (hs : 0 < s) (N : ℕ) (hN : s ≤ (N : ℝ) * h) :
    0 < ∑ k ∈ range (N + 1),
      geometricApertureWeight a h p s k * (geometricDiagonal z k).re := by
  have hNpos : 0 < N := by
    by_contra hn
    have he : N = 0 := Nat.eq_zero_of_not_pos hn
    subst N
    simp only [Nat.cast_zero, zero_mul] at hN
    exact (not_lt_of_ge hN) hs
  have hN1 : s ≤ (↑(N + 1) : ℝ) * h := by
    push_cast
    nlinarith only [hN, hh]
  exact geometricDiagonal_weighted_pos hz _ N hNpos
    (geometricApertureWeight_zero hN) (geometricApertureWeight_zero hN1)
    (fun k _ => geometricApertureWeight_secondDifference ha.le hh hp hp1.le s k)
    (geometricApertureWeight_initial_pos ha hh hp hp1 hs)

/-- Literal ratio-cosine form of the strict common-center chain cancellation. -/
theorem geometricAperture_cosine_sum_pos
    {a h p s : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hp : 0 ≤ p) (hp1 : p < 1)
    (hs : 0 < s) (N : ℕ) (hN : s ≤ (N : ℝ) * h) (θ : ℝ) :
    0 < ∑ k ∈ range (N + 1), geometricApertureWeight a h p s k *
      (∑ j ∈ range (k + 1), Real.cos ((2 * (j : ℝ) - k) * θ)) := by
  have hz : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  simpa only [geometricDiagonal_exp_re] using
    geometricAperture_phase_sum_pos hz ha hh hp hp1 hs N hN

end GaloisForLFunctions.CompletedArithmeticForms
