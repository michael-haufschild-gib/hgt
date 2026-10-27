import GaloisForLFunctions.ArithmeticElectrostatics.ReflectedTransverseWork
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Positive scale increments of reflected work

Above the zero-free height gap, the scale derivative of rational damping has
enough relative regularity to control the reflected mixed term. Consequently
every reflected pair contributes monotonically as the damping scale increases.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open GaloisForLFunctions.ArithmeticElectrostatics
open Set

/-- Height profile of the scale derivative, with the common factor `4 R³` removed. -/
def dampingVelocity (R t : ℝ) : ℝ := t ^ 2 / (R ^ 2 + t ^ 2) ^ 3

theorem dampingVelocity_nonneg (R t : ℝ) : 0 ≤ dampingVelocity R t := by
  unfold dampingVelocity
  positivity

private theorem dampingVelocity_relative_pos (R a b : ℝ) (ha : 4 ≤ a) (hb : 4 ≤ b) :
    2 * |dampingVelocity R a - dampingVelocity R b| ≤
      |a - b| * (dampingVelocity R a + dampingVelocity R b) := by
  let Q := R ^ 6 - a ^ 2 * b ^ 2 * (3 * R ^ 2 + a ^ 2 + b ^ 2)
  let S := a ^ 2 * (R ^ 2 + b ^ 2) ^ 3 + b ^ 2 * (R ^ 2 + a ^ 2) ^ 3
  let D := (R ^ 2 + a ^ 2) ^ 3 * (R ^ 2 + b ^ 2) ^ 3
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hA : 0 < R ^ 2 + a ^ 2 := by nlinarith only [ha, sq_nonneg R]
  have hB : 0 < R ^ 2 + b ^ 2 := by nlinarith only [hb, sq_nonneg R]
  have hD : 0 < D := mul_pos (pow_pos hA 3) (pow_pos hB 3)
  have hsum : 4 * (a + b) ≤ a ^ 2 + b ^ 2 := by
    nlinarith only [mul_nonneg ha0 (sub_nonneg.mpr ha),
      mul_nonneg hb0 (sub_nonneg.mpr hb)]
  have hlin : 0 ≤ a ^ 2 + b ^ 2 - 2 * (a + b) := by
    linarith only [hsum, ha0, hb0]
  have hquartic : 0 ≤ a ^ 4 + b ^ 4 - 2 * (a + b) * (a ^ 2 + b ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hsum (add_nonneg (sq_nonneg a) (sq_nonneg b))
    nlinarith only [hmul, sq_nonneg (a ^ 2 - b ^ 2)]
  have hm : 0 ≤ S - 2 * (a + b) * Q := by
    have hid : S - 2 * (a + b) * Q =
        (a ^ 2 + b ^ 2 - 2 * (a + b)) * R ^ 6 + 6 * a ^ 2 * b ^ 2 * R ^ 4 +
        3 * a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 + 2 * (a + b)) * R ^ 2 +
        a ^ 2 * b ^ 2 * (a ^ 4 + b ^ 4 + 2 * (a + b) * (a ^ 2 + b ^ 2)) := by
      dsimp only [S, Q]
      ring
    rw [hid]
    positivity
  have hp : 0 ≤ S + 2 * (a + b) * Q := by
    have hid : S + 2 * (a + b) * Q =
        (a ^ 2 + b ^ 2 + 2 * (a + b)) * R ^ 6 + 6 * a ^ 2 * b ^ 2 * R ^ 4 +
        3 * a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2 * (a + b)) * R ^ 2 +
        a ^ 2 * b ^ 2 * (a ^ 4 + b ^ 4 - 2 * (a + b) * (a ^ 2 + b ^ 2)) := by
      dsimp only [S, Q]
      ring
    rw [hid]
    positivity
  have hQ : 2 * |(a + b) * Q| ≤ S := by
    have h := (abs_le.mpr ⟨by linarith only [hp], by linarith only [hm]⟩ :
      |2 * ((a + b) * Q)| ≤ S)
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h
  have hdiff : dampingVelocity R a - dampingVelocity R b =
      (a - b) * ((a + b) * Q) / D := by
    dsimp only [dampingVelocity, Q, D]
    field_simp
    ring
  have hadd : dampingVelocity R a + dampingVelocity R b = S / D := by
    dsimp only [dampingVelocity, S, D]
    field_simp
  rw [hdiff, hadd, abs_div, abs_mul, abs_of_pos hD]
  calc
    2 * (|a - b| * |(a + b) * Q| / D) =
        |a - b| * (2 * |(a + b) * Q|) / D := by ring
    _ ≤ |a - b| * S / D :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (abs_nonneg _)) hD.le
    _ = |a - b| * (S / D) := by ring

/-- The zero-free height gap makes the derivative weights relatively Lipschitz. -/
theorem dampingVelocity_relative (R t u : ℝ) (ht : 4 ≤ |t|) (hu : 4 ≤ |u|) :
    2 * |dampingVelocity R t - dampingVelocity R u| ≤
      |t - u| * (dampingVelocity R t + dampingVelocity R u) := by
  have h := dampingVelocity_relative_pos R |t| |u| ht hu
  simp only [dampingVelocity, sq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub t u)
    (add_nonneg (dampingVelocity_nonneg R t) (dampingVelocity_nonneg R u)))

/-- Near-collision and far-field bounds together absorb the derivative's mixed term. -/
theorem dampingVelocity_work_nonneg (R x y t u : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) (ht : 4 ≤ |t|) (hu : 4 ≤ |u|) :
    0 ≤ reflectedWork x y (t - u) (dampingVelocity R t) (dampingVelocity R u) := by
  apply (reflectedWork_bounds x y (t - u) _ _ ?_).1
  have hv := dampingVelocity_nonneg R t
  have hw := dampingVelocity_nonneg R u
  by_cases hd : (t - u) ^ 2 ≤ 1
  · have h1 := mul_le_mul_of_nonneg_right (dampingVelocity_relative R t u ht hu)
      (abs_nonneg (reflectedCross x y (t - u)))
    have h2 := mul_le_mul_of_nonneg_left (reflectedCross_near x y (t - u) hxy hd)
      (add_nonneg hv hw)
    rw [abs_mul] at h2 ⊢
    nlinarith only [h1, h2]
  · have hdiff : |dampingVelocity R t - dampingVelocity R u| ≤
        dampingVelocity R t + dampingVelocity R u := by
      exact abs_le.mpr ⟨by linarith only [hv, hw], by linarith only [hv, hw]⟩
    rw [abs_mul]
    exact mul_le_mul hdiff (reflectedCross_far x y (t - u) hxy (le_of_not_ge hd))
      (abs_nonneg _) (add_nonneg hv hw)

/-- Exact scale derivative of rational damping away from height zero. -/
theorem hasDerivAt_heightDamping (R t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun r => heightDamping r t) (4 * R ^ 3 * dampingVelocity R t) R := by
  have hden : R ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg R) (sq_pos_of_ne_zero ht))
  convert ((hasDerivAt_id R).pow 4).div
    (((hasDerivAt_id R).pow 2).add_const (t ^ 2) |>.pow 2) (pow_ne_zero 2 hden) using 1
  · rfl
  · dsimp only [dampingVelocity]
    field_simp
    <;> ring

/-- Every reflected pair above the height gap increases with damping scale. -/
theorem reflectedWork_monotoneOn_scale (x y t u : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) (ht : 4 ≤ |t|) (hu : 4 ≤ |u|) :
    MonotoneOn (fun R => reflectedWork x y (t - u) (heightDamping R t)
      (heightDamping R u)) (Ici 0) := by
  have ht0 : t ≠ 0 := by intro h; simp only [h, abs_zero] at ht; linarith only [ht]
  have hu0 : u ≠ 0 := by intro h; simp only [h, abs_zero] at hu; linarith only [hu]
  have hd (R : ℝ) : HasDerivAt
      (fun r => reflectedWork x y (t - u) (heightDamping r t) (heightDamping r u))
      (4 * R ^ 3 * reflectedWork x y (t - u) (dampingVelocity R t)
        (dampingVelocity R u)) R := by
    have h := ((((hasDerivAt_heightDamping R t ht0).add
      (hasDerivAt_heightDamping R u hu0)).mul_const (reflectedEnergy x y (t - u))).add
      (((hasDerivAt_heightDamping R t ht0).sub
        (hasDerivAt_heightDamping R u hu0)).mul_const (reflectedCross x y (t - u)))).div_const 2
    convert h using 1
    · rfl
    · unfold reflectedWork
      ring
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun R _ => (hd R).continuousAt.continuousWithinAt)
    (fun R _ => (hd R).hasDerivWithinAt) ?_
  intro R hR
  rw [interior_Ici] at hR
  exact mul_nonneg (by positivity : 0 ≤ 4 * R ^ 3)
    (dampingVelocity_work_nonneg R x y t u hxy ht hu)

end GaloisForLFunctions.ArithmeticIndexDescent
