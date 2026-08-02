import GaloisForLFunctions.HTGeometry.TorusCoveringNumbers

/-!
# The circle embeds bi-Lipschitzly in the plane

The unit circle `ℝ/ℤ` embeds in `ℂ` by `x ↦ e^{2πix}`.  The chord between two images is
`2 |sin(π s)|`, where `s` is the representative of the difference in `[-1/2, 1/2]`, and on that
interval the sine is trapped between `2s` and `πs`.  So the embedding distorts distances by at most
a factor `2π` in one direction and `4` in the other.

This is the analytic half of the completed-orbit dimension theorem: it turns the metric of the
phase torus into the metric of the reporter space.
-/

open Complex Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The circle, embedded in the plane. -/
def circleEmbed (x : UnitAddCircle) : ℂ := (AddCircle.toCircle x : ℂ)

theorem circleEmbed_coe (u : ℝ) :
    circleEmbed ((u : ℝ) : UnitAddCircle) = Complex.exp (2 * Real.pi * u * Complex.I) := by
  rw [circleEmbed, AddCircle.toCircle_apply_mk]
  simp only [Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem norm_circleEmbed (x : UnitAddCircle) : ‖circleEmbed x‖ = 1 := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [circleEmbed_coe]
  rw [show (2 * (Real.pi : ℂ) * (u : ℂ) * Complex.I) = ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem circleEmbed_sub (x y : UnitAddCircle) :
    circleEmbed x - circleEmbed y = circleEmbed y * (circleEmbed (x - y) - 1) := by
  have hmul : circleEmbed (x - y) * circleEmbed y = circleEmbed x := by
    rw [circleEmbed, circleEmbed, circleEmbed, ← Circle.coe_mul, ← AddCircle.toCircle_add]
    congr 2
    abel
  rw [mul_sub, mul_one, mul_comm (circleEmbed y) (circleEmbed (x - y)), hmul]

/-- The chord subtended by a real angle. -/
theorem norm_exp_two_pi_sub_one (u : ℝ) :
    ‖Complex.exp (2 * Real.pi * u * Complex.I) - 1‖ = 2 * |Real.sin (Real.pi * u)| := by
  have hfac : Complex.exp (2 * (Real.pi : ℂ) * (u : ℂ) * Complex.I) - 1
      = Complex.exp ((Real.pi : ℂ) * (u : ℂ) * Complex.I) *
        (Complex.exp ((Real.pi : ℂ) * (u : ℂ) * Complex.I)
          - Complex.exp (-((Real.pi : ℂ) * (u : ℂ) * Complex.I))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    congr 2
    ring
  have hdiff : Complex.exp ((Real.pi : ℂ) * (u : ℂ) * Complex.I)
      - Complex.exp (-((Real.pi : ℂ) * (u : ℂ) * Complex.I))
      = 2 * Complex.sin ((Real.pi : ℂ) * (u : ℂ)) * Complex.I := by
    rw [Complex.sin]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hnorm1 : ‖Complex.exp ((Real.pi : ℂ) * (u : ℂ) * Complex.I)‖ = 1 := by
    rw [show ((Real.pi : ℂ) * (u : ℂ) * Complex.I) = ((Real.pi * u : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hfac, hdiff, norm_mul, hnorm1, one_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
  rw [show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
  rw [show ((Real.pi : ℂ) * (u : ℂ)) = ((Real.pi * u : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sin, Complex.norm_real]
  simp [Real.norm_eq_abs]

/-- Two-sided chord bound in terms of the circle norm. -/
theorem norm_circleEmbed_sub_one_bounds (x : UnitAddCircle) :
    4 * ‖x‖ ≤ ‖circleEmbed x - 1‖ ∧ ‖circleEmbed x - 1‖ ≤ 2 * Real.pi * ‖x‖ := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  set w : ℝ := u - round u with hw
  have hnorm : ‖((u : ℝ) : UnitAddCircle)‖ = |w| := by
    rw [UnitAddCircle.norm_eq, hw]
  have hper : Complex.exp (2 * Real.pi * u * Complex.I)
      = Complex.exp (2 * Real.pi * w * Complex.I) := by
    have hint : (u : ℂ) = (w : ℂ) + ((round u : ℤ) : ℂ) := by
      rw [hw]
      push_cast
      ring
    rw [hint]
    rw [show 2 * (Real.pi : ℂ) * ((w : ℂ) + ((round u : ℤ) : ℂ)) * Complex.I
        = 2 * (Real.pi : ℂ) * (w : ℂ) * Complex.I
          + ((round u : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hwabs : |w| ≤ 1 / 2 := by
    rw [hw]
    exact abs_sub_round u
  have hchord : ‖circleEmbed ((u : ℝ) : UnitAddCircle) - 1‖ = 2 * |Real.sin (Real.pi * w)| := by
    rw [circleEmbed_coe, hper, norm_exp_two_pi_sub_one]
  rw [hnorm, hchord]
  constructor
  · -- lower bound: `2 |sin (π w)| ≥ 4 |w|`
    rcases le_or_gt 0 w with hw0 | hw0
    · have hpi : 0 ≤ Real.pi * w := by positivity
      have hpi2 : Real.pi * w ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hwabs, abs_of_nonneg hw0]
      have hsin := Real.mul_le_sin hpi hpi2
      rw [abs_of_nonneg hw0, abs_of_nonneg (by
        refine Real.sin_nonneg_of_nonneg_of_le_pi hpi ?_
        nlinarith [Real.pi_pos])]
      have hpi' : Real.pi > 0 := Real.pi_pos
      have : 2 / Real.pi * (Real.pi * w) = 2 * w := by field_simp
      nlinarith [hsin, this]
    · have hw0' : 0 ≤ -w := by linarith
      have hpi : 0 ≤ Real.pi * (-w) := by positivity
      have hpi2 : Real.pi * (-w) ≤ Real.pi / 2 := by
        nlinarith [Real.pi_pos, hwabs, abs_of_neg hw0]
      have hsin := Real.mul_le_sin hpi hpi2
      have hsinneg : Real.sin (Real.pi * w) = -Real.sin (Real.pi * (-w)) := by
        rw [show Real.pi * (-w) = -(Real.pi * w) by ring, Real.sin_neg, neg_neg]
      have hsinpos : 0 ≤ Real.sin (Real.pi * (-w)) := by
        refine Real.sin_nonneg_of_nonneg_of_le_pi hpi ?_
        nlinarith [Real.pi_pos]
      rw [abs_of_neg hw0, hsinneg, abs_neg, abs_of_nonneg hsinpos]
      have hpi' : Real.pi > 0 := Real.pi_pos
      have hid : 2 / Real.pi * (Real.pi * (-w)) = 2 * (-w) := by field_simp
      nlinarith [hsin, hid]
  · -- upper bound: `2 |sin (π w)| ≤ 2 π |w|`
    have hsinle : |Real.sin (Real.pi * w)| ≤ |Real.pi * w| := Real.abs_sin_le_abs
    rw [abs_mul, abs_of_pos Real.pi_pos] at hsinle
    nlinarith [hsinle, abs_nonneg w, Real.pi_pos]

theorem dist_circleEmbed (x y : UnitAddCircle) :
    dist (circleEmbed x) (circleEmbed y) = ‖circleEmbed (x - y) - 1‖ := by
  rw [dist_eq_norm, circleEmbed_sub, norm_mul, norm_circleEmbed, one_mul]

theorem dist_circleEmbed_bounds (x y : UnitAddCircle) :
    4 * dist x y ≤ dist (circleEmbed x) (circleEmbed y) ∧
      dist (circleEmbed x) (circleEmbed y) ≤ 2 * Real.pi * dist x y := by
  have hd : dist x y = ‖x - y‖ := by rw [dist_eq_norm]
  rw [dist_circleEmbed, hd]
  exact norm_circleEmbed_sub_one_bounds (x - y)

theorem lipschitzWith_circleEmbed :
    LipschitzWith (Real.toNNReal (2 * Real.pi)) circleEmbed := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  exact (dist_circleEmbed_bounds x y).2

theorem antilipschitzWith_circleEmbed :
    AntilipschitzWith (Real.toNNReal (1 / 4)) circleEmbed := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  have hb := (dist_circleEmbed_bounds x y).1
  linarith

/-- The phase torus, embedded coordinatewise in the plane. -/
def torusEmbed {k : Type*} (x : UnitAddTorus k) : k → ℂ := fun i => circleEmbed (x i)

theorem lipschitzWith_torusEmbed {k : Type*} [Fintype k] :
    LipschitzWith (Real.toNNReal (2 * Real.pi)) (torusEmbed (k := k)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
  refine le_trans (dist_circleEmbed_bounds (x i) (y i)).2 ?_
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (by positivity)

theorem antilipschitzWith_torusEmbed {k : Type*} [Fintype k] :
    AntilipschitzWith (Real.toNNReal (1 / 4)) (torusEmbed (k := k)) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
  have hb := (dist_circleEmbed_bounds (x i) (y i)).1
  have hmono : dist (circleEmbed (x i)) (circleEmbed (y i))
      ≤ dist (torusEmbed x) (torusEmbed y) := by
    have hpi := dist_le_pi_dist (torusEmbed x) (torusEmbed y) i
    exact hpi
  linarith

end

end GaloisForLFunctions.HTGeometry
