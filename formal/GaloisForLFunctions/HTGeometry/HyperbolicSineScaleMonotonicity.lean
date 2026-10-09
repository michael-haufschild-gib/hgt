import GaloisForLFunctions.HTGeometry.HyperbolicBounds

/-!
# Strict hyperbolic scale comparison

The analytic mechanism of arXiv:2609.20367, Lemma 6.38 and
Corollary 6.39: `sinh x / x` increases strictly on the positive axis.
Consequently its reciprocal square decreases strictly. This strengthens
the corpus's non-strict hyperbolic bound and supplies a scale comparison
independent of the paper's operator arguments.
-/

namespace HTGeometry

/-- The derivative numerator for `sinh x / x` increases from zero. -/
theorem strictMonoOn_mul_cosh_sub_sinh :
    StrictMonoOn (fun x : ℝ => x * Real.cosh x - Real.sinh x) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
  intro x hx
  rw [interior_Ici] at hx
  have hd : HasDerivAt (fun y : ℝ => y * Real.cosh y - Real.sinh y)
      (x * Real.sinh x) x := by
    convert! ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1
    simp
  rw [hd.deriv]
  have hs := Real.sinh_pos_iff.mpr hx
  nlinarith [mul_pos hx hs]

/-- Strict scale law behind the two-scale exponential comparison. -/
theorem strictMonoOn_sinh_div_self :
    StrictMonoOn (fun x : ℝ => Real.sinh x / x) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    ((Real.continuous_sinh.continuousOn).div continuousOn_id (fun x hx => ne_of_gt hx))
  intro x hx
  rw [interior_Ioi] at hx
  rw [((Real.hasDerivAt_sinh x).div (hasDerivAt_id x) hx.ne').deriv]
  apply div_pos _ (sq_pos_of_pos hx)
  have hx0 : 0 < x := hx
  have h := strictMonoOn_mul_cosh_sub_sinh (by simp) hx0.le hx0
  simp only [id_eq, mul_one, zero_mul, Real.sinh_zero, sub_zero] at h ⊢
  nlinarith

/-- Squared reciprocal sinh response decreases strictly with positive scale. -/
theorem strictAntiOn_self_div_sinh_sq :
    StrictAntiOn (fun x : ℝ => (x / Real.sinh x) ^ 2) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hsx : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hsy : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
  have h := strictMonoOn_sinh_div_self hx hy hxy
  have hc : y / Real.sinh y < x / Real.sinh x := by
    apply (div_lt_div_iff₀ hsy hsx).mpr
    have h' := (div_lt_div_iff₀ hx hy).mp h
    nlinarith
  nlinarith [div_pos hy hsy, div_pos hx hsx]

/-- A premise-free parameterization of every strict positive scale comparison. -/
theorem sinh_exp_scale_strict (t r : ℝ) :
    (1 + Real.exp r) * Real.sinh (Real.exp t) <
      Real.sinh ((1 + Real.exp r) * Real.exp t) := by
  have ht := Real.exp_pos t
  have hr := Real.exp_pos r
  have h := strictMonoOn_sinh_div_self ht
    (show 0 < (1 + Real.exp r) * Real.exp t by positivity)
    (show Real.exp t < (1 + Real.exp r) * Real.exp t by nlinarith)
  have h' := (div_lt_div_iff₀ ht (show 0 < (1 + Real.exp r) * Real.exp t by positivity)).mp h
  nlinarith

/-- The Bose fluctuation factor is the squared reciprocal hyperbolic sine,
including the totalized value at zero. -/
theorem bose_fluctuation_eq_sinh (x : ℝ) :
    Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 =
      1 / (4 * Real.sinh (x / 2) ^ 2) := by
  have he : Real.exp (-x) = (Real.exp (x / 2))⁻¹ ^ 2 := by
    rw [show -x = -(x / 2) + -(x / 2) by ring, Real.exp_add, Real.exp_neg]
    ring
  have hs : Real.sinh (x / 2) =
      (Real.exp (x / 2) - (Real.exp (x / 2))⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg]
  rw [he, hs]
  by_cases h : Real.exp (x / 2) = 1
  · simp [h]
  have he0 := Real.exp_pos (x / 2)
  have he2 : Real.exp (x / 2) ^ 2 - 1 ≠ 0 := by
    intro hz
    have : Real.exp (x / 2) = 1 := by nlinarith
    exact h this
  field_simp
  ring

/-- The paper's terminal scalar response decreases on the full positive axis. -/
theorem strictAntiOn_bose_scaled_fluctuation :
    StrictAntiOn (fun x : ℝ => x ^ 2 * Real.exp (-x) /
      (1 - Real.exp (-x)) ^ 2) (Set.Ioi 0) := by
  have heq (x : ℝ) : x ^ 2 * Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 =
      ((x / 2) / Real.sinh (x / 2)) ^ 2 := by
    rw [mul_div_assoc, bose_fluctuation_eq_sinh]
    ring
  intro x hx y hy hxy
  dsimp only
  rw [heq, heq]
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hx' : x / 2 ∈ Set.Ioi (0 : ℝ) := by change (0 : ℝ) < x / 2; linarith
  have hy' : y / 2 ∈ Set.Ioi (0 : ℝ) := by change (0 : ℝ) < y / 2; linarith
  exact strictAntiOn_self_div_sinh_sq hx' hy' (by linarith)

end HTGeometry
