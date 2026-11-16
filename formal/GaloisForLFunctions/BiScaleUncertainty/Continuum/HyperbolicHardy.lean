import GaloisForLFunctions.BiScaleUncertainty.ContinuumShearDirichlet

/-!
# Hyperbolic Hardy energy with its exact square remainder

The unit-divergence field in Drach's hyperbolic-area argument
(https://arxiv.org/abs/2611.17326, proof of Lemma 3) becomes the logarithmic
weight `exp (-x)`. Completing the square in the corpus's continuum shear energy
separates one quarter of the hyperbolic mass, a nonnegative endpoint flux, and
an explicit square remainder. The state is the primitive of an arbitrary
continuous velocity, anchored at the lower endpoint.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace GaloisForLFunctions.BiScaleUncertainty.ContinuumShear

/-- The logarithmic primitive with its lower boundary value removed. -/
def anchoredLogPrimitive (q : C(ℝ, ℝ)) (u x : ℝ) : ℝ :=
  logPrimitive q x - logPrimitive q u

/-- Logarithmic velocity of the physical primitive. -/
def logVelocity (q : C(ℝ, ℝ)) (x : ℝ) : ℝ := q (Real.exp x) * Real.exp x

theorem hasDerivAt_anchoredLogPrimitive (q : C(ℝ, ℝ)) (u x : ℝ) :
    HasDerivAt (anchoredLogPrimitive q u) (logVelocity q x) x :=
  (hasDerivAt_logPrimitive q x).sub_const _

theorem continuous_anchoredLogPrimitive (q : C(ℝ, ℝ)) (u : ℝ) :
    Continuous (anchoredLogPrimitive q u) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_anchoredLogPrimitive q u x).continuousAt

theorem continuous_logVelocity (q : C(ℝ, ℝ)) : Continuous (logVelocity q) :=
  (q.continuous.comp Real.continuous_exp).mul Real.continuous_exp

/-- Hyperbolic vertical mass in logarithmic coordinates. -/
def hyperbolicMass (q : C(ℝ, ℝ)) (u v : ℝ) : ℝ :=
  ∫ x in u..v, Real.exp (-x) * (anchoredLogPrimitive q u x)^2

/-- The square left by the hyperbolic ground-state transformation. -/
def hardyRemainder (q : C(ℝ, ℝ)) (u v : ℝ) : ℝ :=
  ∫ x in u..v, Real.exp (-x) *
    (logVelocity q x - anchoredLogPrimitive q u x / 2)^2

private theorem boundary_flux (q : C(ℝ, ℝ)) (u v : ℝ) :
    (∫ x in u..v,
      (Real.exp (-x) * anchoredLogPrimitive q u x * logVelocity q x -
        Real.exp (-x) * (anchoredLogPrimitive q u x)^2 / 2)) =
      Real.exp (-v) * (anchoredLogPrimitive q u v)^2 / 2 := by
  have hf := continuous_anchoredLogPrimitive q u
  have hv := continuous_logVelocity q
  have he : Continuous (fun x : ℝ => Real.exp (-x)) := Real.continuous_exp.comp continuous_neg
  have hd (x : ℝ) : HasDerivAt
      (fun x => Real.exp (-x) * (anchoredLogPrimitive q u x)^2 / 2)
      (Real.exp (-x) * anchoredLogPrimitive q u x * logVelocity q x -
        Real.exp (-x) * (anchoredLogPrimitive q u x)^2 / 2) x := by
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using ((hasDerivAt_id x).neg.exp)
    convert (hexp.mul ((hasDerivAt_anchoredLogPrimitive q u x).pow 2)).div_const 2
      using 1 <;> first | rfl | (simp only [Pi.pow_apply]; ring)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x)
    ((((he.mul hf).mul hv).sub ((he.mul (hf.pow 2)).div_const 2)).intervalIntegrable u v)
  simpa only [anchoredLogPrimitive, sub_self, pow_two, mul_zero, zero_div, sub_zero] using h

/-- Exact hyperbolic energy decomposition, valid also for oppositely oriented endpoints. -/
theorem hyperbolic_hardy_decomposition (q : C(ℝ, ℝ)) (u v : ℝ) :
    energy q (Real.exp u) (Real.exp v) =
      hyperbolicMass q u v / 4 + hardyRemainder q u v +
        Real.exp (-v) * (anchoredLogPrimitive q u v)^2 / 2 := by
  have hf := continuous_anchoredLogPrimitive q u
  have hv := continuous_logVelocity q
  have he : Continuous (fun x : ℝ => Real.exp (-x)) := Real.continuous_exp.comp continuous_neg
  have hm := ((he.mul (hf.pow 2)).div_const 4).intervalIntegrable (μ := volume) u v
  have hr := (he.mul ((hv.sub (hf.div_const 2)).pow 2)).intervalIntegrable (μ := volume) u v
  have hb := (((he.mul hf).mul hv).sub
    ((he.mul (hf.pow 2)).div_const 2)).intervalIntegrable (μ := volume) u v
  simp only [Pi.mul_apply, Pi.pow_apply] at hm hr hb
  rw [← log_energy_eq]
  simp only [(hasDerivAt_logPrimitive q _).deriv]
  calc
    _ = ∫ x in u..v,
        ((Real.exp (-x) * (anchoredLogPrimitive q u x)^2 / 4 +
          Real.exp (-x) * (logVelocity q x - anchoredLogPrimitive q u x / 2)^2) +
          (Real.exp (-x) * anchoredLogPrimitive q u x * logVelocity q x -
            Real.exp (-x) * (anchoredLogPrimitive q u x)^2 / 2)) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [logVelocity]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (f := fun x => Real.exp (-x) * (anchoredLogPrimitive q u x)^2 / 4 +
          Real.exp (-x) * (logVelocity q x - anchoredLogPrimitive q u x / 2)^2)
        (g := fun x => Real.exp (-x) * anchoredLogPrimitive q u x * logVelocity q x -
          Real.exp (-x) * (anchoredLogPrimitive q u x)^2 / 2) (hm.add hr) hb,
        intervalIntegral.integral_add
          (f := fun x => Real.exp (-x) * (anchoredLogPrimitive q u x)^2 / 4)
          (g := fun x => Real.exp (-x) *
            (logVelocity q x - anchoredLogPrimitive q u x / 2)^2) hm hr,
        intervalIntegral.integral_div,
        boundary_flux]
      rfl

/-- Every anchored continuum state pays the hyperbolic one-quarter mass cost. -/
theorem hyperbolic_hardy_bound (q : C(ℝ, ℝ)) (u : ℝ) (r : ℝ≥0) :
    hyperbolicMass q u (u + r) / 4 +
        Real.exp (-(u + r)) * (anchoredLogPrimitive q u (u + r))^2 / 2 ≤
      energy q (Real.exp u) (Real.exp (u + r)) := by
  rw [hyperbolic_hardy_decomposition]
  have hrem : 0 ≤ hardyRemainder q u (u + r) :=
    intervalIntegral.integral_nonneg_of_forall (le_add_of_nonneg_right r.coe_nonneg)
      (fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  linarith only [hrem]

#print axioms hyperbolic_hardy_decomposition
#print axioms hyperbolic_hardy_bound

end GaloisForLFunctions.BiScaleUncertainty.ContinuumShear
