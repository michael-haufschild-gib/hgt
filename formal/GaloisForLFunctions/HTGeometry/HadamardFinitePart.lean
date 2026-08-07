import Mathlib

/-!
# The Hadamard finite part of the Cauchy kernel on an interval

For a punctured interval the inverse-distance kernel integrates in closed form,

`∫_{(-a,a), |y−x|>ε} dy/|x−y| = log (a² − x²) − 2 log ε`,

so subtracting the value at the centre and adding back `2 v(x) log ε` produces, **for every
`ε` separately and with no limit**, the split

`∫_{|y−x|>ε} v(y)/|x−y| + 2 v(x) log ε
   = ∫_{|y−x|>ε} (v(y) − v(x))/|x−y| + v(x) log (a² − x²)`.

The logarithmic coefficient `v(x)` on the right is therefore an exact invariant of the kernel: it
does not depend on the cutoff, and the remaining integrand is a divided difference, which is
bounded whenever `v` is Lipschitz.  That is the whole mechanism behind the endpoint logarithmic
blow-up of the restricted Weil operator.
-/

open MeasureTheory intervalIntegral Set

namespace GaloisForLFunctions.HTGeometry

/-! ## The punctured kernel integral -/

private theorem hasDerivAt_neg_log_sub {x y : ℝ} (h : y < x) :
    HasDerivAt (fun z : ℝ => -Real.log (x - z)) (x - y)⁻¹ y := by
  have hpos : 0 < x - y := sub_pos.mpr h
  have hinner : HasDerivAt (fun z : ℝ => x - z) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub x
  have hlog : HasDerivAt (fun z : ℝ => Real.log (x - z)) (-(x - y)⁻¹) y := by
    have hcomp := (Real.hasDerivAt_log hpos.ne').comp y hinner
    have : (x - y)⁻¹ * (-1 : ℝ) = -(x - y)⁻¹ := by ring
    rw [this] at hcomp
    exact hcomp
  have hneg := hlog.neg
  rw [neg_neg] at hneg
  exact hneg

private theorem hasDerivAt_log_sub {x y : ℝ} (h : x < y) :
    HasDerivAt (fun z : ℝ => Real.log (z - x)) (y - x)⁻¹ y := by
  have hpos : 0 < y - x := sub_pos.mpr h
  have hinner : HasDerivAt (fun z : ℝ => z - x) 1 y := by
    simpa using (hasDerivAt_id y).sub_const x
  have hcomp := (Real.hasDerivAt_log hpos.ne').comp y hinner
  have h1 : (y - x)⁻¹ * (1 : ℝ) = (y - x)⁻¹ := by ring
  rw [h1] at hcomp
  exact hcomp

/-- Left half of the punctured inverse-distance integral. -/
theorem integral_left_inv_sub {a x ε : ℝ} (hε : 0 < ε) (hleft : -a ≤ x - ε) :
    (∫ y in (-a)..(x - ε), (x - y)⁻¹) = Real.log (x + a) - Real.log ε := by
  have hderiv : ∀ y ∈ uIcc (-a) (x - ε), HasDerivAt (fun z : ℝ => -Real.log (x - z)) (x - y)⁻¹ y := by
    intro y hy
    rw [uIcc_of_le hleft, mem_Icc] at hy
    exact hasDerivAt_neg_log_sub (by linarith [hy.2])
  have hint : IntervalIntegrable (fun y : ℝ => (x - y)⁻¹) volume (-a) (x - ε) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hleft]
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro y hy
    rw [mem_Icc] at hy
    intro hc
    nlinarith [hy.2]
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : x - (x - ε) = ε := by ring
  have h2 : x - -a = x + a := by ring
  rw [h1, h2]
  ring

/-- Right half of the punctured inverse-distance integral. -/
theorem integral_right_inv_sub {a x ε : ℝ} (hε : 0 < ε) (hright : x + ε ≤ a) :
    (∫ y in (x + ε)..a, (y - x)⁻¹) = Real.log (a - x) - Real.log ε := by
  have hderiv : ∀ y ∈ uIcc (x + ε) a, HasDerivAt (fun z : ℝ => Real.log (z - x)) (y - x)⁻¹ y := by
    intro y hy
    rw [uIcc_of_le hright, mem_Icc] at hy
    exact hasDerivAt_log_sub (by linarith [hy.1])
  have hint : IntervalIntegrable (fun y : ℝ => (y - x)⁻¹) volume (x + ε) a := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hright]
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro y hy
    rw [mem_Icc] at hy
    intro hc
    nlinarith [hy.1]
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : x + ε - x = ε := by ring
  rw [h1]

/-- **Punctured kernel integral.**  The inverse-distance kernel on the punctured interval has the
closed form `log (a² − x²) − 2 log ε`. -/
theorem integral_punctured_inv_dist {a x ε : ℝ} (hxa : -a < x) (hax : x < a) (hε : 0 < ε)
    (hleft : -a ≤ x - ε) (hright : x + ε ≤ a) :
    ((∫ y in (-a)..(x - ε), (x - y)⁻¹) + ∫ y in (x + ε)..a, (y - x)⁻¹) =
      Real.log (a ^ 2 - x ^ 2) - 2 * Real.log ε := by
  rw [integral_left_inv_sub hε hleft, integral_right_inv_sub hε hright]
  have hxa' : 0 < x + a := by linarith
  have hax' : 0 < a - x := by linarith
  have hfac : a ^ 2 - x ^ 2 = (x + a) * (a - x) := by ring
  rw [hfac, Real.log_mul hxa'.ne' hax'.ne']
  ring

/-! ## The finite-part split -/

private theorem intervalIntegrable_left {a x ε : ℝ} (v : ℝ → ℝ) (hv : Continuous v) (hε : 0 < ε)
    (hleft : -a ≤ x - ε) : IntervalIntegrable (fun y : ℝ => v y * (x - y)⁻¹) volume (-a) (x - ε) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hleft]
  refine hv.continuousOn.mul (ContinuousOn.inv₀ (by fun_prop) ?_)
  intro y hy
  rw [mem_Icc] at hy
  intro hc
  nlinarith [hy.2]

private theorem intervalIntegrable_right {a x ε : ℝ} (v : ℝ → ℝ) (hv : Continuous v) (hε : 0 < ε)
    (hright : x + ε ≤ a) : IntervalIntegrable (fun y : ℝ => v y * (y - x)⁻¹) volume (x + ε) a := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hright]
  refine hv.continuousOn.mul (ContinuousOn.inv₀ (by fun_prop) ?_)
  intro y hy
  rw [mem_Icc] at hy
  intro hc
  nlinarith [hy.1]

/-- The cutoff finite part of the Cauchy kernel against a weight. -/
noncomputable def cutoffFinitePart (a x ε : ℝ) (v : ℝ → ℝ) : ℝ :=
  (∫ y in (-a)..(x - ε), v y * (x - y)⁻¹) + (∫ y in (x + ε)..a, v y * (y - x)⁻¹) +
    2 * v x * Real.log ε

/-- The cutoff divided-difference integral. -/
noncomputable def cutoffDividedDifference (a x ε : ℝ) (v : ℝ → ℝ) : ℝ :=
  (∫ y in (-a)..(x - ε), (v y - v x) * (x - y)⁻¹) + ∫ y in (x + ε)..a, (v y - v x) * (y - x)⁻¹

/-- **Exact finite-part split.**  For every cutoff, the finite part is the divided-difference
integral plus the *cutoff-independent* logarithmic term `v(x) log (a² − x²)`. -/
theorem cutoffFinitePart_eq {a x ε : ℝ} (v : ℝ → ℝ) (hv : Continuous v)
    (hxa : -a < x) (hax : x < a) (hε : 0 < ε) (hleft : -a ≤ x - ε) (hright : x + ε ≤ a) :
    cutoffFinitePart a x ε v =
      cutoffDividedDifference a x ε v + v x * Real.log (a ^ 2 - x ^ 2) := by
  have hL := intervalIntegrable_left v hv hε hleft
  have hR := intervalIntegrable_right v hv hε hright
  have hcL : IntervalIntegrable (fun y : ℝ => v x * (x - y)⁻¹) volume (-a) (x - ε) :=
    intervalIntegrable_left (fun _ => v x) continuous_const hε hleft
  have hcR : IntervalIntegrable (fun y : ℝ => v x * (y - x)⁻¹) volume (x + ε) a :=
    intervalIntegrable_right (fun _ => v x) continuous_const hε hright
  have hsplitL : (∫ y in (-a)..(x - ε), (v y - v x) * (x - y)⁻¹) =
      (∫ y in (-a)..(x - ε), v y * (x - y)⁻¹) - ∫ y in (-a)..(x - ε), v x * (x - y)⁻¹ := by
    rw [← intervalIntegral.integral_sub hL hcL]
    exact intervalIntegral.integral_congr fun y _ => by ring
  have hsplitR : (∫ y in (x + ε)..a, (v y - v x) * (y - x)⁻¹) =
      (∫ y in (x + ε)..a, v y * (y - x)⁻¹) - ∫ y in (x + ε)..a, v x * (y - x)⁻¹ := by
    rw [← intervalIntegral.integral_sub hR hcR]
    exact intervalIntegral.integral_congr fun y _ => by ring
  have hconstL : (∫ y in (-a)..(x - ε), v x * (x - y)⁻¹) =
      v x * ∫ y in (-a)..(x - ε), (x - y)⁻¹ := by
    rw [intervalIntegral.integral_const_mul]
  have hconstR : (∫ y in (x + ε)..a, v x * (y - x)⁻¹) =
      v x * ∫ y in (x + ε)..a, (y - x)⁻¹ := by
    rw [intervalIntegral.integral_const_mul]
  have hker := integral_punctured_inv_dist hxa hax hε hleft hright
  rw [cutoffFinitePart, cutoffDividedDifference, hsplitL, hsplitR, hconstL, hconstR]
  first
    | linear_combination (v x) * hker
    | linear_combination (-(v x)) * hker

end GaloisForLFunctions.HTGeometry
