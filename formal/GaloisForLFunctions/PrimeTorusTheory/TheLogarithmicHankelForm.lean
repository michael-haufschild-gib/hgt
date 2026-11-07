import Mathlib

/-!
# The logarithmic Hankel form

For real weights `v` of total mass zero and shifts `s ≥ 0`,

`Σ_{i,j} v_i v_j log(x + s_i + s_j) ≤ 0` for `x > 0`.

The `x`-derivative of the form is the Hilbert form `Σ v_i v_j/(x + s_i + s_j) = ∫₀¹ z^{x-1} (Σ v_i z^{s_i})² dz ≥ 0`, and the
form tends to `0` as `x → ∞`. So the phase of a squared word is positive with no cancellation among its Taylor terms, it decreases in
`x`, and multiplying the word by `α + βz` shows that its values at `x, x+1, x+2` are log-convex.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

variable {ι : Type*}

/-- The logarithmic Hankel form. -/
def logForm (S : Finset ι) (v s : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, v i * v j * Real.log (x + s i + s j)

/-- The Hilbert form, the `x`-derivative of `logForm`. -/
def hilbertForm (S : Finset ι) (v s : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, v i * v j / (x + s i + s j)

theorem integral_rpow_unit {r : ℝ} (hr : 0 < r) : ∫ z in (0 : ℝ)..1, z ^ (r - 1) = 1 / r := by
  rw [integral_rpow (Or.inl (by linarith))]
  have e : r - 1 + 1 = r := by ring
  rw [e, Real.one_rpow, Real.zero_rpow hr.ne', sub_zero]

/-- The Hilbert form is the integral of a square against `z^{x-1}`. -/
theorem hilbertForm_eq_integral (S : Finset ι) (v : ι → ℝ) {s : ι → ℝ} (hs : ∀ i ∈ S, 0 ≤ s i)
    {x : ℝ} (hx : 0 < x) :
    hilbertForm S v s x = ∫ z in (0 : ℝ)..1, z ^ (x - 1) * (∑ i ∈ S, v i * z ^ s i) ^ 2 := by
  have hcongr : ∫ z in (0 : ℝ)..1, z ^ (x - 1) * (∑ i ∈ S, v i * z ^ s i) ^ 2 =
      ∫ z in (0 : ℝ)..1, ∑ i ∈ S, ∑ j ∈ S, v i * v j * z ^ (x + s i + s j - 1) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun z hz => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hz
    have hz0 : 0 < z := hz.1
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : x + s i + s j - 1 = (x - 1) + s i + s j := by ring
    rw [e, Real.rpow_add hz0, Real.rpow_add hz0]
    ring
  rw [hcongr]
  have hpos : ∀ i ∈ S, ∀ j ∈ S, 0 < x + s i + s j := fun i hi j hj => by
    have := hs i hi
    have := hs j hj
    linarith
  have hint : ∀ i ∈ S, ∀ j ∈ S, IntervalIntegrable
      (fun z : ℝ => v i * v j * z ^ (x + s i + s j - 1)) MeasureTheory.volume 0 1 := fun i hi j hj =>
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [hpos i hi j hj])).const_mul _
  have hint2 : ∀ i ∈ S, IntervalIntegrable
      (fun z : ℝ => ∑ j ∈ S, v i * v j * z ^ (x + s i + s j - 1)) MeasureTheory.volume 0 1 :=
    fun i hi => by
      have h := IntervalIntegrable.sum S fun j hj => hint i hi j hj
      have e : (fun z : ℝ => ∑ j ∈ S, v i * v j * z ^ (x + s i + s j - 1)) =
          ∑ j ∈ S, fun z : ℝ => v i * v j * z ^ (x + s i + s j - 1) := by
        funext z
        simp [Finset.sum_apply]
      rw [e]
      exact h
  rw [intervalIntegral.integral_finsetSum hint2]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_finsetSum fun j hj => hint i hi j hj]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [intervalIntegral.integral_const_mul, integral_rpow_unit (hpos i hi j hj)]
  ring

theorem hilbertForm_nonneg (S : Finset ι) (v : ι → ℝ) {s : ι → ℝ} (hs : ∀ i ∈ S, 0 ≤ s i)
    {x : ℝ} (hx : 0 < x) : 0 ≤ hilbertForm S v s x := by
  rw [hilbertForm_eq_integral S v hs hx]
  refine intervalIntegral.integral_nonneg zero_le_one fun z hz => ?_
  exact mul_nonneg (Real.rpow_nonneg hz.1 _) (sq_nonneg _)

theorem hasDerivAt_logForm (S : Finset ι) (v : ι → ℝ) {s : ι → ℝ} (hs : ∀ i ∈ S, 0 ≤ s i)
    {x : ℝ} (hx : 0 < x) : HasDerivAt (logForm S v s) (hilbertForm S v s x) x := by
  unfold logForm hilbertForm
  refine HasDerivAt.fun_sum fun i hi => HasDerivAt.fun_sum fun j hj => ?_
  have hpos : x + s i + s j ≠ 0 := by
    have := hs i hi
    have := hs j hj
    positivity
  have h := (((((hasDerivAt_id' x).add_const (s i)).add_const (s j)).log hpos).const_mul
    (v i * v j))
  rw [mul_one_div] at h
  exact h

theorem logForm_mono (S : Finset ι) (v : ι → ℝ) {s : ι → ℝ} (hs : ∀ i ∈ S, 0 ≤ s i) :
    MonotoneOn (logForm S v s) (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · exact fun x hx => (hasDerivAt_logForm S v hs hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_logForm S v hs hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_logForm S v hs hx).deriv]
    exact hilbertForm_nonneg S v hs hx

/-- With total mass zero the form tends to `0`. -/
theorem tendsto_logForm (S : Finset ι) {v : ι → ℝ} {s : ι → ℝ} (hs : ∀ i ∈ S, 0 ≤ s i)
    (hv : ∑ i ∈ S, v i = 0) : Tendsto (logForm S v s) atTop (𝓝 0) := by
  have hlim : Tendsto (fun y : ℝ => ∑ i ∈ S, ∑ j ∈ S, v i * v j * Real.log (1 + (s i + s j) / y))
      atTop (𝓝 (∑ i ∈ S, ∑ j ∈ S, v i * v j * Real.log (1 + 0))) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    refine Tendsto.const_mul _ ?_
    refine (Real.continuousAt_log (by norm_num)).tendsto.comp ?_
    exact tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  simp only [add_zero, Real.log_one, mul_zero, Finset.sum_const_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hsplit : ∀ i ∈ S, ∀ j ∈ S, Real.log (y + s i + s j) =
      Real.log y + Real.log (1 + (s i + s j) / y) := fun i hi j hj => by
    have h1 := hs i hi
    have h2 := hs j hj
    have hp : 0 < 1 + (s i + s j) / y := by positivity
    rw [← Real.log_mul hy.ne' hp.ne']
    congr 1
    field_simp
    ring
  have hzero : ∑ i ∈ S, ∑ j ∈ S, v i * v j * Real.log y = 0 := by
    have e : ∑ i ∈ S, ∑ j ∈ S, v i * v j * Real.log y =
        (∑ i ∈ S, v i) * (∑ j ∈ S, v j) * Real.log y := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
    rw [e, hv]
    ring
  unfold logForm
  rw [← add_zero (∑ i ∈ S, ∑ j ∈ S, v i * v j * Real.log (1 + (s i + s j) / y)), ← hzero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hsplit i hi j hj]
  ring

/-- **The logarithm is conditionally negative definite on Hankel forms.** -/
theorem logForm_nonpos (S : Finset ι) {v : ι → ℝ} {s : ι → ℝ} (hs : ∀ i ∈ S, 0 ≤ s i)
    (hv : ∑ i ∈ S, v i = 0) {x : ℝ} (hx : 0 < x) : logForm S v s x ≤ 0 := by
  refine ge_of_tendsto (tendsto_logForm S hs hv) ?_
  filter_upwards [eventually_ge_atTop x] with y hy
  exact logForm_mono S v hs hx (lt_of_lt_of_le hx hy) hy

/-- Multiplying a word by `α + βz` gives the quadratic form in `x, x+1, x+2`. -/
theorem logForm_quadratic (S : Finset ι) {v : ι → ℝ} {s : ι → ℝ} (hs : ∀ i ∈ S, 0 ≤ s i)
    (hv : ∑ i ∈ S, v i = 0) {x : ℝ} (hx : 0 < x) (α β : ℝ) :
    α ^ 2 * logForm S v s x + 2 * (α * β) * logForm S v s (x + 1) + β ^ 2 * logForm S v s (x + 2)
      ≤ 0 := by
  classical
  set S' : Finset (ι × Bool) := S ×ˢ Finset.univ with hS'
  set a : Bool → ℝ := fun b => if b then β else α with ha
  set v' : ι × Bool → ℝ := fun p => a p.2 * v p.1 with hv'
  set s' : ι × Bool → ℝ := fun p => s p.1 + (if p.2 then 1 else 0) with hs'
  have hs'0 : ∀ p ∈ S', 0 ≤ s' p := by
    intro p hp
    have h1 := hs p.1 (Finset.mem_product.mp hp).1
    simp only [hs']
    split_ifs <;> linarith
  have hv'0 : ∑ p ∈ S', v' p = 0 := by
    rw [hS', Finset.sum_product]
    have : ∀ i ∈ S, ∑ b : Bool, v' (i, b) = (α + β) * v i := fun i _ => by
      simp [hv', ha]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hv, mul_zero]
  have h := logForm_nonpos S' hs'0 hv'0 hx
  have e : logForm S' v' s' x = α ^ 2 * logForm S v s x + 2 * (α * β) * logForm S v s (x + 1) +
      β ^ 2 * logForm S v s (x + 2) := by
    unfold logForm
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, hS', Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_product, Fintype.sum_bool, Finset.sum_add_distrib, hv', hs', ha]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [if_true, if_false, Bool.false_eq_true]
    have e1 : x + (s i + 1) + (s j + 1) = x + 2 + s i + s j := by ring
    have e2 : x + (s i + 1) + (s j + 0) = x + 1 + s i + s j := by ring
    have e3 : x + (s i + 0) + (s j + 1) = x + 1 + s i + s j := by ring
    have e4 : x + (s i + 0) + (s j + 0) = x + s i + s j := by ring
    rw [e1, e2, e3, e4]
    ring
  rwa [e] at h

/-- The phase of a squared word is log-convex along unit steps. -/
theorem logForm_logConvex (S : Finset ι) {v : ι → ℝ} {s : ι → ℝ} (hs : ∀ i ∈ S, 0 ≤ s i)
    (hv : ∑ i ∈ S, v i = 0) {x : ℝ} (hx : 0 < x) (h0 : logForm S v s x < 0) :
    logForm S v s (x + 1) ^ 2 ≤ logForm S v s x * logForm S v s (x + 2) := by
  have h := logForm_quadratic S hs hv hx (-logForm S v s (x + 1)) (logForm S v s x)
  have e : (-logForm S v s (x + 1)) ^ 2 * logForm S v s x +
      2 * (-logForm S v s (x + 1) * logForm S v s x) * logForm S v s (x + 1) +
      logForm S v s x ^ 2 * logForm S v s (x + 2) =
      logForm S v s x * (logForm S v s x * logForm S v s (x + 2) - logForm S v s (x + 1) ^ 2) := by
    ring
  rw [e] at h
  have := nonneg_of_mul_nonpos_right h h0
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
