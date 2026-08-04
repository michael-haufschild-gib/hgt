import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The multiplicative covariance anomaly of a finite family of multipliers

Given multipliers `u_v : ℝ → ℂ` with `u_v(0) = 1`, the difference between the product and the sum of
its one-place increments,

```text
C_s(t) = prod_(v in s) u_v(t) - 1 - sum_(v in s) (u_v(t) - 1),
```

is a purely higher-order object.  This module proves the three structural facts about it that are
independent of what the multipliers are:

* `covarianceAnomaly_eq_sum_powerset` — the **factorization-independent** expansion
  `C_s = sum_(|I| >= 2) prod_(v in I) (u_v - 1)`.  It shows `C_s` does not depend on any pairing or
  splitting of the places: it is the complete higher-than-linear part of the product.
* `covarianceAnomaly_zero`, `hasDerivAt_covarianceAnomaly` — the constant and linear jets at the seam
  vanish.
* `tendsto_covarianceAnomaly_div_sq` — the quadratic jet is exactly
  `((sum c_v)^2 - sum c_v^2)/2`, where `c_v = u_v'(0)`.  Equivalently `C_s''(0) = 2 sum_(v<w) c_v c_w`.

The proofs of the two jet statements go through one algebraic recursion,
`covarianceAnomaly_insert`, rather than through the powerset expansion; that keeps them free of
subset-cardinality combinatorics and needs only *first* derivatives, even for the quadratic jet.

`offDiagCharge_eq_sum_offDiag` records the companion identity
`(sum b)^2 - sum b^2 = sum_(v != w) b_v b_w`, which is what makes the quadratic jet amenable to a
termwise lower bound.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Finset Filter Topology

variable {ι : Type*} [DecidableEq ι]

/-- The sum of the one-place multiplier increments. -/
def multiplierDefectSum (s : Finset ι) (u : ι → ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ v ∈ s, (u v t - 1)

/-- The multiplicative covariance anomaly: the product minus one minus the sum of the one-place
increments. -/
def covarianceAnomaly (s : Finset ι) (u : ι → ℝ → ℂ) (t : ℝ) : ℂ :=
  (∏ v ∈ s, u v t) - 1 - multiplierDefectSum s u t

/-! ## Factorization independence -/

/-- The elementary subset expansion of a finite product of `1 + a v`. -/
theorem prod_one_add_sub_one_sub_sum (s : Finset ι) (a : ι → ℂ) :
    (∏ v ∈ s, (1 + a v)) - 1 - ∑ v ∈ s, a v
      = ∑ I ∈ s.powerset.filter fun I => 2 ≤ I.card, ∏ v ∈ I, a v := by
  have hexp : (∏ v ∈ s, (1 + a v)) = ∑ I ∈ s.powerset, ∏ v ∈ I, a v := by
    have hcomm : (∏ v ∈ s, (1 + a v)) = ∏ v ∈ s, (a v + 1) :=
      Finset.prod_congr rfl fun v _ => add_comm 1 (a v)
    rw [hcomm, Finset.prod_add]
    exact Finset.sum_congr rfl fun I _ => by rw [Finset.prod_const_one, mul_one]
  have hfilter : (s.powerset.filter fun I => ¬ I.card ≤ 1)
      = s.powerset.filter fun I => 2 ≤ I.card := by
    ext I
    simp only [Finset.mem_filter, not_le]
    exact and_congr_right fun _ => by omega
  have hsplit : (∑ I ∈ s.powerset, ∏ v ∈ I, a v)
      = (∑ I ∈ s.powerset.filter fun I => I.card ≤ 1, ∏ v ∈ I, a v)
        + ∑ I ∈ s.powerset.filter fun I => 2 ≤ I.card, ∏ v ∈ I, a v := by
    rw [← hfilter]
    exact (Finset.sum_filter_add_sum_filter_not s.powerset _ _).symm
  have hlowset : (s.powerset.filter fun I => I.card ≤ 1)
      = insert (∅ : Finset ι) (s.image fun v => ({v} : Finset ι)) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨hsub, hcard⟩
      rcases Nat.lt_or_ge I.card 1 with h | h
      · exact Or.inl (Finset.card_eq_zero.mp (by omega))
      · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (show I.card = 1 from le_antisymm hcard h)
        exact Or.inr ⟨v, hsub (by rw [hv]; exact Finset.mem_singleton_self v), hv.symm⟩
    · rintro (rfl | ⟨v, hv, rfl⟩)
      · exact ⟨Finset.empty_subset s, by simp⟩
      · exact ⟨Finset.singleton_subset_iff.mpr hv, by simp⟩
  have hnotmem : (∅ : Finset ι) ∉ s.image fun v => ({v} : Finset ι) := by
    simp only [Finset.mem_image, not_exists]
    intro v hv
    exact (Finset.singleton_ne_empty v) hv.2
  have hlow : (∑ I ∈ s.powerset.filter fun I => I.card ≤ 1, ∏ v ∈ I, a v)
      = 1 + ∑ v ∈ s, a v := by
    rw [hlowset, Finset.sum_insert hnotmem, Finset.prod_empty,
      Finset.sum_image fun v _ w _ h => Finset.singleton_injective h]
    exact congrArg _ (Finset.sum_congr rfl fun v _ => by simp)
  rw [hexp, hsplit, hlow]
  ring

/-- **Equation (7).**  The anomaly is the sum over all subsets of size at least two of the products of
the one-place increments.  In particular it is independent of any splitting or pairing of the
places. -/
theorem covarianceAnomaly_eq_sum_powerset (s : Finset ι) (u : ι → ℝ → ℂ) (t : ℝ) :
    covarianceAnomaly s u t
      = ∑ I ∈ s.powerset.filter fun I => 2 ≤ I.card, ∏ v ∈ I, (u v t - 1) := by
  have h := prod_one_add_sub_one_sub_sum s fun v => u v t - 1
  rw [covarianceAnomaly, multiplierDefectSum, ← h]
  refine congrArg₂ _ (congrArg₂ _ ?_ rfl) rfl
  exact Finset.prod_congr rfl fun v _ => by ring

/-! ## The insertion recursion -/

theorem multiplierDefectSum_insert {x : ι} {s : Finset ι} (hx : x ∉ s) (u : ι → ℝ → ℂ) (t : ℝ) :
    multiplierDefectSum (insert x s) u t = (u x t - 1) + multiplierDefectSum s u t := by
  rw [multiplierDefectSum, multiplierDefectSum, Finset.sum_insert hx]

/-- The recursion that carries both jet computations.  Adding a place multiplies the previous anomaly
by the new multiplier and adds the product of the new increment with the previous total increment. -/
theorem covarianceAnomaly_insert {x : ι} {s : Finset ι} (hx : x ∉ s) (u : ι → ℝ → ℂ) (t : ℝ) :
    covarianceAnomaly (insert x s) u t
      = u x t * covarianceAnomaly s u t + (u x t - 1) * multiplierDefectSum s u t := by
  rw [covarianceAnomaly, covarianceAnomaly, Finset.prod_insert hx,
    multiplierDefectSum_insert hx]
  ring

/-! ## The vanishing constant and linear jets -/

omit [DecidableEq ι] in
theorem multiplierDefectSum_zero {u : ι → ℝ → ℂ} (hu : ∀ v, u v 0 = 1) (s : Finset ι) :
    multiplierDefectSum s u 0 = 0 := by
  rw [multiplierDefectSum]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [hu v, sub_self]

omit [DecidableEq ι] in
theorem hasDerivAt_multiplierDefectSum {u : ι → ℝ → ℂ} {c : ι → ℂ}
    (hd : ∀ v, HasDerivAt (u v) (c v) 0) (s : Finset ι) :
    HasDerivAt (multiplierDefectSum s u) (∑ v ∈ s, c v) 0 := by
  have h : HasDerivAt (fun t => ∑ v ∈ s, (u v t - 1)) (∑ v ∈ s, c v) 0 := by
    refine HasDerivAt.fun_sum fun v _ => ?_
    exact (hd v).sub_const 1
  exact h

omit [DecidableEq ι] in
/-- **Equation (8), constant jet.** -/
theorem covarianceAnomaly_zero {u : ι → ℝ → ℂ} (hu : ∀ v, u v 0 = 1) (s : Finset ι) :
    covarianceAnomaly s u 0 = 0 := by
  rw [covarianceAnomaly, multiplierDefectSum_zero hu s,
    Finset.prod_congr rfl fun v _ => hu v, Finset.prod_const_one]
  ring

/-- **Equation (8), linear jet.**  The anomaly has vanishing derivative at the seam: the linear part
of the product is exactly the sum of the one-place linear parts. -/
theorem hasDerivAt_covarianceAnomaly {u : ι → ℝ → ℂ} {c : ι → ℂ}
    (hu : ∀ v, u v 0 = 1) (hd : ∀ v, HasDerivAt (u v) (c v) 0) (s : Finset ι) :
    HasDerivAt (covarianceAnomaly s u) 0 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hfun : (covarianceAnomaly (∅ : Finset ι) u) = fun _ : ℝ => (0 : ℂ) := by
      funext t
      rw [covarianceAnomaly, multiplierDefectSum]
      simp
    rw [hfun]
    exact hasDerivAt_const 0 0
  | insert x s hx ih =>
    have h1 : HasDerivAt (fun t => u x t * covarianceAnomaly s u t)
        (c x * covarianceAnomaly s u 0 + u x 0 * 0) 0 := (hd x).mul ih
    have h2 : HasDerivAt (fun t => (u x t - 1) * multiplierDefectSum s u t)
        (c x * multiplierDefectSum s u 0 + (u x 0 - 1) * ∑ v ∈ s, c v) 0 :=
      ((hd x).sub_const 1).mul (hasDerivAt_multiplierDefectSum hd s)
    rw [covarianceAnomaly_zero hu s, hu x] at h1
    rw [multiplierDefectSum_zero hu s, hu x] at h2
    have h3 := h1.fun_add h2
    have hval : c x * 0 + 1 * 0 + (c x * 0 + (1 - 1) * ∑ v ∈ s, c v) = (0 : ℂ) := by ring
    rw [hval] at h3
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with t
    exact covarianceAnomaly_insert hx u t

/-! ## The quadratic jet -/

/-- The increment slope of a multiplier at the seam. -/
theorem tendsto_multiplier_sub_one_div {u : ℝ → ℂ} {c : ℂ} (h0 : u 0 = 1)
    (hd : HasDerivAt u c 0) :
    Tendsto (fun t : ℝ => (u t - 1) / (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
  rw [hasDerivAt_iff_tendsto_slope] at hd
  refine hd.congr fun t => ?_
  simp only [slope, vsub_eq_sub, h0, sub_zero]
  rw [Complex.real_smul]
  push_cast
  ring

omit [DecidableEq ι] in
theorem tendsto_multiplierDefectSum_div {u : ι → ℝ → ℂ} {c : ι → ℂ}
    (hu : ∀ v, u v 0 = 1) (hd : ∀ v, HasDerivAt (u v) (c v) 0) (s : Finset ι) :
    Tendsto (fun t : ℝ => multiplierDefectSum s u t / (t : ℂ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ v ∈ s, c v)) := by
  have h : Tendsto (fun t : ℝ => ∑ v ∈ s, (u v t - 1) / (t : ℂ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ v ∈ s, c v)) :=
    tendsto_finsetSum s fun v _ => tendsto_multiplier_sub_one_div (hu v) (hd v)
  refine h.congr fun t => ?_
  rw [multiplierDefectSum, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => div_eq_mul_inv _ _

/-- **Equation (9).**  The quadratic jet of the anomaly at the seam is
`((sum c_v)^2 - sum c_v^2)/2`, i.e. `sum_(v<w) c_v c_w`.  Equivalently `C_s''(0) = 2 sum_(v<w) c_v c_w`.

Note that only first derivatives of the multipliers are used: the second-order data of each place
cancels between the product and the sum of increments, which is the exact content of the card's
"differentiating twice leaves only the two-element subsets". -/
theorem tendsto_covarianceAnomaly_div_sq {u : ι → ℝ → ℂ} {c : ι → ℂ}
    (hu : ∀ v, u v 0 = 1) (hd : ∀ v, HasDerivAt (u v) (c v) 0) (s : Finset ι) :
    Tendsto (fun t : ℝ => covarianceAnomaly s u t / (t : ℂ) ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (((∑ v ∈ s, c v) ^ 2 - ∑ v ∈ s, c v ^ 2) / 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hfun : ∀ t : ℝ, covarianceAnomaly (∅ : Finset ι) u t / (t : ℂ) ^ 2 = 0 := by
      intro t
      rw [covarianceAnomaly, multiplierDefectSum]
      simp
    have h0 : Tendsto (fun t : ℝ => covarianceAnomaly (∅ : Finset ι) u t / (t : ℂ) ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := Tendsto.congr (fun t => (hfun t).symm) tendsto_const_nhds
    simpa using h0
  | insert x s hx ih =>
    have hux : Tendsto (fun t : ℝ => u x t) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      have hc : ContinuousAt (u x) 0 := (hd x).continuousAt
      have := hc.tendsto
      rw [hu x] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hslope := tendsto_multiplier_sub_one_div (hu x) (hd x)
    have hsum := tendsto_multiplierDefectSum_div hu hd s
    have hlim := (hux.mul ih).add (hslope.mul hsum)
    have hval : 1 * (((∑ v ∈ s, c v) ^ 2 - ∑ v ∈ s, c v ^ 2) / 2) + c x * ∑ v ∈ s, c v
        = (((∑ v ∈ insert x s, c v) ^ 2 - ∑ v ∈ insert x s, c v ^ 2) / 2) := by
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      ring
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : ((t : ℂ)) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr (by simpa using ht))
    rw [covarianceAnomaly_insert hx u t]
    field_simp

/-! ## The off-diagonal charge -/

/-- The quadratic-jet magnitude, as an off-diagonal sum.  This is the form that admits a termwise
lower bound; the `(sum b)^2 - sum b^2` form does not, because the diagonal correction has the wrong
sign. -/
theorem offDiagCharge_eq_sum_offDiag (s : Finset ι) (b : ι → ℝ) :
    (∑ v ∈ s, b v) ^ 2 - ∑ v ∈ s, b v ^ 2 = ∑ x ∈ s.offDiag, b x.1 * b x.2 := by
  have h1 : (∑ v ∈ s, b v) ^ 2 = ∑ x ∈ s ×ˢ s, b x.1 * b x.2 := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  have h2 : (∑ x ∈ s ×ˢ s, b x.1 * b x.2)
      = (∑ x ∈ s.diag, b x.1 * b x.2) + ∑ x ∈ s.offDiag, b x.1 * b x.2 := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag s), Finset.diag_union_offDiag]
  have h3 : (∑ x ∈ s.diag, b x.1 * b x.2) = ∑ v ∈ s, b v ^ 2 := by
    rw [Finset.sum_diag]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [h1, h2, h3]
  ring

omit [DecidableEq ι] in
/-- A termwise comparison of two off-diagonal charges. -/
theorem sum_offDiag_le_sum_offDiag {s : Finset ι} {b b' : ι → ℝ}
    (h : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → b v * b w ≤ b' v * b' w) :
    (∑ x ∈ s.offDiag, b x.1 * b x.2) ≤ ∑ x ∈ s.offDiag, b' x.1 * b' x.2 := by
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Finset.mem_offDiag] at hx
  exact h x.1 hx.1 x.2 hx.2.1 hx.2.2

end GaloisForLFunctions.RHTower

end
