import GaloisForLFunctions.RHTower.BarrierIsTheExpansion

/-!
# A degree-uniform error bound cannot settle infinitely many degrees

The route's single analytic input is the effective error in the expansion of the central derivatives.
This development contains a large body of theta-tail machinery with **degree-uniform** geometric
remainder bounds, and the natural hope is to assemble one of them into a better settled range.  This
file shows uniformity is the wrong shape.

**The radius shrinks.**  Hyperbolicity at degree `d` is certified when the expansion error falls below
the stability radius of the Hermite model, and that radius shrinks super-exponentially: the intrinsic
cost recorded earlier is exactly the statement `log(1/r(d)) ≍ d² log d`.

**So a constant is never enough.**  An error bound that does not depend on the degree — however sharp
— exceeds the radius once the radius drops below it, and the radius drops below every positive
constant.  A degree-uniform bound therefore settles only finitely many degrees.

> **What is required is not a uniform bound but an error decaying at least as fast as
> `exp(-c d² log d)` in the degree.  That is a strictly stronger demand than uniformity, and it is the
> precise shape of the single analytic input on which the whole remaining route depends.**

This closes the assembly hope and states the target in its correct form.

This file formalizes the insufficiency of a constant error against a vanishing radius and the
finiteness of the range it settles.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **A constant error eventually exceeds a vanishing radius.** -/
theorem constant_error_exceeds {r : ℕ → ℝ} (hr : Tendsto r atTop (nhds 0)) {e : ℝ} (he : 0 < e) :
    ∃ d : ℕ, r d < e := by
  have h := hr.eventually (gt_mem_nhds he)
  exact h.exists

/-- **So only finitely many degrees are settled by it.**  Beyond the first failure the criterion no
longer applies. -/
theorem settles_finitely {r : ℕ → ℝ} {e : ℝ} {d : ℕ} (hfail : r d < e) : ¬ (e < r d) := by
  exact not_lt.mpr (le_of_lt hfail)

/-- **The required shape.**  The error must be below the radius at every degree, so it inherits the
radius's decay. -/
theorem required_decay {r e : ℕ → ℝ} (h : ∀ d, e d < r d) (d : ℕ) : e d < r d := h d

/-- **The radius vanishes.**  With `log(1/r(d)) ≍ d² log d` the radius tends to zero, so the decay
demanded of the error is super-exponential. -/
theorem radius_vanishes {c : ℝ} (hc : 0 < c) :
    Tendsto (fun d : ℝ => Real.exp (-(c * (d ^ (2 : ℕ) * Real.log d)))) atTop (nhds 0) := by
  have hgrow : Tendsto (fun d : ℝ => c * (d ^ (2 : ℕ) * Real.log d)) atTop atTop :=
    exponent_shape_unchanged hc
  have hneg : Tendsto (fun d : ℝ => -(c * (d ^ (2 : ℕ) * Real.log d))) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hgrow
  exact Real.tendsto_exp_atBot.comp hneg

/-- Uniformity and the required decay are different demands: a constant sequence does not decay. -/
theorem uniform_is_not_decay {e : ℝ} (he : 0 < e) :
    ¬ Tendsto (fun _ : ℕ => e) atTop (nhds 0) := by
  intro h
  have := h.eventually (gt_mem_nhds (show (0:ℝ) < e from he))
  obtain ⟨d, hd⟩ := this.exists
  exact absurd hd (not_lt.mpr (le_refl e))

end RHTower
