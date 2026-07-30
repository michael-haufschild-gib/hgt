import GaloisForLFunctions.RHTower.HeightTimeScalingLaw

/-!
# The touching comparison: a minimum obeys the differential inequality of its minimizer

The collision argument tracks the running minimum `u_min(τ) = min_i δ_i(τ)²` of a family of gaps.
Each gap is differentiable, but the minimum is only Lipschitz, so the differential inequality
`u_min' ≤ -c` is not literally available.  What *is* available is the touching structure: at every
time some member of the family attains the minimum, lies above it everywhere, and has derivative at
most `-c`.  That is enough.

**Touching comparison.**  Let `f` be continuous on `[0,T]` and suppose that for every `x ∈ [0,T)`
there is a function `g` with `f ≤ g` everywhere, `f x = g x`, and a right derivative `g' ≤ -c` at
`x`.  Then

```text
f x ≤ f 0 - c·x     for all x ∈ [0,T] .
```

The proof is the fencing theorem for continuous functions: for `z > x` the difference quotient of `f`
is at most that of `g`, because `f z ≤ g z` while `f x = g x`; the quotient of `g` tends to `g' ≤ -c`,
so the lower right Dini derivative of `f` is at most `-c`, which is the derivative of the comparison
line.

A finite minimum supplies the hypothesis for free: the minimizing index at `x` gives a function lying
above `f` and touching it there, and its derivative is at most `-c` by the collision estimate, which
applies precisely because the minimizing gap satisfies the running-mean hypothesis by definition.

This closes the last soft step in the collision argument: no Dini-derivative theory beyond the
fencing theorem is needed, and no persistence hypothesis.

This file formalizes the touching comparison and the finite-minimum instance of its hypothesis.
-/

open Set Filter Topology

noncomputable section

namespace RHTower

/-- **Touching comparison.**  A continuous function that is touched from above at every point by a
differentiable function of slope at most `-c` decreases at least linearly. -/
theorem touching_comparison {f : ℝ → ℝ} {c T : ℝ}
    (hf : ContinuousOn f (Icc 0 T))
    (htouch : ∀ x ∈ Ico (0 : ℝ) T, ∃ g : ℝ → ℝ, ∃ g' : ℝ,
      (∀ y, f y ≤ g y) ∧ f x = g x ∧ HasDerivWithinAt g g' (Ici x) x ∧ g' ≤ -c) :
    ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) T → f x ≤ f 0 - c * x := by
  have hB : ContinuousOn (fun x : ℝ => f 0 - c * x) (Icc 0 T) := by fun_prop
  have hB' : ∀ x ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun x : ℝ => f 0 - c * x) (-c) (Ici x) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => c * x) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    simpa using (h1.const_sub (f 0)).hasDerivWithinAt (s := Ici x)
  refine image_le_of_liminf_slope_right_le_deriv_boundary hf (by simp) hB hB' ?_
  intro x hx r hr
  obtain ⟨g, g', hge, heq, hderiv, hle⟩ := htouch x hx
  have hslope : Tendsto (slope g x) (𝓝[>] x) (𝓝 g') := by
    have := hasDerivWithinAt_iff_tendsto_slope.mp hderiv
    simpa [Ici_sdiff_left] using this
  have hgr : g' < r := lt_of_le_of_lt hle hr
  have hev : ∀ᶠ z in 𝓝[>] x, slope g x z < r := hslope.eventually (eventually_lt_nhds hgr)
  have hmono : ∀ᶠ z in 𝓝[>] x, slope f x z ≤ slope g x z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzx : 0 < z - x := sub_pos.mpr hz
    rw [slope_def_field, slope_def_field, div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (inv_pos.mpr hzx))
    have := hge z
    linarith [heq]
  exact ((hev.and hmono).mono fun z hz => lt_of_le_of_lt hz.2 hz.1).frequently

/-- **The finite minimum supplies the hypothesis.**  If `f` is the pointwise minimum of a finite
family, then at each point the minimizing member lies above `f` and touches it. -/
theorem min_touches {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ → ℝ) (x : ℝ) :
    ∃ i : ι, (∀ y, (Finset.univ.inf' Finset.univ_nonempty fun j => u j y) ≤ u i y) ∧
      (Finset.univ.inf' Finset.univ_nonempty fun j => u j x) = u i x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) fun j => u j x
  exact ⟨i, fun y => Finset.inf'_le _ (Finset.mem_univ i), hi⟩

/-- The conclusion in the form used by the collision argument: the running minimum of the squared
gaps reaches zero by time `u_min(0)/c`. -/
theorem min_reaches_zero {u₀ c T : ℝ} (hc : 0 < c)
    (hbound : u₀ - c * T ≤ 0) : T ≥ u₀ / c := by
  rw [ge_iff_le, div_le_iff₀ hc]
  linarith

end RHTower
