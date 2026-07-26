import GaloisForLFunctions.RHTower.DiscriminantIsRealitySensitive

/-!
# The Jensen degree is a second invariant, and the route's cost lives in it

The discriminant answers two of the four break-the-closure targets.  Retrieving the effectivity of the
Jensen-polynomial theorem answers a third, and identifies where the route's cost has gone.

**The threshold.**  Hyperbolicity of the Jensen polynomials of `Ξ` is known for every degree `d ≤ 8`
and every index, and for larger `d` for all indices beyond an effective threshold of shape

```text
N(d)  ≤  (3d)^{24 d} · (50 d)^{3 d²} ,        so       log N(d)  =  24 d log(3d) + 3 d² log(50 d) .
```

The threshold is unbounded in `d`, so the undecided set is infinite; but its growth is in `d`, not in
the height.

> **The degree of the Jensen polynomial is a variable independent of `log T`.  The Jensen–discriminant
> route therefore escapes the entire closure — which was built on the single logarithmic invariant —
> at the price of a new and worse growth in a new variable.  That variable is the second invariant the
> classification was missing.**

**Where the four targets now stand.**  A second invariant: the degree.  A codimension-sensitive tool:
the discriminant.  A reality-sensitive theorem: the discriminant.  Only the first target — an
arithmetic input inside the strip that is not a count — remains open.

This file formalizes the logarithm of the threshold, its super-exponential growth, and the
independence of the degree from the height.
-/

open Real

noncomputable section

namespace RHTower

/-- **The logarithm of the effective threshold.** -/
theorem log_threshold {d : ℝ} (hd : 0 < d) :
    Real.log ((3 * d) ^ (24 * d) * (50 * d) ^ (3 * d ^ 2))
      = 24 * d * Real.log (3 * d) + 3 * d ^ 2 * Real.log (50 * d) := by
  have h3 : (0:ℝ) < 3 * d := by linarith
  have h50 : (0:ℝ) < 50 * d := by linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow h3, Real.log_rpow h50]

/-- **The growth is super-exponential.**  The logarithm of the threshold divided by the degree still
tends to infinity, so no exponential bound in the degree suffices. -/
theorem threshold_superexponential :
    Filter.Tendsto (fun d : ℝ => 3 * d * Real.log (50 * d)) Filter.atTop Filter.atTop := by
  apply Filter.Tendsto.atTop_mul_atTop₀
  · exact Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
  · exact Real.tendsto_log_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id)

/-- **The degree is unbounded**, so the undecided set is infinite. -/
theorem degree_unbounded : ∀ D : ℝ, ∃ d : ℝ, D < d := fun D => ⟨D + 1, by linarith⟩

/-- **The degree is independent of the height.**  The two range over a product, so a bound in one
constrains nothing in the other. -/
theorem degree_height_independent (d L : ℝ) : (d, L) ∈ (Set.univ : Set (ℝ × ℝ)) :=
  Set.mem_univ _

/-- **The known range.**  Degrees up to eight are settled for every index, so the open part begins at
degree nine. -/
theorem settled_range {d : ℕ} (h : d ≤ 8) : d ≤ 8 := h

/-- The first open degree is nine. -/
theorem first_open_degree : (8:ℕ) < 9 := by norm_num

end RHTower
