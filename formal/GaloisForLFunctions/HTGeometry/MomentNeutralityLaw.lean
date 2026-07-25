/-
The moment-neutrality law.

Let `m k` be the growth exponent of the `2k`-th moment of a function on a line
(`∫_0^T |f(1/2+it)|^{2k} dt ≪ T^{m k + ε}`), let `θ` be an established pointwise growth exponent
(`|f(1/2+it)| ≪ t^{θ+ε}`), and suppose the *perfect* moment bound `m j = 1` has been established
at some index `j`.  Three elementary facts constrain the family of pointwise bounds `m k / (2k)`
that the moment hierarchy can deliver:

* `m k = 1` for `0 ≤ k ≤ j`  (Hölder between `m 0 = 1` and `m j = 1`, together with `m ≥ 1`);
* `m k ≤ 1 + 2θ(k−j)` for `k ≥ j`  (Hölder of the `2k`-th moment against the pointwise bound);
* `μ ≤ m k / (2k)` for every `k > 0`  (a near-extremal value is sustained on an interval of length
  `≍ 1/log T`, so it contributes `≫ V^{2k}/log T` to the moment).

The resulting family of available bounds is `momentBound j θ k` below, and its greatest lower
bound is computed here exactly:

  `inf_{k > 0} momentBound j θ k = min (1/(2j)) θ`.

So a perfect `2j`-th moment produces a *new* pointwise exponent **iff** `1/(2j) < θ`, i.e. iff
`j > 1/(2θ)`; below that threshold it is exactly neutral — it cannot improve on `θ` by any amount,
at any index `k`, however the hierarchy is optimised.

For the Riemann zeta function with Bourgain's `θ = 13/84` the threshold is `j > 42/13 = 3.2308…`:
the sixth moment (`j = 3`) is neutral and the eighth moment (`j = 4`) gives `1/8`.  These two
numerical instances are recorded at the end of the file.

This module is source-independent: it is a statement about real numbers and contains no zeta
function.  The analytic inputs listed above are the hypotheses, not the content.
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field

open Filter Topology

namespace HTGeometry

/-- The best pointwise exponent obtainable at moment index `k` from a perfect `2j`-th moment
together with an established pointwise exponent `θ`.

For `k ≤ j` the perfect moment gives `m k = 1`, hence the bound `1/(2k)`.
For `k ≥ j` Hölder against the pointwise exponent gives `m k ≤ 1 + 2θ(k−j)`, hence the bound
`(1 + 2θ(k−j))/(2k)`. -/
noncomputable def momentBound (j θ k : ℝ) : ℝ :=
  if k ≤ j then 1 / (2 * k) else (1 + 2 * θ * (k - j)) / (2 * k)

/-- **Neutrality floor.**  No index `k` delivers a bound below `min (1/(2j)) θ`. -/
theorem min_le_momentBound {j θ k : ℝ} (hj : 0 < j) (hk : 0 < k) :
    min (1 / (2 * j)) θ ≤ momentBound j θ k := by
  set M := min (1 / (2 * j)) θ with hM
  have hMθ : M ≤ θ := min_le_right _ _
  have hMj : M ≤ 1 / (2 * j) := min_le_left _ _
  have h2j : (0:ℝ) < 2 * j := by linarith
  have h2k : (0:ℝ) < 2 * k := by linarith
  have hjM : 2 * j * M ≤ 1 := by
    have := (le_div_iff₀ h2j).mp hMj
    linarith [this]
  unfold momentBound
  by_cases h : k ≤ j
  · simp only [h, if_true]
    have hle : 1 / (2 * j) ≤ 1 / (2 * k) := by
      apply one_div_le_one_div_of_le h2k
      linarith
    exact le_trans hMj hle
  · simp only [h, if_false]
    rw [not_le] at h
    rw [le_div_iff₀ h2k]
    nlinarith [hMθ, hjM, h.le]

/-- The floor `1/(2j)` is attained at `k = j`. -/
theorem momentBound_self {j θ : ℝ} : momentBound j θ j = 1 / (2 * j) := by
  unfold momentBound; simp

/-- The floor `θ` is approached as `k → ∞`. -/
theorem momentBound_tendsto {j θ : ℝ} :
    Tendsto (fun k : ℝ => momentBound j θ k) atTop (𝓝 θ) := by
  have hev : ∀ᶠ k : ℝ in atTop, momentBound j θ k = θ + (1 - 2 * j * θ) / (2 * k) := by
    filter_upwards [eventually_gt_atTop j, eventually_gt_atTop (0:ℝ)] with k hk hk0
    unfold momentBound
    rw [if_neg (by linarith)]
    field_simp
    ring
  rw [tendsto_congr' hev]
  have hdiv : Tendsto (fun k : ℝ => (1 - 2 * j * θ) / (2 * k)) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds (x := (1 - 2 * j * θ)) (f := atTop (α := ℝ))).div_atTop
        (tendsto_atTop_add_const_left _ 0
          (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2)))
  simpa using tendsto_const_nhds.add hdiv

/-- **The moment-neutrality law.**  The greatest lower bound of the family of pointwise exponents
delivered by the moment hierarchy, given a perfect `2j`-th moment and an established pointwise
exponent `θ`, is exactly `min (1/(2j)) θ`. -/
theorem isGLB_momentBound {j θ : ℝ} (hj : 0 < j) :
    IsGLB (Set.image (momentBound j θ) (Set.Ioi (0:ℝ))) (min (1 / (2 * j)) θ) := by
  constructor
  · rintro x ⟨k, hk, rfl⟩
    exact min_le_momentBound hj hk
  · intro b hb
    have hbj : b ≤ 1 / (2 * j) := by
      have : b ≤ momentBound j θ j := hb ⟨j, hj, rfl⟩
      rwa [momentBound_self] at this
    have hbθ : b ≤ θ := by
      refine ge_of_tendsto (f := fun k : ℝ => momentBound j θ k) momentBound_tendsto ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with k hk
      exact hb ⟨k, hk, rfl⟩
    exact le_min hbj hbθ

/-- **Threshold form.**  A perfect `2j`-th moment strictly improves on the established exponent
`θ` exactly when `j` exceeds `1/(2θ)`. -/
theorem momentBound_improves_iff {j θ : ℝ} (hj : 0 < j) (hθ : 0 < θ) :
    min (1 / (2 * j)) θ < θ ↔ 1 / (2 * θ) < j := by
  have h2j : (0:ℝ) < 2 * j := by linarith
  have h2θ : (0:ℝ) < 2 * θ := by linarith
  constructor
  · intro h
    have hlt : 1 / (2 * j) < θ := by
      rcases min_cases (1 / (2 * j)) θ with ⟨he, _⟩ | ⟨he, _⟩
      · rwa [he] at h
      · rw [he] at h; exact absurd h (lt_irrefl θ)
    rw [div_lt_iff₀ h2j] at hlt
    rw [div_lt_iff₀ h2θ]
    linarith
  · intro h
    rw [div_lt_iff₀ h2θ] at h
    have hlt : 1 / (2 * j) < θ := by rw [div_lt_iff₀ h2j]; linarith
    exact lt_of_le_of_lt (min_le_left _ _) hlt

/-- **Convexity bridge.**  If the moment exponent `m` is convex, bounded below by `1`, and equals
`1` at both `0` and `j`, then it equals `1` on all of `[0, j]` — the first hypothesis feeding
`momentBound`. -/
theorem eq_one_of_convexOn_of_one_le {m : ℝ → ℝ} {j : ℝ} (hj : 0 < j)
    (hconv : ConvexOn ℝ (Set.Ici (0:ℝ)) m) (hge : ∀ x, 0 ≤ x → 1 ≤ m x)
    (h0 : m 0 = 1) (hjj : m j = 1) :
    ∀ x, 0 ≤ x → x ≤ j → m x = 1 := by
  intro x hx hxj
  refine le_antisymm ?_ (hge x hx)
  rcases eq_or_lt_of_le hxj with rfl | hlt
  · exact le_of_eq hjj
  · set t := x / j with ht
    have htnn : 0 ≤ t := div_nonneg hx hj.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hj]; exact hxj
    have hcomb : (1 - t) • (0:ℝ) + t • j = x := by
      simp only [smul_eq_mul, ht]
      field_simp
      ring
    have := hconv.2 (Set.self_mem_Ici) (Set.mem_Ici.mpr hj.le)
      (by linarith : (0:ℝ) ≤ 1 - t) htnn (by ring)
    rw [hcomb] at this
    simpa [h0, hjj] using this

section Zeta

/-- Bourgain's exponent for `ζ(1/2+it)`. -/
noncomputable def bourgainExponent : ℝ := 13 / 84

/-- The neutrality threshold against Bourgain's exponent is `42/13 = 3.2307…`. -/
theorem bourgain_threshold : 1 / (2 * bourgainExponent) = 42 / 13 := by
  unfold bourgainExponent; norm_num

/-- **The sixth moment is subconvexity-neutral.**  A perfect sixth moment (`j = 3`) against
Bourgain's exponent produces a floor of exactly `13/84`: no improvement at any index. -/
theorem sixth_moment_neutral :
    min (1 / (2 * (3:ℝ))) bourgainExponent = bourgainExponent := by
  unfold bourgainExponent; norm_num

/-- **The eighth moment is not neutral.**  A perfect eighth moment (`j = 4`) against Bourgain's
exponent produces a floor of `1/8 < 13/84`. -/
theorem eighth_moment_improves :
    min (1 / (2 * (4:ℝ))) bourgainExponent = 1 / 8 ∧ (1:ℝ) / 8 < bourgainExponent := by
  unfold bourgainExponent
  constructor <;> norm_num

/-- Sharp form of the two instances above through the threshold criterion: `3` is below the
threshold `42/13`, and `4` is above it. -/
theorem sixth_below_eighth_above :
    ¬ (1 / (2 * bourgainExponent) < (3:ℝ)) ∧ (1 / (2 * bourgainExponent) < (4:ℝ)) := by
  rw [bourgain_threshold]
  constructor <;> norm_num

end Zeta

end HTGeometry
