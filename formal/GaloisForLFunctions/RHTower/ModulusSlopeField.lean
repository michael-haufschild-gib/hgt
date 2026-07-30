/-
# The modulus-slope field as a subharmonicity-constrained object

`log ‖ξ‖` is subharmonic, and the subharmonicity is quantitative: the circle average
`A(r) = ⨍_{|z-ρ|=r} log ‖ξ(z)‖` is a convex, nondecreasing function of `log r` whose two-radius
slope weights every enclosed zero by its multiplicity.  This module develops the two-circle slope
`modulusSlope ρ r₁ r₂` at ALL radius scales — not only in the germ limit, where it reads the local
vanishing order (`modulusSlope_eq_order`) — as one constrained field on the plane.

The engine is the two-radius difference of Jensen's formula
(`MeromorphicOn.circleAverage_log_norm`): the trailing-coefficient constant cancels, leaving the
exact weighted divisor sum

  `A(r₂) − A(r₁) = ∑_{ξ(u)=0, ‖u−ρ‖ ≤ r₂} ord_u(ξ) · w(u)`,
  `w(u) = log r₂ − log (max r₁ ‖u−ρ‖) ∈ [0, log r₂ − log r₁]`

(`xi_circleAverage_sub_eq_divisor_sum`).  Three constraint laws follow:

* `modulusSlope_nonneg` — the field is nonnegative at every center and radius pair;
* `ballOrderSum_le_modulusSlope`, `modulusSlope_le_ballOrderSum` — the slope brackets the
  enclosed divisor mass: `n(r₁) ≤ slope(r₁,r₂) ≤ n(r₂)`;
* `modulusSlope_radii_mono` — slopes are nondecreasing in the radius pair: convexity of the
  circle average in `log r`, in discrete two-radius form.

The dichotomy `modulusSlope_eq_zero_iff_ball_zeroFree` turns a single vanishing sample into
zero-freeness of the whole enclosed open ball, and
`modulusSlope_eq_ballOrderSum_of_annulus_zeroFree` reads the exact enclosed integer at every
zero-free annulus.  The two RH surfaces of the same constraint:

* `not_riemannHypothesis_of_modulusSlope_ne_zero` — the disproof surface: ONE nonzero slope
  sample over a right-half-contained ball refutes RH.  Two circle averages of `log ‖ξ‖` at any
  scale; no shrinking radii, no zero located, no phase information.
* `rh_iff_forall_rightHalf_modulusSlope_eq_zero` — the proof surface: RH is the flatness of the
  field over every right-half-contained radius pair.  The small-radius tomography criterion
  upgrades to a uniform all-scale statement with no germ quantifier, because vanishing
  propagates downward through the convexity law
  (`modulusSlope_eq_zero_of_outer_eq_zero`).
-/
import GaloisForLFunctions.RHTower.ChargeTomography

open Complex Metric

namespace RHTower

noncomputable section

/-- The total ξ-divisor mass of the closed ball of radius `r` around `ρ`: the number of enclosed
ξ-zeros counted with multiplicity. -/
def xiBallOrderSum (ρ : ℂ) (r : ℝ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor xi (closedBall ρ r) u

/-- On its domain, the ball divisor of ξ is the (finite) local vanishing order. -/
theorem xi_divisor_closedBall_eq_order_toNat {ρ : ℂ} {r : ℝ} {u : ℂ}
    (hu : u ∈ closedBall ρ r) :
    MeromorphicOn.divisor xi (closedBall ρ r) u = ((analyticOrderAt xi u).toNat : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (xi_analyticOnNhd _) hu,
    ← ENat.coe_toNat (xi_orderAt_ne_top u)]
  simp

/-- Outside its domain, the ball divisor of ξ vanishes. -/
theorem xi_divisor_closedBall_eq_zero_of_notMem {ρ : ℂ} {r : ℝ} {u : ℂ}
    (hu : u ∉ closedBall ρ r) :
    MeromorphicOn.divisor xi (closedBall ρ r) u = 0 := by
  by_contra h
  exact hu ((MeromorphicOn.divisor xi (closedBall ρ r)).supportWithinDomain
    (Function.mem_support.mpr h))

/-- The enclosed divisor mass is nonnegative. -/
theorem xiBallOrderSum_nonneg (ρ : ℂ) (r : ℝ) : 0 ≤ xiBallOrderSum ρ r := by
  rw [xiBallOrderSum, finsum_eq_sum_of_support_subset _
    (by rw [Set.Finite.coe_toFinset] :
      Function.support ⇑(MeromorphicOn.divisor xi (closedBall ρ r)) ⊆
        ↑((MeromorphicOn.divisor xi (closedBall ρ r)).finiteSupport
          (isCompact_closedBall ρ r)).toFinset)]
  refine Finset.sum_nonneg fun u hu => ?_
  have hudom : u ∈ closedBall ρ r :=
    (MeromorphicOn.divisor xi (closedBall ρ r)).supportWithinDomain
      (by rwa [Set.Finite.mem_toFinset] at hu)
  rw [xi_divisor_closedBall_eq_order_toNat hudom]
  positivity

/-- **The two-radius Jensen difference.**  For `0 < r₁ < r₂` the difference of circle averages of
`log ‖ξ‖` around `ρ` is the divisor sum over the outer closed ball, each zero weighted by
`log r₂ − log r₁` if it lies in the inner closed ball and by `log r₂ − log ‖u − ρ‖` if it lies in
the open annulus.  The trailing coefficient of Jensen's formula is radius-free and cancels. -/
theorem xi_circleAverage_sub_eq_divisor_sum (ρ : ℂ) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
        Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁ =
      ∑ u ∈ ((MeromorphicOn.divisor xi (closedBall ρ r₂)).finiteSupport
          (isCompact_closedBall ρ r₂)).toFinset,
        ((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) *
          (if ‖u - ρ‖ ≤ r₁ then Real.log r₂ - Real.log r₁
            else Real.log r₂ - Real.log ‖u - ρ‖) := by
  have hr₂ : 0 < r₂ := hr₁.trans h₁₂
  have habs₁ : |r₁| = r₁ := abs_of_pos hr₁
  have habs₂ : |r₂| = r₂ := abs_of_pos hr₂
  have hmer₂ : MeromorphicOn xi (closedBall ρ |r₂|) := (xi_analyticOnNhd _).meromorphicOn
  have hmer₁ : MeromorphicOn xi (closedBall ρ |r₁|) := (xi_analyticOnNhd _).meromorphicOn
  set T := ((MeromorphicOn.divisor xi (closedBall ρ r₂)).finiteSupport
    (isCompact_closedBall ρ r₂)).toFinset with hTdef
  -- membership bookkeeping for the outer support finset
  have hTdom : ∀ u ∈ T, u ∈ closedBall ρ r₂ := fun u hu =>
    (MeromorphicOn.divisor xi (closedBall ρ r₂)).supportWithinDomain
      (by rwa [hTdef, Set.Finite.mem_toFinset] at hu)
  have hD₁D₂ : ∀ u : ℂ, MeromorphicOn.divisor xi (closedBall ρ r₁) u ≠ 0 →
      MeromorphicOn.divisor xi (closedBall ρ r₂) u ≠ 0 := by
    intro u h1
    have humem : u ∈ closedBall ρ r₁ :=
      (MeromorphicOn.divisor xi (closedBall ρ r₁)).supportWithinDomain
        (Function.mem_support.mpr h1)
    have humem₂ : u ∈ closedBall ρ r₂ := closedBall_subset_closedBall h₁₂.le humem
    rw [xi_divisor_closedBall_eq_order_toNat humem₂]
    rwa [xi_divisor_closedBall_eq_order_toNat humem] at h1
  have hsupp₂ : Function.support (fun u =>
      ((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) *
        Real.log (r₂ * ‖ρ - u‖⁻¹)) ⊆ ↑T := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [hTdef, Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    exact hu (by rw [h0]; simp)
  have hsupp₁ : Function.support (fun u =>
      ((MeromorphicOn.divisor xi (closedBall ρ r₁)) u : ℝ) *
        Real.log (r₁ * ‖ρ - u‖⁻¹)) ⊆ ↑T := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [hTdef, Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    refine hu ?_
    have h1 : MeromorphicOn.divisor xi (closedBall ρ r₁) u = 0 := by
      by_contra hne
      exact (hD₁D₂ u hne) h0
    rw [h1]
    simp
  -- Jensen at both radii; the trailing coefficient cancels in the difference
  have hJ : Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
      Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁ =
      (∑ u ∈ T, (((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) *
          Real.log (r₂ * ‖ρ - u‖⁻¹) -
        ((MeromorphicOn.divisor xi (closedBall ρ r₁)) u : ℝ) *
          Real.log (r₁ * ‖ρ - u‖⁻¹))) +
      (((MeromorphicOn.divisor xi (closedBall ρ r₂)) ρ : ℝ) * Real.log r₂ -
        ((MeromorphicOn.divisor xi (closedBall ρ r₁)) ρ : ℝ) * Real.log r₁) := by
    rw [MeromorphicOn.circleAverage_log_norm hr₂.ne' hmer₂,
      MeromorphicOn.circleAverage_log_norm hr₁.ne' hmer₁, habs₂, habs₁,
      finsum_eq_sum_of_support_subset _ hsupp₂,
      finsum_eq_sum_of_support_subset _ hsupp₁,
      Finset.sum_sub_distrib]
    ring
  rw [hJ]
  -- the center divisor value agrees over both balls
  have hcen₂ : ρ ∈ closedBall ρ r₂ := mem_closedBall_self hr₂.le
  have hcen₁ : ρ ∈ closedBall ρ r₁ := mem_closedBall_self hr₁.le
  have hcenter : ((MeromorphicOn.divisor xi (closedBall ρ r₁)) ρ : ℝ) =
      ((MeromorphicOn.divisor xi (closedBall ρ r₂)) ρ : ℝ) := by
    rw [xi_divisor_closedBall_eq_order_toNat hcen₁, xi_divisor_closedBall_eq_order_toNat hcen₂]
  -- termwise identification away from the center
  have hterm : ∀ u ∈ T, u ≠ ρ →
      ((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) * Real.log (r₂ * ‖ρ - u‖⁻¹) -
        ((MeromorphicOn.divisor xi (closedBall ρ r₁)) u : ℝ) * Real.log (r₁ * ‖ρ - u‖⁻¹) =
      ((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) *
        (if ‖u - ρ‖ ≤ r₁ then Real.log r₂ - Real.log r₁
          else Real.log r₂ - Real.log ‖u - ρ‖) := by
    intro u huT hune
    have hnorm : 0 < ‖u - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hune)
    have hlog₂ : Real.log (r₂ * ‖ρ - u‖⁻¹) = Real.log r₂ - Real.log ‖u - ρ‖ := by
      rw [norm_sub_rev ρ u, Real.log_mul hr₂.ne' (inv_ne_zero hnorm.ne'), Real.log_inv]
      ring
    have hlog₁ : Real.log (r₁ * ‖ρ - u‖⁻¹) = Real.log r₁ - Real.log ‖u - ρ‖ := by
      rw [norm_sub_rev ρ u, Real.log_mul hr₁.ne' (inv_ne_zero hnorm.ne'), Real.log_inv]
      ring
    by_cases hle : ‖u - ρ‖ ≤ r₁
    · have humem₁ : u ∈ closedBall ρ r₁ := by
        rw [mem_closedBall, dist_eq_norm]; exact hle
      have humem₂ : u ∈ closedBall ρ r₂ := closedBall_subset_closedBall h₁₂.le humem₁
      rw [if_pos hle, hlog₂, hlog₁, xi_divisor_closedBall_eq_order_toNat humem₁,
        xi_divisor_closedBall_eq_order_toNat humem₂]
      ring
    · have hnot : u ∉ closedBall ρ r₁ := by
        rw [mem_closedBall, dist_eq_norm]; exact hle
      rw [if_neg hle, hlog₂, xi_divisor_closedBall_eq_zero_of_notMem hnot]
      push_cast
      ring
  by_cases hρT : ρ ∈ T
  · rw [Finset.sum_eq_sum_sdiff_singleton_add hρT, Finset.sum_eq_sum_sdiff_singleton_add hρT
      (fun u => ((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) *
        (if ‖u - ρ‖ ≤ r₁ then Real.log r₂ - Real.log r₁
          else Real.log r₂ - Real.log ‖u - ρ‖))]
    have hdiffρ : ((MeromorphicOn.divisor xi (closedBall ρ r₂)) ρ : ℝ) *
        Real.log (r₂ * ‖ρ - ρ‖⁻¹) -
        ((MeromorphicOn.divisor xi (closedBall ρ r₁)) ρ : ℝ) *
        Real.log (r₁ * ‖ρ - ρ‖⁻¹) = 0 := by
      simp
    have hwρ : ((MeromorphicOn.divisor xi (closedBall ρ r₂)) ρ : ℝ) *
        (if ‖ρ - ρ‖ ≤ r₁ then Real.log r₂ - Real.log r₁
          else Real.log r₂ - Real.log ‖ρ - ρ‖) =
        ((MeromorphicOn.divisor xi (closedBall ρ r₂)) ρ : ℝ) *
          (Real.log r₂ - Real.log r₁) := by
      rw [if_pos (by simpa using hr₁.le)]
    have hsum_eq : ∑ u ∈ T \ {ρ},
        (((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) *
            Real.log (r₂ * ‖ρ - u‖⁻¹) -
          ((MeromorphicOn.divisor xi (closedBall ρ r₁)) u : ℝ) *
            Real.log (r₁ * ‖ρ - u‖⁻¹)) =
        ∑ u ∈ T \ {ρ},
          ((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) *
            (if ‖u - ρ‖ ≤ r₁ then Real.log r₂ - Real.log r₁
              else Real.log r₂ - Real.log ‖u - ρ‖) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      have huT : u ∈ T := (Finset.mem_sdiff.mp hu).1
      have hune : u ≠ ρ := by
        have := (Finset.mem_sdiff.mp hu).2
        simpa using this
      exact hterm u huT hune
    rw [hsum_eq, hdiffρ, hwρ, hcenter]
    ring
  · have hD₂ρ : ((MeromorphicOn.divisor xi (closedBall ρ r₂)) ρ : ℝ) = 0 := by
      have : MeromorphicOn.divisor xi (closedBall ρ r₂) ρ = 0 := by
        by_contra h
        exact hρT (by rw [hTdef, Set.Finite.mem_toFinset]; exact Function.mem_support.mpr h)
      rw [this]
      simp
    have hD₁ρ : ((MeromorphicOn.divisor xi (closedBall ρ r₁)) ρ : ℝ) = 0 := by
      rw [hcenter]
      exact hD₂ρ
    rw [Finset.sum_congr rfl (fun u hu => hterm u hu (fun h => hρT (h ▸ hu))), hD₂ρ, hD₁ρ]
    ring

/-- The enclosed divisor mass as a sum over the support finset, in `ℝ`. -/
theorem xiBallOrderSum_cast_eq_finsetSum (ρ : ℂ) (r : ℝ) :
    ((xiBallOrderSum ρ r : ℤ) : ℝ) =
      ∑ u ∈ ((MeromorphicOn.divisor xi (closedBall ρ r)).finiteSupport
          (isCompact_closedBall ρ r)).toFinset,
        ((MeromorphicOn.divisor xi (closedBall ρ r)) u : ℝ) := by
  rw [xiBallOrderSum, finsum_eq_sum_of_support_subset _
    (by rw [Set.Finite.coe_toFinset] :
      Function.support ⇑(MeromorphicOn.divisor xi (closedBall ρ r)) ⊆
        ↑((MeromorphicOn.divisor xi (closedBall ρ r)).finiteSupport
          (isCompact_closedBall ρ r)).toFinset)]
  push_cast
  rfl

/-- **Nonnegativity of the slope field.**  Subharmonicity of `log ‖ξ‖` in two-radius form: the
circle average is nondecreasing in the radius, at every center and every radius pair. -/
theorem modulusSlope_nonneg (ρ : ℂ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    0 ≤ modulusSlope ρ r₁ r₂ := by
  have hΔ : 0 < Real.log r₂ - Real.log r₁ := sub_pos.mpr (Real.log_lt_log hr₁ h₁₂)
  rw [modulusSlope, xi_circleAverage_sub_eq_divisor_sum ρ hr₁ h₁₂]
  refine div_nonneg (Finset.sum_nonneg fun u hu => ?_) hΔ.le
  have hudom : u ∈ closedBall ρ r₂ :=
    (MeromorphicOn.divisor xi (closedBall ρ r₂)).supportWithinDomain
      (by rwa [Set.Finite.mem_toFinset] at hu)
  have hur₂ : ‖u - ρ‖ ≤ r₂ := by rwa [mem_closedBall, dist_eq_norm] at hudom
  refine mul_nonneg ?_ ?_
  · rw [xi_divisor_closedBall_eq_order_toNat hudom]
    positivity
  · split_ifs with h
    · exact hΔ.le
    · exact sub_nonneg.mpr (Real.log_le_log (hr₁.trans (not_le.mp h)) hur₂)

/-- **Upper divisor bracket.**  The slope is at most the divisor mass of the outer ball. -/
theorem modulusSlope_le_ballOrderSum (ρ : ℂ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    modulusSlope ρ r₁ r₂ ≤ ((xiBallOrderSum ρ r₂ : ℤ) : ℝ) := by
  have hΔ : 0 < Real.log r₂ - Real.log r₁ := sub_pos.mpr (Real.log_lt_log hr₁ h₁₂)
  rw [modulusSlope, xi_circleAverage_sub_eq_divisor_sum ρ hr₁ h₁₂, div_le_iff₀ hΔ,
    xiBallOrderSum_cast_eq_finsetSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun u hu => ?_
  have hudom : u ∈ closedBall ρ r₂ :=
    (MeromorphicOn.divisor xi (closedBall ρ r₂)).supportWithinDomain
      (by rwa [Set.Finite.mem_toFinset] at hu)
  have hDnn : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) := by
    rw [xi_divisor_closedBall_eq_order_toNat hudom]
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hDnn
  split_ifs with h
  · exact le_refl _
  · exact sub_le_sub_left (Real.log_le_log hr₁ (not_le.mp h).le) _

/-- **Lower divisor bracket.**  The slope is at least the divisor mass of the inner ball. -/
theorem ballOrderSum_le_modulusSlope (ρ : ℂ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    ((xiBallOrderSum ρ r₁ : ℤ) : ℝ) ≤ modulusSlope ρ r₁ r₂ := by
  have hΔ : 0 < Real.log r₂ - Real.log r₁ := sub_pos.mpr (Real.log_lt_log hr₁ h₁₂)
  rw [modulusSlope, xi_circleAverage_sub_eq_divisor_sum ρ hr₁ h₁₂, le_div_iff₀ hΔ]
  have hD₁D₂ : ∀ u : ℂ, MeromorphicOn.divisor xi (closedBall ρ r₁) u ≠ 0 →
      MeromorphicOn.divisor xi (closedBall ρ r₂) u ≠ 0 := by
    intro u h1
    have humem : u ∈ closedBall ρ r₁ :=
      (MeromorphicOn.divisor xi (closedBall ρ r₁)).supportWithinDomain
        (Function.mem_support.mpr h1)
    have humem₂ : u ∈ closedBall ρ r₂ := closedBall_subset_closedBall h₁₂.le humem
    rw [xi_divisor_closedBall_eq_order_toNat humem₂]
    rwa [xi_divisor_closedBall_eq_order_toNat humem] at h1
  have hsupp₁ : Function.support ⇑(MeromorphicOn.divisor xi (closedBall ρ r₁)) ⊆
      ↑((MeromorphicOn.divisor xi (closedBall ρ r₂)).finiteSupport
        (isCompact_closedBall ρ r₂)).toFinset := by
    intro u hu
    rw [Set.Finite.coe_toFinset]
    exact Function.mem_support.mpr (hD₁D₂ u (Function.mem_support.mp hu))
  have hn₁ : ((xiBallOrderSum ρ r₁ : ℤ) : ℝ) =
      ∑ u ∈ ((MeromorphicOn.divisor xi (closedBall ρ r₂)).finiteSupport
          (isCompact_closedBall ρ r₂)).toFinset,
        ((MeromorphicOn.divisor xi (closedBall ρ r₁)) u : ℝ) := by
    rw [xiBallOrderSum, finsum_eq_sum_of_support_subset _ hsupp₁]
    push_cast
    rfl
  rw [hn₁, Finset.sum_mul]
  refine Finset.sum_le_sum fun u hu => ?_
  have hudom : u ∈ closedBall ρ r₂ :=
    (MeromorphicOn.divisor xi (closedBall ρ r₂)).supportWithinDomain
      (by rwa [Set.Finite.mem_toFinset] at hu)
  by_cases hle : ‖u - ρ‖ ≤ r₁
  · have humem₁ : u ∈ closedBall ρ r₁ := by
      rw [mem_closedBall, dist_eq_norm]; exact hle
    rw [if_pos hle, xi_divisor_closedBall_eq_order_toNat humem₁,
      xi_divisor_closedBall_eq_order_toNat hudom]
  · have hnot : u ∉ closedBall ρ r₁ := by
      rw [mem_closedBall, dist_eq_norm]; exact hle
    rw [xi_divisor_closedBall_eq_zero_of_notMem hnot]
    push_cast
    rw [zero_mul, if_neg hle]
    have hur₂ : ‖u - ρ‖ ≤ r₂ := by rwa [mem_closedBall, dist_eq_norm] at hudom
    refine mul_nonneg ?_ ?_
    · rw [xi_divisor_closedBall_eq_order_toNat hudom]
      positivity
    · exact sub_nonneg.mpr (Real.log_le_log (hr₁.trans (not_le.mp hle)) hur₂)

/-- **Convexity of the circle average in `log r`, two-radius form.**  Slopes over nested radius
pairs are nondecreasing: the inner slope never exceeds the outer slope. -/
theorem modulusSlope_radii_mono (ρ : ℂ) {r₁ r₂ r₃ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (h₂₃ : r₂ < r₃) :
    modulusSlope ρ r₁ r₂ ≤ modulusSlope ρ r₂ r₃ :=
  (modulusSlope_le_ballOrderSum ρ hr₁ h₁₂).trans
    (ballOrderSum_le_modulusSlope ρ (hr₁.trans h₁₂) h₂₃)

/-- **Downward propagation of flatness.**  A vanishing outer slope forces every inner slope to
vanish: one flat sample at a large scale flattens the whole germ below it. -/
theorem modulusSlope_eq_zero_of_outer_eq_zero (ρ : ℂ) {r₁ r₂ r₃ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (h₂₃ : r₂ < r₃)
    (h : modulusSlope ρ r₂ r₃ = 0) : modulusSlope ρ r₁ r₂ = 0 :=
  le_antisymm (h ▸ modulusSlope_radii_mono ρ hr₁ h₁₂ h₂₃) (modulusSlope_nonneg ρ hr₁ h₁₂)

/-- **The flatness dichotomy.**  A slope sample vanishes exactly when the enclosed open ball is
ξ-zero-free: one vanishing two-circle sample certifies zero-freeness of the whole enclosed
ball, and conversely.  Zeros on the outer circle itself carry weight zero and are invisible. -/
theorem modulusSlope_eq_zero_iff_ball_zeroFree (ρ : ℂ) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    modulusSlope ρ r₁ r₂ = 0 ↔ ∀ z ∈ ball ρ r₂, xi z ≠ 0 := by
  have hΔ : 0 < Real.log r₂ - Real.log r₁ := sub_pos.mpr (Real.log_lt_log hr₁ h₁₂)
  rw [modulusSlope, xi_circleAverage_sub_eq_divisor_sum ρ hr₁ h₁₂, div_eq_zero_iff]
  constructor
  · rintro (hN | hΔ0)
    swap
    · exact absurd hΔ0 hΔ.ne'
    intro z hz hzero
    have hz₂ : z ∈ closedBall ρ r₂ := ball_subset_closedBall hz
    have hzn : ‖z - ρ‖ < r₂ := by rwa [mem_ball, dist_eq_norm] at hz
    have horder : (analyticOrderAt xi z).toNat ≠ 0 := fun h0 =>
      ((xi_orderToNat_eq_zero_iff z).mp h0) hzero
    have hzT : z ∈ ((MeromorphicOn.divisor xi (closedBall ρ r₂)).finiteSupport
        (isCompact_closedBall ρ r₂)).toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_support,
        xi_divisor_closedBall_eq_order_toNat hz₂]
      exact_mod_cast horder
    have hterms : ∀ u ∈ ((MeromorphicOn.divisor xi (closedBall ρ r₂)).finiteSupport
        (isCompact_closedBall ρ r₂)).toFinset,
        (0 : ℝ) ≤ ((MeromorphicOn.divisor xi (closedBall ρ r₂)) u : ℝ) *
          (if ‖u - ρ‖ ≤ r₁ then Real.log r₂ - Real.log r₁
            else Real.log r₂ - Real.log ‖u - ρ‖) := by
      intro u hu
      have hudom : u ∈ closedBall ρ r₂ :=
        (MeromorphicOn.divisor xi (closedBall ρ r₂)).supportWithinDomain
          (by rwa [Set.Finite.mem_toFinset] at hu)
      have hur₂ : ‖u - ρ‖ ≤ r₂ := by rwa [mem_closedBall, dist_eq_norm] at hudom
      refine mul_nonneg ?_ ?_
      · rw [xi_divisor_closedBall_eq_order_toNat hudom]
        positivity
      · split_ifs with h
        · exact hΔ.le
        · exact sub_nonneg.mpr (Real.log_le_log (hr₁.trans (not_le.mp h)) hur₂)
    have hzterm := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hN z hzT
    have hDpos : (0 : ℝ) < ((MeromorphicOn.divisor xi (closedBall ρ r₂)) z : ℝ) := by
      rw [xi_divisor_closedBall_eq_order_toNat hz₂]
      exact_mod_cast Nat.pos_of_ne_zero horder
    have hwpos : (0 : ℝ) < (if ‖z - ρ‖ ≤ r₁ then Real.log r₂ - Real.log r₁
        else Real.log r₂ - Real.log ‖z - ρ‖) := by
      split_ifs with h
      · exact hΔ
      · exact sub_pos.mpr (Real.log_lt_log (hr₁.trans (not_le.mp h)) hzn)
    exact absurd hzterm (mul_pos hDpos hwpos).ne'
  · intro hfree
    left
    refine Finset.sum_eq_zero fun u hu => ?_
    have hudom : u ∈ closedBall ρ r₂ :=
      (MeromorphicOn.divisor xi (closedBall ρ r₂)).supportWithinDomain
        (by rwa [Set.Finite.mem_toFinset] at hu)
    have hur₂ : ‖u - ρ‖ ≤ r₂ := by rwa [mem_closedBall, dist_eq_norm] at hudom
    have huzero : xi u = 0 := by
      by_contra hne
      have h0 : (analyticOrderAt xi u).toNat = 0 := (xi_orderToNat_eq_zero_iff u).mpr hne
      have : MeromorphicOn.divisor xi (closedBall ρ r₂) u = 0 := by
        rw [xi_divisor_closedBall_eq_order_toNat hudom, h0]
        rfl
      rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
      exact hu this
    have heq : ‖u - ρ‖ = r₂ := by
      refine le_antisymm hur₂ (not_lt.mp fun hlt => ?_)
      exact hfree u (by rw [mem_ball, dist_eq_norm]; exact hlt) huzero
    rw [if_neg (by rw [heq]; exact not_le.mpr h₁₂), heq, sub_self, mul_zero]

/-- **Exact integer readoff at a zero-free annulus.**  If ξ has no zero in the closed annulus
`r₁ < ‖z − ρ‖ ≤ r₂`, the slope equals the enclosed divisor mass of the inner ball on the nose:
the field is integer-valued away from zero radii. -/
theorem modulusSlope_eq_ballOrderSum_of_annulus_zeroFree (ρ : ℂ) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hfree : ∀ z : ℂ, r₁ < ‖z - ρ‖ → ‖z - ρ‖ ≤ r₂ → xi z ≠ 0) :
    modulusSlope ρ r₁ r₂ = ((xiBallOrderSum ρ r₁ : ℤ) : ℝ) := by
  have hΔ : 0 < Real.log r₂ - Real.log r₁ := sub_pos.mpr (Real.log_lt_log hr₁ h₁₂)
  have hD₁D₂ : ∀ u : ℂ, MeromorphicOn.divisor xi (closedBall ρ r₁) u ≠ 0 →
      MeromorphicOn.divisor xi (closedBall ρ r₂) u ≠ 0 := by
    intro u h1
    have humem : u ∈ closedBall ρ r₁ :=
      (MeromorphicOn.divisor xi (closedBall ρ r₁)).supportWithinDomain
        (Function.mem_support.mpr h1)
    have humem₂ : u ∈ closedBall ρ r₂ := closedBall_subset_closedBall h₁₂.le humem
    rw [xi_divisor_closedBall_eq_order_toNat humem₂]
    rwa [xi_divisor_closedBall_eq_order_toNat humem] at h1
  have hsupp₁ : Function.support ⇑(MeromorphicOn.divisor xi (closedBall ρ r₁)) ⊆
      ↑((MeromorphicOn.divisor xi (closedBall ρ r₂)).finiteSupport
        (isCompact_closedBall ρ r₂)).toFinset := by
    intro u hu
    rw [Set.Finite.coe_toFinset]
    exact Function.mem_support.mpr (hD₁D₂ u (Function.mem_support.mp hu))
  have hn₁ : ((xiBallOrderSum ρ r₁ : ℤ) : ℝ) =
      ∑ u ∈ ((MeromorphicOn.divisor xi (closedBall ρ r₂)).finiteSupport
          (isCompact_closedBall ρ r₂)).toFinset,
        ((MeromorphicOn.divisor xi (closedBall ρ r₁)) u : ℝ) := by
    rw [xiBallOrderSum, finsum_eq_sum_of_support_subset _ hsupp₁]
    push_cast
    rfl
  rw [modulusSlope, xi_circleAverage_sub_eq_divisor_sum ρ hr₁ h₁₂, hn₁,
    div_eq_iff hΔ.ne', Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hudom : u ∈ closedBall ρ r₂ :=
    (MeromorphicOn.divisor xi (closedBall ρ r₂)).supportWithinDomain
      (by rwa [Set.Finite.mem_toFinset] at hu)
  have hur₂ : ‖u - ρ‖ ≤ r₂ := by rwa [mem_closedBall, dist_eq_norm] at hudom
  by_cases hle : ‖u - ρ‖ ≤ r₁
  · have humem₁ : u ∈ closedBall ρ r₁ := by
      rw [mem_closedBall, dist_eq_norm]; exact hle
    rw [if_pos hle, xi_divisor_closedBall_eq_order_toNat humem₁,
      xi_divisor_closedBall_eq_order_toNat hudom]
  · have huzero : xi u = 0 := by
      by_contra hne
      have h0 : (analyticOrderAt xi u).toNat = 0 := (xi_orderToNat_eq_zero_iff u).mpr hne
      have hD0 : MeromorphicOn.divisor xi (closedBall ρ r₂) u = 0 := by
        rw [xi_divisor_closedBall_eq_order_toNat hudom, h0]
        rfl
      rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
      exact hu hD0
    exact absurd huzero (hfree u (not_le.mp hle) hur₂)

/-- **The disproof surface.**  A single nonzero two-circle slope sample of `log ‖ξ‖` over a ball
contained in the right half-plane refutes the Riemann Hypothesis: two circle averages of the
modulus at one center, at any scale, with no zero located and no phase read. -/
theorem not_riemannHypothesis_of_modulusSlope_ne_zero {ρ : ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (hhalf : 1 / 2 ≤ ρ.re - r₂)
    (hslope : modulusSlope ρ r₁ r₂ ≠ 0) : ¬ RiemannHypothesis := by
  intro hRH
  apply hslope
  rw [modulusSlope_eq_zero_iff_ball_zeroFree ρ hr₁ h₁₂]
  intro z hz
  refine rh_iff_xi_ne_zero_right.mp hRH z ?_
  rw [mem_rightHalf]
  have hzn : ‖z - ρ‖ < r₂ := by rwa [mem_ball, dist_eq_norm] at hz
  have hre : |(z - ρ).re| ≤ ‖z - ρ‖ := Complex.abs_re_le_norm _
  have : ρ.re - z.re ≤ ‖z - ρ‖ := by
    have := neg_abs_le (z - ρ).re
    simp only [Complex.sub_re] at hre this
    linarith [abs_le.mp hre]
  linarith

/-- **The proof surface.**  RH is the flatness of the modulus-slope field: the two-circle slope
of `log ‖ξ‖` vanishes at every center and every radius pair whose enclosed ball stays in the
right half-plane.  All scales at once — no shrinking-radius germ quantifier. -/
theorem rh_iff_forall_rightHalf_modulusSlope_eq_zero :
    RiemannHypothesis ↔
      ∀ (ρ : ℂ) (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → 1 / 2 ≤ ρ.re - r₂ →
        modulusSlope ρ r₁ r₂ = 0 := by
  constructor
  · intro hRH ρ r₁ r₂ hr₁ h₁₂ hhalf
    by_contra h
    exact not_riemannHypothesis_of_modulusSlope_ne_zero hr₁ h₁₂ hhalf h hRH
  · intro hflat
    rw [rh_iff_xi_ne_zero_right]
    intro ρ hρ hzero
    have hρre : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
    have hr₂ : 0 < ρ.re - 1 / 2 := by linarith
    have hsample := hflat ρ ((ρ.re - 1 / 2) / 2) (ρ.re - 1 / 2)
      (by linarith) (by linarith) (by linarith)
    have hfree := (modulusSlope_eq_zero_iff_ball_zeroFree ρ
      (by linarith) (by linarith)).mp hsample
    exact hfree ρ (mem_ball_self hr₂) hzero

end

end RHTower
