import GaloisForLFunctions.HTGeometry.OscillatorRecessiveLimits

/-!
# The ladder identity for the harmonic oscillator

For a solution of `v″ = (ξ² − μ)v` set

`A v = v′ + ξ v` ,   `B = v v′ + ξ v²` .

A single differentiation gives `B′ = (A v)² + (1 − μ)v²`, so by the fundamental theorem of calculus

`∫_{-R}^{R} (A v)² = B(R) − B(−R) + (μ − 1)∫_{-R}^{R} v²` .

When the boundary term vanishes at infinity — which it does for a square-integrable solution — this
becomes `‖A v‖² = (μ − 1)‖v‖²`, so `μ ≥ 1` for a nontrivial solution.  Moreover `A v` solves the
same equation with `μ` replaced by `μ − 2`, so the argument iterates.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The lowering operator applied to a solution. -/
noncomputable def oscLower (v v' : ℝ → ℝ) (x : ℝ) : ℝ := v' x + x * v x

/-- Derivative of the lowered solution. -/
noncomputable def oscLowerDeriv (mu : ℝ) (v v' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (x ^ (2 : ℕ) - mu + 1) * v x + x * v' x

/-- Boundary function of the ladder identity. -/
noncomputable def oscBoundary (v v' : ℝ → ℝ) (x : ℝ) : ℝ := oscProduct v v' x + x * v x ^ (2 : ℕ)

/-- A solution and its derivative are continuous. -/
theorem continuous_of_hasDerivAt {v v' : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (v' x) x) :
    Continuous v :=
  continuous_iff_continuousAt.2 fun x => (hv x).continuousAt

/-- **Boundary derivative.**  `B′ = (A v)² + (1 − μ)v²`. -/
theorem hasDerivAt_oscBoundary {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ (2 : ℕ) - mu) * v x) x) (x : ℝ) :
    HasDerivAt (oscBoundary v v') (oscLower v v' x ^ (2 : ℕ) + (1 - mu) * v x ^ (2 : ℕ)) x := by
  have h1 := hasDerivAt_oscProduct hv hv' x
  have hb : HasDerivAt (fun y => v y ^ (2 : ℕ)) (2 * v x * v' x) x := by
    refine ((hv x).pow 2).congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun y => y * v y ^ (2 : ℕ)) (v x ^ (2 : ℕ) + x * (2 * v x * v' x)) x := by
    refine ((hasDerivAt_id x).mul hb).congr_deriv ?_
    simp only [id_eq]
    ring
  refine (h1.add h2).congr_deriv ?_
  rw [oscLower]
  ring

/-- **The lowered solution solves the shifted equation.** -/
theorem hasDerivAt_oscLower {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ (2 : ℕ) - mu) * v x) x) (x : ℝ) :
    HasDerivAt (oscLower v v') (oscLowerDeriv mu v v' x) x := by
  have h : HasDerivAt (fun y => v' y + y * v y)
      ((x ^ (2 : ℕ) - mu) * v x + (v x + x * v' x)) x := by
    refine ((hv' x).add ((hasDerivAt_id x).mul (hv x))).congr_deriv ?_
    simp only [id_eq]
    ring
  refine h.congr_deriv ?_
  rw [oscLowerDeriv]
  ring

theorem hasDerivAt_oscLowerDeriv {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ (2 : ℕ) - mu) * v x) x) (x : ℝ) :
    HasDerivAt (oscLowerDeriv mu v v') ((x ^ (2 : ℕ) - (mu - 2)) * oscLower v v' x) x := by
  have hq : HasDerivAt (fun y : ℝ => y ^ (2 : ℕ) - mu + 1) (2 * x) x := by
    have := ((hasDerivAt_pow 2 x).sub_const mu).add_const 1
    simpa using this
  have h1 : HasDerivAt (fun y => (y ^ (2 : ℕ) - mu + 1) * v y)
      (2 * x * v x + (x ^ (2 : ℕ) - mu + 1) * v' x) x := hq.mul (hv x)
  have h2 : HasDerivAt (fun y => y * v' y) (v' x + x * ((x ^ (2 : ℕ) - mu) * v x)) x := by
    refine ((hasDerivAt_id x).mul (hv' x)).congr_deriv ?_
    simp only [id_eq]
    ring
  refine (h1.add h2).congr_deriv ?_
  rw [oscLower]
  ring

/-- **Ladder identity on a symmetric interval.** -/
theorem integral_oscLower_sq_interval {mu : ℝ} {v v' : ℝ → ℝ} (R : ℝ)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ (2 : ℕ) - mu) * v x) x) :
    (∫ x in (-R)..R, oscLower v v' x ^ (2 : ℕ))
      = oscBoundary v v' R - oscBoundary v v' (-R)
        + (mu - 1) * ∫ x in (-R)..R, v x ^ (2 : ℕ) := by
  have hcv : Continuous v := continuous_of_hasDerivAt hv
  have hcv' : Continuous v' := continuous_of_hasDerivAt hv'
  have hcL : Continuous fun x => oscLower v v' x ^ (2 : ℕ) := by
    have : Continuous fun x => oscLower v v' x := by
      simp only [oscLower]
      exact hcv'.add (continuous_id.mul hcv)
    exact this.pow 2
  have hcs : Continuous fun x => v x ^ (2 : ℕ) := hcv.pow 2
  have hFTC : (∫ x in (-R)..R, (oscLower v v' x ^ (2 : ℕ) + (1 - mu) * v x ^ (2 : ℕ)))
      = oscBoundary v v' R - oscBoundary v v' (-R) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_oscBoundary hv hv' x) ?_
    exact (hcL.add (continuous_const.mul hcs)).intervalIntegrable _ _
  have hf : IntervalIntegrable (fun x : ℝ => oscLower v v' x ^ (2 : ℕ)) volume (-R) R := by
    apply Continuous.intervalIntegrable
    exact hcL
  have hg : IntervalIntegrable (fun x : ℝ => (1 - mu) * v x ^ (2 : ℕ)) volume (-R) R := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul hcs
  have hsplit : (∫ x in (-R)..R, (oscLower v v' x ^ (2 : ℕ) + (1 - mu) * v x ^ (2 : ℕ)))
      = (∫ x in (-R)..R, oscLower v v' x ^ (2 : ℕ))
        + ∫ x in (-R)..R, (1 - mu) * v x ^ (2 : ℕ) :=
    intervalIntegral.integral_add hf hg
  have hconst : (∫ x in (-R)..R, (1 - mu) * v x ^ (2 : ℕ))
      = (1 - mu) * ∫ x in (-R)..R, v x ^ (2 : ℕ) :=
    intervalIntegral.integral_const_mul _ _
  rw [hsplit, hconst] at hFTC
  linarith

/-- The symmetric truncations of the ladder identity are uniformly bounded, so the lowered solution
is square integrable. -/
theorem integrable_oscLower_sq {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ (2 : ℕ) - mu) * v x) x)
    (hB : Tendsto (fun R : ℝ => oscBoundary v v' R) atTop (𝓝 0))
    (hBneg : Tendsto (fun R : ℝ => oscBoundary v v' (-R)) atTop (𝓝 0))
    (hint : Integrable (fun x => v x ^ (2 : ℕ))) :
    Integrable (fun x => oscLower v v' x ^ (2 : ℕ)) := by
  have hcv : Continuous v := continuous_of_hasDerivAt hv
  have hcv' : Continuous v' := continuous_of_hasDerivAt hv'
  have hcL : Continuous fun x => oscLower v v' x ^ (2 : ℕ) := by
    have hc : Continuous fun x => oscLower v v' x := by
      simp only [oscLower]
      exact hcv'.add (continuous_id.mul hcv)
    exact hc.pow 2
  have hB1 : ∀ᶠ R : ℝ in atTop, |oscBoundary v v' R| < 1 := by
    have := hB.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hB.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)] with R hR
    simpa [Real.dist_eq] using hR
  have hB2 : ∀ᶠ R : ℝ in atTop, |oscBoundary v v' (-R)| < 1 := by
    filter_upwards [hBneg.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)] with R hR
    simpa [Real.dist_eq] using hR
  refine MeasureTheory.integrable_of_intervalIntegral_norm_bounded
    (2 + |mu - 1| * ∫ x, v x ^ (2 : ℕ)) (a := fun R : ℝ => -R) (b := fun R : ℝ => R)
    (l := atTop) ?_ (Filter.tendsto_neg_atBot_iff.2 Filter.tendsto_id) Filter.tendsto_id ?_
  · intro R
    exact (hcL.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [hB1, hB2, eventually_ge_atTop (0 : ℝ)] with R h1 h2 hR0
    have hid := integral_oscLower_sq_interval (mu := mu) R hv hv'
    have hnorm : (∫ x in (-R)..R, ‖oscLower v v' x ^ (2 : ℕ)‖)
        = ∫ x in (-R)..R, oscLower v v' x ^ (2 : ℕ) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hnorm, hid]
    have hsub : (∫ x in (-R)..R, v x ^ (2 : ℕ)) ≤ ∫ x, v x ^ (2 : ℕ) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact MeasureTheory.setIntegral_le_integral hint
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
    have hsubnn : (0 : ℝ) ≤ ∫ x in (-R)..R, v x ^ (2 : ℕ) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
    have hmul : (mu - 1) * (∫ x in (-R)..R, v x ^ (2 : ℕ)) ≤ |mu - 1| * ∫ x, v x ^ (2 : ℕ) := by
      have h3 : (mu - 1) * (∫ x in (-R)..R, v x ^ (2 : ℕ))
          ≤ |mu - 1| * (∫ x in (-R)..R, v x ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hsubnn
      have h4 : |mu - 1| * (∫ x in (-R)..R, v x ^ (2 : ℕ)) ≤ |mu - 1| * ∫ x, v x ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hsub (abs_nonneg _)
      linarith
    have hb1 : oscBoundary v v' R ≤ 1 := le_of_lt (lt_of_le_of_lt (le_abs_self _) h1)
    have hb2 : -oscBoundary v v' (-R) ≤ 1 := by
      have := neg_le_abs (oscBoundary v v' (-R))
      linarith
    linarith

/-- **Ladder norm identity.**  With vanishing boundary terms the lowered solution's square norm is
`(μ − 1)` times the original's. -/
theorem integral_oscLower_sq_eq {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ (2 : ℕ) - mu) * v x) x)
    (hB : Tendsto (fun R : ℝ => oscBoundary v v' R) atTop (𝓝 0))
    (hBneg : Tendsto (fun R : ℝ => oscBoundary v v' (-R)) atTop (𝓝 0))
    (hint : Integrable (fun x => v x ^ (2 : ℕ))) :
    (∫ x, oscLower v v' x ^ (2 : ℕ)) = (mu - 1) * ∫ x, v x ^ (2 : ℕ) := by
  have hintL := integrable_oscLower_sq hv hv' hB hBneg hint
  have h1 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, oscLower v v' x ^ (2 : ℕ)) atTop
      (𝓝 (∫ x, oscLower v v' x ^ (2 : ℕ))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hintL
      (Filter.tendsto_neg_atBot_iff.2 Filter.tendsto_id) Filter.tendsto_id
  have h2 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, v x ^ (2 : ℕ)) atTop (𝓝 (∫ x, v x ^ (2 : ℕ))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hint
      (Filter.tendsto_neg_atBot_iff.2 Filter.tendsto_id) Filter.tendsto_id
  have h3 : Tendsto (fun R : ℝ => oscBoundary v v' R - oscBoundary v v' (-R)
      + (mu - 1) * ∫ x in (-R)..R, v x ^ (2 : ℕ)) atTop
      (𝓝 (0 - 0 + (mu - 1) * ∫ x, v x ^ (2 : ℕ))) :=
    (hB.sub hBneg).add (h2.const_mul (mu - 1))
  have heq : (fun R : ℝ => ∫ x in (-R)..R, oscLower v v' x ^ (2 : ℕ))
      = fun R : ℝ => oscBoundary v v' R - oscBoundary v v' (-R)
        + (mu - 1) * ∫ x in (-R)..R, v x ^ (2 : ℕ) :=
    funext fun R => integral_oscLower_sq_interval R hv hv'
  rw [heq] at h1
  have := tendsto_nhds_unique h1 h3
  simpa using this

/-- **The separation constant is at least one** for a nontrivial square-integrable solution. -/
theorem one_le_of_integrable_of_pos {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ (2 : ℕ) - mu) * v x) x)
    (hB : Tendsto (fun R : ℝ => oscBoundary v v' R) atTop (𝓝 0))
    (hBneg : Tendsto (fun R : ℝ => oscBoundary v v' (-R)) atTop (𝓝 0))
    (hint : Integrable (fun x => v x ^ (2 : ℕ)))
    (hpos : 0 < ∫ x, v x ^ (2 : ℕ)) : 1 ≤ mu := by
  have hid := integral_oscLower_sq_eq hv hv' hB hBneg hint
  have hnn : (0 : ℝ) ≤ ∫ x, oscLower v v' x ^ (2 : ℕ) :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg _
  rw [hid] at hnn
  nlinarith

end GaloisForLFunctions.HTGeometry
