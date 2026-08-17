import GaloisForLFunctions.HTGeometry.ComplexPairPeakRigidity

/-!
# Localization of the complex-pair comparison

The comparison `R(t) ≥ 2 e^{β t} cos (γ t)` is automatic wherever `e^{-β t} R(t) ≥ 2`, since the
cosine never exceeds `1`.  For a positive exponential sum `S(t) = e^{-β t} R(t)` the set where
`S < 2` is convex — `S` is a positive combination of exponentials, so `S'' ≥ 0` — and it is bounded
as soon as some exponent lies strictly below `β` and some strictly above.

Consequently the comparison, an inequality over the whole line involving infinitely many peaks of the
cosine, is equivalent to the same inequality on one explicit compact interval, hence to finitely many
instances of the arc criterion.  This is what turns the criterion into a decision procedure.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

variable {m : ℕ}

/-- Where the normalised sum reaches `2`, the comparison is automatic. -/
theorem cos_le_of_two_le_shift (c a : Fin m → ℝ) {β γ t : ℝ}
    (h : 2 ≤ expSum c (fun i => a i - β) t) :
    2 * Real.exp (β * t) * Real.cos (γ * t) ≤ expSum c a t := by
  have hshift := expSum_shift_apply c a β t
  have hpos : (0 : ℝ) < Real.exp (β * t) := Real.exp_pos _
  have hcos : Real.cos (γ * t) ≤ 1 := Real.cos_le_one _
  have hR : expSum c a t = Real.exp (β * t) * expSum c (fun i => a i - β) t := by
    rw [hshift, ← mul_assoc, ← Real.exp_add]
    simp
  rw [hR]
  have h1 : 2 * Real.cos (γ * t) ≤ expSum c (fun i => a i - β) t := by linarith
  calc 2 * Real.exp (β * t) * Real.cos (γ * t)
      = Real.exp (β * t) * (2 * Real.cos (γ * t)) := by ring
    _ ≤ Real.exp (β * t) * expSum c (fun i => a i - β) t :=
        mul_le_mul_of_nonneg_left h1 hpos.le

/-- A positive exponential sum is convex. -/
theorem convexOn_expSum (c a : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ConvexOn ℝ univ (expSum c a) := by
  refine convexOn_of_deriv2_nonneg convex_univ ((contDiff_expSum c a).continuous).continuousOn
    ((contDiff_expSum c a).differentiable (by simp)).differentiableOn ?_ (fun t _ => ?_)
  · rw [deriv_expSum]
    exact ((contDiff_expSum _ a).differentiable (by simp)).differentiableOn
  · rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, deriv_expSum,
      deriv_expSum, expSum]
    refine Finset.sum_nonneg (fun i _ => ?_)
    have hrw : c i * a i * a i = c i * a i ^ 2 := by ring
    rw [hrw]
    exact mul_nonneg (mul_nonneg (hc i) (sq_nonneg _)) (Real.exp_pos _).le

/-- **Boundedness of the exceptional set.**  If some exponent lies strictly below `β` and some
strictly above, the set where the normalised sum stays below `2` is bounded, with an explicit
bound. -/
theorem sublevel_bounded (c a : Fin m → ℝ) (hc : ∀ i, 0 < c i) {β : ℝ} {i j : Fin m}
    (hi : a i < β) (hj : β < a j) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, expSum c (fun k => a k - β) t < 2 → |t| ≤ T := by
  set Li : ℝ := Real.log (2 / c i) / (a i - β) with hLi
  set Uj : ℝ := Real.log (2 / c j) / (a j - β) with hUj
  refine ⟨max |Li| |Uj|, le_trans (abs_nonneg _) (le_max_left _ _), ?_⟩
  intro t ht
  have hterm : ∀ k : Fin m, c k * Real.exp ((a k - β) * t)
      ≤ expSum c (fun k => a k - β) t := by
    intro k
    rw [expSum]
    exact Finset.single_le_sum (f := fun k => c k * Real.exp ((a k - β) * t))
      (fun k _ => (mul_pos (hc k) (Real.exp_pos _)).le) (Finset.mem_univ k)
  have hstep : ∀ k : Fin m, (a k - β) * t < Real.log (2 / c k) := by
    intro k
    have h1 : c k * Real.exp ((a k - β) * t) < 2 := lt_of_le_of_lt (hterm k) ht
    have h2 : Real.exp ((a k - β) * t) < 2 / c k := by
      rw [lt_div_iff₀ (hc k)]
      linarith
    have := Real.log_lt_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at this
  have hdi : a i - β < 0 := by linarith
  have hdj : (0 : ℝ) < a j - β := by linarith
  have hlow : Li < t := by
    rw [hLi, div_lt_iff_of_neg hdi]
    have := hstep i
    linarith
  have hhigh : t < Uj := by
    rw [hUj, lt_div_iff₀ hdj]
    have := hstep j
    linarith
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h1 : -|Li| ≤ Li := neg_abs_le Li
    have h2 : -(max |Li| |Uj|) ≤ -|Li| := by
      simp
    linarith
  · have h1 : Uj ≤ |Uj| := le_abs_self Uj
    have h2 : |Uj| ≤ max |Li| |Uj| := le_max_right _ _
    linarith

/-- **Localization.**  Under strict straddling of `β` by the exponents, the comparison over the whole
line is equivalent to the comparison on one explicit compact interval. -/
theorem cos_dominated_iff_on_Icc (c a : Fin m → ℝ) (hc : ∀ i, 0 < c i) {β γ : ℝ} {i j : Fin m}
    (hi : a i < β) (hj : β < a j) :
    ∃ T : ℝ, 0 ≤ T ∧
      ((∀ t : ℝ, 2 * Real.exp (β * t) * Real.cos (γ * t) ≤ expSum c a t)
        ↔ ∀ t ∈ Icc (-T) T, 2 * Real.exp (β * t) * Real.cos (γ * t) ≤ expSum c a t) := by
  obtain ⟨T, hT0, hT⟩ := sublevel_bounded c a hc hi hj
  refine ⟨T, hT0, ⟨fun h t _ => h t, fun h t => ?_⟩⟩
  by_cases hmem : t ∈ Icc (-T) T
  · exact h t hmem
  · refine cos_le_of_two_le_shift c a ?_
    by_contra hcon
    push Not at hcon
    exact hmem (abs_le.mp (hT t hcon))

end GaloisForLFunctions.HTGeometry
