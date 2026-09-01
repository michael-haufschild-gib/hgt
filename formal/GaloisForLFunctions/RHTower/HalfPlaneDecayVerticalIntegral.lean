import Mathlib

/-!
# The vertical integral of a decaying analytic function is `O(1)`

Levinson's budget contains the far-right integrals `∫_{T₁}^{T₂} log‖H(d+it)‖ dt` and
`∫_{T₁}^{T₂} Re (H′/H)(d+it) dt` for `H` the mollified detector.  A pointwise bound would give
`O(T₂ − T₁)`, which is exactly the order of the main term and therefore fatal.

Both integrands are the restriction to a vertical line of a function analytic on the closed
half-plane `Re s ≥ d` and decaying like `e^{-α Re s}` there.  Cauchy's theorem on the rectangle
`[d,X] × [T₁,T₂]`, letting `X → ∞`, converts the vertical integral into two horizontal ones,

```text
i·∫_{T₁}^{T₂} F(d+it) dt = ∫_d^∞ F(x+iT₁) dx − ∫_d^∞ F(x+iT₂) dx,
```

whose right-hand side is bounded by `2K e^{-αd}/α`, independently of the window length.  This is the
Lean form of the classical remark that the logarithm of a mollified zeta detector is an absolutely
convergent Dirichlet series with no constant term.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

noncomputable section

namespace RHTower

/-- The exponential tail integral, with its explicit antiderivative. -/
theorem integral_exp_neg_le {α K d X : ℝ} (hα : 0 < α) (hK : 0 ≤ K) :
    (∫ x in d..X, K * Real.exp (-α * x)) ≤ K * Real.exp (-α * d) / α := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -K * Real.exp (-α * y) / α)
      (K * Real.exp (-α * x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => -α * y) (-α) x := by
      simpa using (hasDerivAt_id x).const_mul (-α)
    have h2 := (Real.hasDerivAt_exp (-α * x)).comp x h1
    have h3 := (h2.const_mul (-K)).div_const α
    have hval : -K * (Real.exp (-α * x) * -α) / α = K * Real.exp (-α * x) := by
      field_simp
    exact h3.congr_deriv hval
  have heq : (∫ x in d..X, K * Real.exp (-α * x))
      = (-K * Real.exp (-α * X) / α) - (-K * Real.exp (-α * d) / α) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) ?_
    exact (Continuous.intervalIntegrable (by fun_prop) d X)
  rw [heq]
  have hnum : K * Real.exp (-α * d) - K * Real.exp (-α * X) ≤ K * Real.exp (-α * d) := by
    have hB : (0 : ℝ) ≤ K * Real.exp (-α * X) := by positivity
    linarith
  calc -K * Real.exp (-α * X) / α - -K * Real.exp (-α * d) / α
      = (K * Real.exp (-α * d) - K * Real.exp (-α * X)) / α := by ring
    _ ≤ (K * Real.exp (-α * d)) / α := by gcongr

/-- **The vertical integral of a decaying analytic function is bounded independently of the window
length.** -/
theorem norm_integral_vertical_le_of_halfPlane_decay
    {F : ℂ → ℂ} {d T₁ T₂ K α : ℝ} (hT : T₁ ≤ T₂) (hα : 0 < α) (hK : 0 ≤ K)
    (hF : ∀ z : ℂ, d ≤ z.re → AnalyticAt ℂ F z)
    (hbound : ∀ z : ℂ, d ≤ z.re → ‖F z‖ ≤ K * Real.exp (-α * z.re)) :
    ‖∫ t in T₁..T₂, F ((d : ℂ) + (t : ℂ) * I)‖ ≤ 2 * (K * Real.exp (-α * d) / α) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- pick a far-right edge at which the connecting vertical integral is negligible
  have htend : Tendsto (fun X : ℝ => (T₂ - T₁) * (K * Real.exp (-α * X))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X : ℝ => α * X) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hα tendsto_id
    have h2 : Tendsto (fun X : ℝ => Real.exp (-(α * X))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := h2.const_mul ((T₂ - T₁) * K)
    rw [mul_zero] at h3
    refine h3.congr fun X => ?_
    rw [show -α * X = -(α * X) by ring]
    ring
  obtain ⟨X, hXd, hXsmall⟩ : ∃ X : ℝ, d ≤ X ∧ (T₂ - T₁) * (K * Real.exp (-α * X)) < ε := by
    have hev := (htend.eventually (eventually_lt_nhds hε)).and (eventually_ge_atTop d)
    obtain ⟨X, hX⟩ := hev.exists
    exact ⟨X, hX.2, hX.1⟩
  -- Cauchy on the rectangle `[d,X] × [T₁,T₂]`
  set z : ℂ := (d : ℂ) + (T₁ : ℂ) * I with hz
  set w : ℂ := (X : ℂ) + (T₂ : ℂ) * I with hw
  have hzre : z.re = d := by rw [hz]; simp
  have hzim : z.im = T₁ := by rw [hz]; simp
  have hwre : w.re = X := by rw [hw]; simp
  have hwim : w.im = T₂ := by rw [hw]; simp
  have hDiff : DifferentiableOn ℂ F (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
    intro s hs
    have hsre : d ≤ s.re := by
      have h := (Complex.mem_reProdIm.mp hs).1
      rw [hzre, hwre, uIcc_of_le hXd] at h
      exact h.1
    exact ((hF s hsre).differentiableAt).differentiableWithinAt
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hDiff
  rw [hzre, hzim, hwre, hwim] at hcauchy
  -- rearrange
  have hrearr : I • (∫ y in T₁..T₂, F ((d : ℂ) + (y : ℂ) * I))
      = ((∫ x in d..X, F ((x : ℂ) + (T₁ : ℂ) * I))
          - ∫ x in d..X, F ((x : ℂ) + (T₂ : ℂ) * I))
        + I • ∫ y in T₁..T₂, F ((X : ℂ) + (y : ℂ) * I) := by
    simp only [smul_eq_mul] at hcauchy ⊢
    linear_combination -hcauchy
  have hnormI : ‖I • (∫ y in T₁..T₂, F ((d : ℂ) + (y : ℂ) * I))‖
      = ‖∫ y in T₁..T₂, F ((d : ℂ) + (y : ℂ) * I)‖ := by
    rw [norm_smul]
    simp
  have hhoriz : ∀ T : ℝ, ‖∫ x in d..X, F ((x : ℂ) + (T : ℂ) * I)‖
      ≤ K * Real.exp (-α * d) / α := by
    intro T
    have hre : ∀ x : ℝ, d ≤ x → d ≤ ((x : ℂ) + (T : ℂ) * I).re := by
      intro x hx
      simpa using hx
    have hcontOn : ContinuousOn (fun x : ℝ => F ((x : ℂ) + (T : ℂ) * I)) (uIcc d X) := by
      intro x hx
      rw [uIcc_of_le hXd] at hx
      have hc : ContinuousAt (F ∘ (fun y : ℝ => (y : ℂ) + (T : ℂ) * I)) x :=
        ContinuousAt.comp ((hF _ (hre x hx.1)).continuousAt)
          (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + (T : ℂ) * I) x)
      have hc' : ContinuousAt (fun y : ℝ => F ((y : ℂ) + (T : ℂ) * I)) x := by
        simpa [Function.comp_def] using hc
      exact hc'.continuousWithinAt
    have hnormle : ‖∫ x in d..X, F ((x : ℂ) + (T : ℂ) * I)‖
        ≤ ∫ x in d..X, ‖F ((x : ℂ) + (T : ℂ) * I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hXd
    refine le_trans hnormle (le_trans ?_ (integral_exp_neg_le (d := d) (X := X) hα hK))
    refine intervalIntegral.integral_mono_on hXd hcontOn.norm.intervalIntegrable
      (Continuous.intervalIntegrable (by fun_prop) d X) ?_
    intro x hx
    have hb := hbound ((x : ℂ) + (T : ℂ) * I) (hre x hx.1)
    have hxre : ((x : ℂ) + (T : ℂ) * I).re = x := by simp
    rwa [hxre] at hb
  have hvert : ‖∫ y in T₁..T₂, F ((X : ℂ) + (y : ℂ) * I)‖
      ≤ (T₂ - T₁) * (K * Real.exp (-α * X)) := by
    have hconst : ∀ y ∈ Set.uIoc T₁ T₂,
        ‖F ((X : ℂ) + (y : ℂ) * I)‖ ≤ K * Real.exp (-α * X) := by
      intro y _
      have hre : d ≤ ((X : ℂ) + (y : ℂ) * I).re := by simpa using hXd
      have hb := hbound ((X : ℂ) + (y : ℂ) * I) hre
      have hxre : ((X : ℂ) + (y : ℂ) * I).re = X := by simp
      rwa [hxre] at hb
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hconst
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T₂ - T₁), mul_comm] at h
  have hnormvert : ‖I • (∫ y in T₁..T₂, F ((X : ℂ) + (y : ℂ) * I))‖
      = ‖∫ y in T₁..T₂, F ((X : ℂ) + (y : ℂ) * I)‖ := by
    rw [norm_smul]; simp
  have hchain : ‖∫ y in T₁..T₂, F ((d : ℂ) + (y : ℂ) * I)‖
      ≤ (K * Real.exp (-α * d) / α) + (K * Real.exp (-α * d) / α)
        + (T₂ - T₁) * (K * Real.exp (-α * X)) := by
    rw [← hnormI, hrearr]
    refine le_trans (norm_add_le _ _) ?_
    have hsub := norm_sub_le (∫ x in d..X, F ((x : ℂ) + (T₁ : ℂ) * I))
      (∫ x in d..X, F ((x : ℂ) + (T₂ : ℂ) * I))
    have h1 := hhoriz T₁
    have h2 := hhoriz T₂
    rw [hnormvert]
    linarith [hsub, h1, h2, hvert]
  linarith [hchain, hXsmall]

end RHTower

end
