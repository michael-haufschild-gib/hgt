import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Norm bounds for the continuous functional calculus

The isometric continuous functional calculus makes the operator norm of `cfc f a` the supremum of
`‖f‖` over the spectrum of `a`.  Two consequences used when a family of symbols is controlled only
on the spectrum: a pointwise bound bounds the operator, and symbols that become uniformly small on
the spectrum give operators converging to zero in norm.

This is the step that converts an estimate on rational symbols into a norm estimate on the
corresponding functions of a bounded self-adjoint operator.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContinuousFunctionalCalculus
open Filter Topology

variable {𝕜 A : Type*} {p : outParam (A → Prop)}
variable [RCLike 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
variable [IsometricContinuousFunctionalCalculus 𝕜 A p] [Nontrivial A]

/-- **CFC norm bound.**  A pointwise bound for the symbol on the spectrum bounds the norm of the
resulting operator, because that norm is attained as `‖f x‖` at some spectral point. -/
theorem norm_cfc_le_of_forall_le (f : 𝕜 → 𝕜) (a : A) {C : ℝ}
    (hf : ContinuousOn f (spectrum 𝕜 a)) (ha : p a)
    (h : ∀ x ∈ spectrum 𝕜 a, ‖f x‖ ≤ C) : ‖cfc f a‖ ≤ C := by
  obtain ⟨⟨x, hx, hxeq⟩, -⟩ := IsGreatest.norm_cfc (𝕜 := 𝕜) f a hf ha
  rw [← hxeq]
  exact h x hx

/-- **Norm convergence from uniform symbol smallness.**  If the symbols are eventually uniformly
small on the spectrum, the corresponding operators tend to zero in norm. -/
theorem tendsto_norm_cfc_zero {ι : Type*} {l : Filter ι} (g : ι → 𝕜 → 𝕜) (a : A) (ha : p a)
    (hcont : ∀ i, ContinuousOn (g i) (spectrum 𝕜 a))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x ∈ spectrum 𝕜 a, ‖g i x‖ ≤ ε) :
    Tendsto (fun i => ‖cfc (g i) a‖) l (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  filter_upwards [h (ε / 2) (by linarith)] with i hi
  have hb := norm_cfc_le_of_forall_le (g i) a (hcont i) ha hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-! ## The resolvent-coordinate symbol estimate -/

section Symbol

/-- **The resolvent symbol estimate.**  In the coordinate `x` of the bounded resolvent, the symbol
of `((-lambda)(A - lambda)^{-1} - 1)(A - rho)^{-1}` is `-x(1 + rho x)/(1 + s x)` with
`s = rho - lambda`.  On `[0, M]` it is bounded by `(1 + |rho| M)/s`, uniformly in `x`: the factor
`x/(1 + s x)` never exceeds `1/s`, which is what removes the spectral accumulation point at `0`
where the unscaled symbols do not converge. -/
theorem abs_resolventSymbol_le {rho M s x : ℝ} (hs : 0 < s) (hx0 : 0 ≤ x) (hxM : x ≤ M) :
    |x * (1 + rho * x) / (1 + s * x)| ≤ (1 + |rho| * M) / s := by
  have hden : 0 < 1 + s * x := by nlinarith
  have hM : 0 ≤ M := le_trans hx0 hxM
  have habs : |1 + rho * x| ≤ 1 + |rho| * M := by
    have h1 : |1 + rho * x| ≤ 1 + |rho| * x := by
      calc |1 + rho * x| ≤ |(1 : ℝ)| + |rho * x| := abs_add_le _ _
        _ = 1 + |rho| * x := by rw [abs_one, abs_mul, abs_of_nonneg hx0]
    nlinarith [abs_nonneg rho]
  have hnum : |x * (1 + rho * x)| ≤ x * (1 + |rho| * M) := by
    rw [abs_mul, abs_of_nonneg hx0]
    exact mul_le_mul_of_nonneg_left habs hx0
  have hfrac : x / (1 + s * x) ≤ 1 / s := by
    rw [div_le_div_iff₀ hden hs]
    nlinarith
  rw [abs_div, abs_of_pos hden]
  calc |x * (1 + rho * x)| / (1 + s * x)
      ≤ (x * (1 + |rho| * M)) / (1 + s * x) := by
        gcongr
    _ = (1 + |rho| * M) * (x / (1 + s * x)) := by ring
    _ ≤ (1 + |rho| * M) * (1 / s) := by
        refine mul_le_mul_of_nonneg_left hfrac ?_
        nlinarith [abs_nonneg rho]
    _ = (1 + |rho| * M) / s := by ring

/-- The symbol bound tends to zero as the shift recedes. -/
theorem tendsto_resolventSymbolBound_atTop (rho M : ℝ) :
    Tendsto (fun s : ℝ => (1 + |rho| * M) / s) atTop (𝓝 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id

/-- **Uniform smallness of the symbols.**  As the shift recedes, the resolvent symbols become
uniformly small on the spectral window `[0, M]`.  This is the scalar input of the strong resolvent
limit: the bound does not depend on `x`, so the accumulation point `0` is covered too. -/
theorem eventually_forall_abs_resolventSymbol_le (rho M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, ∀ x ∈ Set.Icc (0 : ℝ) M,
      |x * (1 + rho * x) / (1 + s * x)| ≤ ε := by
  have hb := tendsto_resolventSymbolBound_atTop rho M
  have hsmall := hb.eventually (Iio_mem_nhds hε)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with s hs hsm x hx
  exact le_trans (abs_resolventSymbol_le hs hx.1 hx.2) (le_of_lt hsm)

/-- **Uniform bound on the resolvent symbols.**  The symbol of `(-lambda)(A - lambda)^{-1}` in the
coordinate of the bounded resolvent is `(s - rho) x / (1 + s x)` with `s = rho - lambda`, and on
`[0, M]` it is bounded by `1 + |rho|` once `s >= 1`, uniformly in both `x` and `s`.  This is the
uniform operator bound the strong-limit bridge requires. -/
theorem abs_resolventFamilySymbol_le {rho s x : ℝ} (hs : 1 ≤ s) (hx0 : 0 ≤ x) :
    |(s - rho) * x / (1 + s * x)| ≤ 1 + |rho| := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hden : 0 < 1 + s * x := by nlinarith
  have hfrac : x / (1 + s * x) ≤ 1 / s := by
    rw [div_le_div_iff₀ hden hs0]
    nlinarith
  have hnum : |s - rho| ≤ s + |rho| := by
    calc |s - rho| ≤ |s| + |rho| := abs_sub _ _
      _ = s + |rho| := by rw [abs_of_pos hs0]
  have hkey : |(s - rho) * x| ≤ (s + |rho|) * x := by
    rw [abs_mul, abs_of_nonneg hx0]
    exact mul_le_mul_of_nonneg_right hnum hx0
  rw [abs_div, abs_of_pos hden]
  calc |(s - rho) * x| / (1 + s * x) ≤ ((s + |rho|) * x) / (1 + s * x) := by gcongr
    _ = (s + |rho|) * (x / (1 + s * x)) := by ring
    _ ≤ (s + |rho|) * (1 / s) := by
        refine mul_le_mul_of_nonneg_left hfrac ?_
        nlinarith [abs_nonneg rho]
    _ ≤ 1 + |rho| := by
        rw [mul_one_div, div_le_iff₀ hs0]
        nlinarith [abs_nonneg rho]

/-- **The link between the two symbols.**  Subtracting one from the family symbol and multiplying
by the coordinate produces exactly the estimate symbol.  This is the scalar shadow of
`(T_lambda - 1) ∘L B`, and it is where the numerator `-lambda x` cancels against `-s x` leaving the
`rho`-only numerator that the uniform estimate controls. -/
theorem resolventSymbol_sub_one_mul {rho s x : ℝ} (hden : 1 + s * x ≠ 0) :
    ((s - rho) * x / (1 + s * x) - 1) * x = -(x * (1 + rho * x) / (1 + s * x)) := by
  field_simp
  ring

end Symbol

end GaloisForLFunctions.HTGeometry
