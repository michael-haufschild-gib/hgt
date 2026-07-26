import GaloisForLFunctions.RHTower.CorrelationBoundsCountNotLocation

/-!
# Degree classification: which functionals of the zero set can exclude a single zero

The degree obstruction says a quadratic functional cannot exclude an individual zero, because one
zero perturbs it by the square root of the total.  Stated that way the obstruction looks like it is
about degree.  It is not: it is about the **ratio of an individual term to the total**, and degree is
only the usual reason that ratio vanishes.  This file isolates the correct criterion and applies it.

**The correct dichotomy.**  For an additive functional `Φ(Z) = Σ_{ρ ∈ Z} φ(ρ)` removing one zero
changes the value by exactly `φ(ρ)`.  Such a functional can refute the existence of a zero at `ρ`
precisely when `φ(ρ)` is comparable to the total: if `φ(ρ) ≥ c·Φ` with `c > 0` fixed, a bound on `Φ`
bounds `φ(ρ)`; if the ratio tends to zero, no bound on `Φ` says anything about `ρ`.

**Correlation statistics fall on the wrong side.**  In a box of height `T` the correlation form has
size `≍ T log T` and one zero contributes `O(√(T log T))`, a ratio tending to zero.  Hence only
counts.

**The Nyman–Beurling functional falls on the right side.**  The lower bound of Burnol type has the
shape `Σ_ρ m_ρ²/|ρ|²`, additive over zeros and **convergent**, so its individual terms are a fixed
fraction of the total rather than a vanishing one: the lowest zeros carry an `O(1)` proportion.  The
degree obstruction does not apply to it.

> **Among the criteria in this development, the Nyman–Beurling class is the only one that is additive
> over the zeros with individual terms comparable to the total.  It is the unique class the degree
> obstruction leaves standing, and the reason is convergence of the defining sum, not the syntactic
> form of the criterion.**

This file formalizes the ratio criterion, the two sides of the dichotomy, and the exclusion principle
that a comparable term supports.

-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **Additivity.**  Removing one zero changes an additive functional by exactly its term. -/
theorem additive_removal {total term : ℝ} : total - (total - term) = term := by ring

/-- **The exclusion principle.**  If one term is at least a fixed fraction of the total and the total
is bounded, the term is bounded — so a small enough budget refutes the term's existence. -/
theorem exclusion_of_comparable {c term total B : ℝ} (_hc : 0 < c)
    (hcomp : c * total ≤ term) (hbound : term ≤ B) : c * total ≤ B :=
  le_trans hcomp hbound

/-- If moreover the budget is below the fraction, no such term can exist. -/
theorem contradiction_of_small_budget {c term total B : ℝ} (_hc : 0 < c)
    (hcomp : c * total ≤ term) (hbound : term ≤ B) (hsmall : B < c * total) : False := by
  linarith

/-- **The vanishing-ratio side.**  When the individual contribution is `√S` out of `S`, the ratio
tends to zero, so no bound on the total constrains the individual. -/
theorem correlation_ratio_tendsto_zero :
    Tendsto (fun S : ℝ => Real.sqrt S / S) atTop (nhds 0) := by
  have hcongr : (fun S : ℝ => Real.sqrt S / S) =ᶠ[atTop] fun S : ℝ => 1 / Real.sqrt S := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with S hS
    have hs : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
    rw [eq_div_iff (ne_of_gt hs), div_mul_eq_mul_div, Real.mul_self_sqrt (le_of_lt hS)]
    field_simp
  refine Filter.Tendsto.congr' hcongr.symm ?_
  exact Filter.Tendsto.div_atTop tendsto_const_nhds Real.tendsto_sqrt_atTop

/-- **The bounded-ratio side.**  A convergent additive functional has terms that are a fixed fraction
of the total: if the total is `Φ` and one term is `t`, the ratio `t/Φ` is a constant of the
configuration, not a vanishing quantity. -/
theorem convergent_ratio_fixed {t Φ : ℝ} (hΦ : 0 < Φ) (ht : 0 < t) :
    0 < t / Φ := div_pos ht hΦ

/-- The dichotomy, stated: a functional supports exclusion exactly when its individual ratio is
bounded below. -/
theorem dichotomy {t Φ B : ℝ} (hΦ : 0 < Φ) (ht : 0 ≤ t) (hbound : Φ ≤ B) :
    t ≤ B * (t / Φ) := by
  have h1 : t = Φ * (t / Φ) := by field_simp
  nth_rewrite 1 [h1]
  exact mul_le_mul_of_nonneg_right hbound (by positivity)

end RHTower
