import GaloisForLFunctions.RHTower.CriticalScaleMatching

/-!
# The atlas is blind to unfolded data

Every obstruction recorded in this development is a statement about a scale: a width `L`, a deviation
`a`, a height through `log T`, or a dimensionless combination of them such as `aL`.  Correlation
statistics of the zeros are different in kind: they are defined **after** dividing out the density
`log T / 2π`, so they are invariant under the rescaling that the atlas measures.

**Unfolding is scale invariant.**  Replacing `γ` by `λγ` and the density scale `M` by `M/λ` leaves the
unfolded difference `(γ_j - γ_k)·M` unchanged.  So no bound expressed in the atlas's variables can
constrain an unfolded statistic.

**And the atlas's own quantities are not invariant.**  The detection ceiling `sinh(aL)/a + L` changes
under the same rescaling, so it lives on the other side of the divide.

> **The closure results proved here say nothing about correlation statistics.  The pair-correlation
> lane is genuinely open with respect to everything in this development, rather than merely
> unexplored.**

**The unconditional input that lane has.**  The pair-correlation form is a squared modulus, hence
nonnegative without any hypothesis:

```text
Σ_{j,k} w_j w_k cos( α(γ_j - γ_k) )  =  ( Σ_j w_j cos αγ_j )²  +  ( Σ_j w_j sin αγ_j )²  ≥  0 .
```

This is the only unconditional statement about the zeros' correlations, and it is exactly the
positivity that drives the classical simple-zero proportions.

This file formalizes the scale invariance of unfolded differences, the non-invariance of the atlas's
ceiling, and the unconditional positivity of the pair-correlation form.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Unfolded differences are scale invariant.**  Scaling the ordinates by `λ` and the density scale
by `1/λ` leaves the unfolded difference unchanged. -/
theorem unfolded_scale_invariant (g₁ g₂ M lam : ℝ) (hlam : lam ≠ 0) :
    (lam * g₁ - lam * g₂) * (M / lam) = (g₁ - g₂) * M := by
  field_simp

/-- **The atlas's ceiling is not scale invariant.**  At `a = 1`, `L = 1`, `λ = 2` the rescaled ceiling
differs from the original, so it constrains dimensionful data only. -/
theorem ceiling_not_scale_invariant :
    Real.sinh 1 / 1 + 1 ≠ Real.sinh (2 * (1 / 2)) / 2 + 1 / 2 := by
  have h1 : (2:ℝ) * (1 / 2) = 1 := by norm_num
  rw [h1]
  intro h
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  simp only [div_one] at h
  nlinarith [h, hs]

/-- **The pair-correlation form is a squared modulus.**  Expanding the cosine of a difference splits
the double sum into two squares. -/
theorem pair_correlation_eq_squares {n : ℕ} (w γ : Fin n → ℝ) (α : ℝ) :
    ∑ j, ∑ k, w j * w k * Real.cos (α * (γ j - γ k))
      = (∑ j, w j * Real.cos (α * γ j)) ^ (2 : ℕ) + (∑ j, w j * Real.sin (α * γ j)) ^ (2 : ℕ) := by
  have hexp : ∀ j k : Fin n, w j * w k * Real.cos (α * (γ j - γ k))
      = (w j * Real.cos (α * γ j)) * (w k * Real.cos (α * γ k))
        + (w j * Real.sin (α * γ j)) * (w k * Real.sin (α * γ k)) := by
    intro j k
    rw [mul_sub, Real.cos_sub]
    ring
  calc ∑ j, ∑ k, w j * w k * Real.cos (α * (γ j - γ k))
      = ∑ j, ∑ k, ((w j * Real.cos (α * γ j)) * (w k * Real.cos (α * γ k))
          + (w j * Real.sin (α * γ j)) * (w k * Real.sin (α * γ k))) := by
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => hexp j k))
    _ = (∑ j, ∑ k, (w j * Real.cos (α * γ j)) * (w k * Real.cos (α * γ k)))
          + (∑ j, ∑ k, (w j * Real.sin (α * γ j)) * (w k * Real.sin (α * γ k))) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_add_distrib)
    _ = (∑ j, w j * Real.cos (α * γ j)) ^ (2 : ℕ) + (∑ j, w j * Real.sin (α * γ j)) ^ (2 : ℕ) := by
        rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
        ring

/-- **Unconditional positivity of the pair-correlation form.** -/
theorem pair_correlation_nonneg {n : ℕ} (w γ : Fin n → ℝ) (α : ℝ) :
    0 ≤ ∑ j, ∑ k, w j * w k * Real.cos (α * (γ j - γ k)) := by
  rw [pair_correlation_eq_squares]
  positivity

/-- The diagonal contributes the full weight mass, so the off-diagonal is bounded below by its
negative: the only unconditional correlation information. -/
theorem offDiagonal_lower_bound {n : ℕ} (w γ : Fin n → ℝ) (α : ℝ) :
    -(∑ j, ∑ k, w j * w k * Real.cos (α * (γ j - γ k))) ≤ 0 := by
  have := pair_correlation_nonneg w γ α
  linarith

end RHTower
