/-
# Böttcher tower — the periodic-point resonance (interior natural boundary, D2)

At a repelling periodic point `z₀` of `f_c` (`F = f_c^[p]`, `F z₀ = z₀`, multiplier `λ = F'(z₀)`,
`|λ| > 1`), a hypothetical analytic continuation `g` of `φ_c` satisfies the functional equation
`g ∘ F = g^k` (`k = 2^p`) near `z₀`. Since `g(z₀)` is a `(k-1)`-th root of unity
(`g(z₀)^k = g(z₀)`), differentiating forces the **resonance** `λ = k` at first order, and (by the
order-`m` Taylor analysis) `λ^m = k` in general — impossible for nonexceptional `c`, so `g` would be
constant, contradicting `|g| = exp(G_c)` non-constant on the basin.

This file proves the first-order resonance and its critical-point corollary (a repelling fixed point
forces `φ_c`'s continuation to have a critical point unless `λ = k`). General lemma; Mathlib only.
-/
import Mathlib

open Filter Topology

namespace Bottcher

/-- **First-order resonance.** If `g ∘ F = g^k` near a fixed point `z₀` of `F`, then
`g'(z₀)·F'(z₀) = k·g(z₀)^{k-1}·g'(z₀)` (differentiate the functional equation). -/
theorem resonance_first_order {g F : ℂ → ℂ} {z₀ : ℂ} {k : ℕ}
    (hg : DifferentiableAt ℂ g z₀) (hF : DifferentiableAt ℂ F z₀)
    (hFz : F z₀ = z₀) (heq : (g ∘ F) =ᶠ[𝓝 z₀] (fun z => g z ^ k)) :
    deriv g z₀ * deriv F z₀ = (k : ℂ) * g z₀ ^ (k - 1) * deriv g z₀ := by
  have hgF : HasDerivAt g (deriv g z₀) (F z₀) := by rw [hFz]; exact hg.hasDerivAt
  have h1 : HasDerivAt (g ∘ F) (deriv g z₀ * deriv F z₀) z₀ := hgF.comp z₀ hF.hasDerivAt
  have h1' : HasDerivAt (fun z => g z ^ k) (deriv g z₀ * deriv F z₀) z₀ :=
    h1.congr_of_eventuallyEq heq.symm
  have h2 : HasDerivAt (fun z => g z ^ k) ((k : ℂ) * g z₀ ^ (k - 1) * deriv g z₀) z₀ :=
    hg.hasDerivAt.pow k
  exact h1'.unique h2

/-- **First-order resonance obstruction.** If the fixed value `g(z₀)` is a `(k-1)`-th root of unity and
the multiplier `F'(z₀) ≠ k`, then `g'(z₀) = 0`: a repelling periodic point forces the continuation of
`φ_c` to have a critical point there (the first step toward the full order-`m` resonance `λ^m = k`,
whose failure for nonexceptional `c` is the interior `J_c` natural boundary). -/
theorem deriv_eq_zero_of_resonance {g F : ℂ → ℂ} {z₀ : ℂ} {k : ℕ}
    (hg : DifferentiableAt ℂ g z₀) (hF : DifferentiableAt ℂ F z₀)
    (hFz : F z₀ = z₀) (heq : (g ∘ F) =ᶠ[𝓝 z₀] (fun z => g z ^ k))
    (hroot : g z₀ ^ (k - 1) = 1) (hne : deriv F z₀ ≠ (k : ℂ)) :
    deriv g z₀ = 0 := by
  have h := resonance_first_order hg hF hFz heq
  rw [hroot, mul_one] at h
  have hh : deriv g z₀ * (deriv F z₀ - (k : ℂ)) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hh with h1 | h2
  · exact h1
  · exact absurd (by linear_combination h2 : deriv F z₀ = (k : ℂ)) hne

end Bottcher
