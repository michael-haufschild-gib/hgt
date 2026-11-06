# Integrable functional-equation defect at unit density

- **ID:** integrable-fe-defect-at-unit-density
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Γ74
- **Statement:** A discrete positive spectrum beginning at 1, with atom masses at least 1 and pole residue at most 1, is the positive-integer counting measure whenever its Riemann functional-equation defect is integrable.

## Mathematical target

Let `1 = λ₀ < λ₁ < …`, `aₙ ≥ 1`, and `Σ aₙ/λₙ² < ∞`. The completed Dirichlet transform has the same strip regularity as the existing Hamburger receiver. Write its pole term as `β Γℝ(s−1)`, so the Dirichlet residue is `2β`. Assume `β` real and `β ≤ 1/2`. An integrable uncompleted defect should force `β = 1/2`, `λₙ = n+1`, and `aₙ = 1`.

## Argument to verify

The defect Laplace transform satisfies `|J(τ)| ≤ C‖τ‖⁻¹/²‖g‖₁`; hence `εJ(ε+iτ) → 0`, including at `τ=0`. The Abel cosine means therefore have limits `β/π` at zero and `aₙ/(2π)` at each atom. Positivity gives `1 ≤ aₙ ≤ 2β ≤ 1`. With equality, the existing cosine-gap argument forces every frequency integral and every positive integer present.

This addresses the unit-density boundary. The possibility of larger pole residue remains outside this statement; Γ74 stays partially solved unless that case is resolved.

## Proof status

Radial-limit argument under inspection. No Lean theorem yet.
