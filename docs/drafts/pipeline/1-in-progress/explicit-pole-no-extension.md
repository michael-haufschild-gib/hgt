# Explicit pole discharges the no-extension interface

- **ID:** explicit-pole-no-extension
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / INTERFACE DISCHARGE
- **Source:** RHTower `NoCrossColumnHealing` + elementary punctured-neighbourhood limit
- **Statement:** `[CONJECTURE]` The reciprocal column `z ↦ (z-b)⁻¹` has `NoExtensionAt` at `b` on the punctured plane. Consequently, multiplying it by an entire nonvanishing partner gives an unconditional instance of the finite-column no-healing law.

## Goal

Supply a genuine analytic provider for the currently providerless `NoExtensionAt` Prop, then
instantiate its no-healing consumer without retaining a boundary-obstruction hypothesis.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: complete proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, focused build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: not intended; interface discharge only

## Approach

If an analytic element `g` agreed with `(z-b)⁻¹` on a punctured neighbourhood, continuity would
make `(z-b)g(z)` tend to zero at `b`.  On that same punctured neighbourhood the product is exactly
one, so uniqueness of limits gives `0 = 1`.  An exponential partner is entire and never zero, so
the existing no-healing theorem then transfers the obstruction to `exp(z)/(z-b)`.
