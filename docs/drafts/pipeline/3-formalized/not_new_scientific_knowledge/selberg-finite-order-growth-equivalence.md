# Selberg finite-order growth equivalence

- **ID:** `selberg-finite-order-growth-equivalence`
- **Status:** Stage 3 — formalized in Lean 4
- **Novelty:** `[LITERATURE]` analytic infrastructure; not new scientific knowledge
- **Lean module:** `GaloisForLFunctions.RHTower.SelbergClass.FiniteOrder`

## Exact theorem

For an entire function `f : ℂ → ℂ`, these are equivalent:

1. there are `A,B>0` and `ρ≥0` such that
   `‖f(z)‖ ≤ A exp(B ‖z‖^ρ)` for every `z`;
2. the same type of bound holds whenever `R≤‖z‖`, for some `R≥0`.

The module also constructs `EntireFiniteOrder` from the outside-disk form and derives the
outside-disk form from every existing carrier.

## Proof

Global implies outside-disk with `R=0`.  Conversely, continuity of the entire function makes its
image on the closed radius-`R` disk compact and bounded.  Replacing `A` by the maximum of the
outside prefactor and this compact bound gives the global inequality because the exponential factor
is at least one.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/SelbergClass/FiniteOrder.lean`: passed
- named module olean build: passed
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only
- umbrella import added; umbrella build deliberately not run
