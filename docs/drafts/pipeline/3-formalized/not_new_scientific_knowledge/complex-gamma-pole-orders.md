# Exact complex Gamma pole orders

- **ID:** `complex-gamma-pole-orders`
- **Status:** Stage 3 — formalized in Lean 4
- **Novelty:** `[LITERATURE]` analytic infrastructure; not new scientific knowledge
- **Lean module:** `GaloisForLFunctions.RHTower.SelbergClass.GammaPoleOrder`

## Exact theorems

- `Gamma` has meromorphic order `-1` at zero.
- `Gamma` has meromorphic order `-1` at every `-n`, `n : ℕ`.
- Away from these points, `Gamma` has meromorphic order `0`.
- Therefore order `-1` occurs exactly at the nonpositive integers.
- For real `lambda ≠ 0`, the affine factor `Gamma(lambda*s + mu)` has order `-1` at
  `s = -(mu+n)/lambda`.

These are meromorphic-order statements because Mathlib totalizes `Gamma (-n)` to zero; testing the
function value would encode poles incorrectly.

## Proof spine

The residue limit `z Gamma(z) → 1` gives order zero for the product.  Additivity of meromorphic
order and the simple zero of `z` force order `-1` for `Gamma` at zero.  The recurrence
`Gamma(s+1)=s Gamma(s)` transports the order inductively because `s` is nonzero at every negative
integer.  At all other points, meromorphy plus continuity gives analyticity, and nonvanishing gives
order zero.  Affine order follows from composition with nonzero derivative.

## Audit

- target source check: passed
- named module olean build: passed
- all `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only
- umbrella import added; umbrella build deliberately not run
