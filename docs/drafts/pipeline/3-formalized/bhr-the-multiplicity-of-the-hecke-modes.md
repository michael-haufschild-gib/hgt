# BHR — the multiplicity of the Hecke modes

- **ID:** bhr-hecke-multiplicity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** continuation of `bhr-the-hecke-rigidity-of-the-cusp-modes.md` (its "Not formalized" item).
- **Statement:**
  1. Two solutions of `a'' = (κ − c/y²)a` on `y > 0` that tend to `0` as `y → ∞` are linearly dependent.
  2. For `f, f' ∈ S(λ)` and every `n`, the modes `a_n(f), a_n(f')` are linearly dependent; the modes of index `n` of
     `S(λ)` span at most a line.
  3. For every `λ` and every family `(c_p)`, the space of `f ∈ S(λ)` with `T_p f = c_p f` for all primes has dimension
     at most `2`.

## Paper proof
1. `W = ab' − a'b` has `W' = 0`. If `a → 0`: on `[y, y+1]`, `|a'(t) − a'(y)| ≤ M sup|a|` (`a'' = Va`, `|V| ≤ |κ| + |c|`
   for `y ≥ 1`), and `∫_y^{y+1} a' = a(y+1) − a(y)`, so `|a'(y)| ≤ (2 + M) sup_{[y,y+1]}|a| → 0`. Hence `W → 0`, `W = 0`.
   If `b(y₀) ≠ 0`, `h = b(y₀)a − a(y₀)b` solves the equation with `h(y₀) = 0`, `h'(y₀) = −W = 0`; uniqueness for the
   Lipschitz system `(h, h')' = (h', Vh)` on `[lo, hi] ∋ y₀, y` gives `h ≡ 0`.
2. `a_n(f)` solves the modal equation with `κ = (2πn)²`, `c = λ` (corpus `deckMode_hasDerivAt` through the `L²` bridge), and
   `|a_n(f)(y)| ≤ sup_x |f(x+iy)| → 0`. Apply (1).
3. By Hecke rigidity `f ↦ (a_1(f), a_{−1}(f))` is injective on the joint eigenspace, with values in the product of two
   spaces of dimension at most one.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheMultiplicityOfTheHeckeModes.lean`, wired into `BlackHoleRingdown.lean`,
checked with `lake --old env lean`, no messages. Axioms of `finrank_jointSpace_le_two`, `modal_proportional`:
`propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.HeckeCusp`) |
|---|---|
| (1) | `ModalSol`, `wronskian_const`, `tendsto_deriv_zero`, `modal_proportional` |
| (2) | `modalSol_fourierCoeff`, `tendsto_fourierCoeff`, `fourierCoeff_proportional`, `finrank_range_modeMap_le` |
| (3) | `jointSpace`, `finrank_jointSpace_le_two` |

## Not formalized
- The mirror `z ↦ −z̄` on `S(λ)`: it commutes with `T_p`, exchanges `a_n` and `a_{−n}`, and would give dimension at most one
  on each parity.

## Log
- 2026-11-08 — created and formalized.
