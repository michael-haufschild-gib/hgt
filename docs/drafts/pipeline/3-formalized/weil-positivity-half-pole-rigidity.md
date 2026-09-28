# Rigidity of Weil positivity across the √n barrier

**Status:** formalized (Lean, unconditional, standard axioms).
**Module:** `formal/GaloisForLFunctions/RHTower/WeilPositivityHalfPoleRigidity.lean`

## Statements
- `vonMangoldt_add_eq_zero_of_symbol_atom`: symbol = continuous `P` of linear growth plus `m|ĥ(0)|²`; `Λ + w` Weil-positive ⇒ `w = 0`.
- `pairing_sqrtStep`: `2πΣβ(n)n^{−½}φ(log n) = π|ĥ(0)|² + ∫|ĥ|²P_β`, with `β(n) = √n − √(n−1)`.
- `vonMangoldt_add_halfPole_eq_zero`: partial sums `κ(√n−1) + E(n)`, `Σ|E|/(n√n) < ∞` ⇒ `w = 0`.
- `vonMangoldt_add_squares_weilPositive_eq_zero`: `Λ + c·1_{squares}` Weil-positive ⇒ `c = 0`.

## Proof
1. `β(n)/√n = ∫_{log(n−1)}^{log n}½e^{(u−log n)/2}du`.
   - Adjacent intervals telescope to `½∫_0^{log M}φ = ½|ĥ(0)|²`.
   - The per-interval remainder is `(1/π)∫|ĥ|²K_n` by Fubini on `ℝ × [log(n−1), log n]`.
2. Concentration away from 0 (the atom decays like `S^{−6}`) gives `P ≤ 0`. Probes give `m ≥ 0`. Zero-mean probes give `P ≡ 0` and then `m = 0`. Resonators finish.
3. The remainder is handled by the L69 Abel symbol under `Σ|B(n)|/(n√n) < ∞`.

## Context
This is the uniqueness half of the Minkowski split. It extends L71 (`θ < ½`) to the prime-power scale `θ = ½` for regular (pole-type) growth.

## Arithmetic corollary (module `WeilPositivityPrimePowersForced`)
- `vonMangoldt_add_primePowerPart_weilPositive_eq_zero`: `(1 + c)`-rescaled prime-power weights are Weil-positive ⇒ `c = 0`.
- `primeWeights_not_weilPositive`: `log p` on the primes alone is not Weil-positive.
- Uses Zeta23 `MediumPNT`, Mathlib `Chebyshev.psi_sub_theta_*` bounds, and Cauchy condensation.
