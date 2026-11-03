# Euler rigidity with the conductor allowed to vary

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ15
- **Statement:** Full Selberg functions with the same product of Gamma functions and an Euler-log discrepancy absolutely convergent at some `σ < 1/2` have identical coefficients, positive parameters `Q` and root numbers. Equality of `Q` is a conclusion. This includes changes at finitely many primes.

## Proof

Swap the functions so `d = log Q_F − log Q_G ≤ 0`. Put `T(s) = exp(ds) R(s)`, with `R` the holomorphic Euler quotient. The identity `gamma_F(s) = exp(ds) gamma_G(s)` follows from equality of the products of Gamma functions. Cancelling the two functional equations off their common isolated zeros, then extending by continuity, gives `T(s) = (ω_F/ω_G) conjugate(T(1−conjugate(s)))` on the overlap strip.

For `Re s ≥ 1/2`, `|exp(ds)| ≤ 1`, so the absolute Euler-log sum bounds `T`. Reflection bounds its left-hand continuation. Gluing and Liouville make it a constant `c ≠ 0`. Normalization of both Dirichlet series gives `R(x) = F(x)/G(x) → 1` as real `x → ∞`. If `d < 0`, then `T(x) → 0`, contradicting `c ≠ 0`. Thus `d = 0`, `Q_F = Q_G` and `c = 1`. Subcritical Euler rigidity gives coefficient equality; the reflected identity at the critical line gives `ω_F = ω_G`. Interchanging `F,G` treats the other ordering of their `Q` parameters.

## Lean

In namespace `GaloisForLFunctions.SelbergClass`:

- `SubcriticalEulerRigidity.lean`: `archGammaFactor`, `eulerQuotient_tendsto_atTop`, `rigidity_of_subcritical_euler_discrepancy`.
- `FinitePrimeRigidity.lean`: `exists_subcritical_of_finite_prime_discrepancy`, `rigidity_of_finite_prime_discrepancy`.

Both canonical `lake --old env lean` checks pass. Nine transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Both modules are imported by `SelbergClass.lean`.

## Scope

The finite-prime theorem derives subcritical convergence from the full Selberg axioms; it adds no convergence or zero-free-region premise. Equality of the bare Gamma products remains required. General Γ15 remains partially solved.
