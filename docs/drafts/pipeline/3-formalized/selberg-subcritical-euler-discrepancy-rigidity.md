# Subcritical Euler discrepancy determines a Selberg function

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ15
- **Statement:** Two full Selberg-class functions with the same completed gamma factor and Euler-log discrepancy absolutely convergent at some real `σ < 1/2` have identical Dirichlet coefficients. In particular, finite-prime changes cannot produce a distinct twin with that gamma factor.

## Proof

Write `b = b_F − b_G` and `R(s) = exp(Σ b(n)n^(−s))`. Increase the convergence abscissa to `max(σ,0) < 1/2`. Normal convergence makes `R` holomorphic to its right and bounds it uniformly on `Re s ≥ 1/2`.

The Euler products give `R G = F` for `Re s > 1`. Cross-multiplying the entire pole regularizations and applying the identity principle continues this equality to `Re s > σ`, away from the displayed pole at one, without dividing by `G`.

On `σ < Re s < 1−σ`, the gamma factors are analytic and nonzero. Cancel them in the two functional equations wherever `G ≠ 0`; isolated zeros and continuity then give `R(s) = (ω_F/ω_G) conjugate(R(1−conjugate(s)))` throughout the overlap. Glue these holomorphic expressions across the critical line. The phase has modulus one, so the resulting entire function is bounded on both half-planes. Liouville makes it constant. Dirichlet-series uniqueness gives `a_F(n) = c a_G(n)`; normalization at one gives `c = 1`.

For a finite set `P` of exceptional primes, let `θ = max(θ_F,θ_G) < 1/2`. The discrepancy satisfies `|b(n)| ≤ C n^θ` and vanishes outside the powers of primes in `P`. At any `θ < σ < 1/2`, each prime contributes a convergent geometric series `C Σ_k p^(k(θ−σ))`. The finite sum proves the required absolute convergence.

## Formalization

`formal/GaloisForLFunctions/SelbergClass/`:

- `SubcriticalEulerRigidity.lean`: `eulerQuotient_mul_value_of_summable`, `eulerQuotient_reflection`, `coeff_eq_of_subcritical_euler_discrepancy`.
- `FinitePrimeRigidity.lean`: `lSeriesSummable_of_finite_prime_support`, `coeff_eq_of_finite_prime_discrepancy`.

Both canonical `lake --old env lean` checks pass. Eight transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Both modules are wired into `SelbergClass.lean`.

## Scope

Equality of the full gamma factors includes the conductor. General full-Selberg twins remain open; no zero-free-strip or reflected-divisor premise is assumed.
