# Exact signed cofactor dilation

Status: `[BRIDGE]`, four unconditional Lean theorems. No RH proof and no new asymptotic bound.

Module: `formal/GaloisForLFunctions/RHTower/LiouvilleSignedCofactorDilation.lean`.

For an arbitrary kernel K on real ratios, put `T_K(N)=sum(n<=N) lambda(n) K(N/n)`. Every positive integer a satisfies

`T_K(aN)-lambda(a)T_K(N)=sum(n<=aN, a does not divide n) lambda(n)K(aN/n)`.

Paper proof: split the finite source into divisible and nondivisible cofactors. The divisible terms are indexed bijectively by `n=a*m`, `1<=m<=N`. Complete multiplicativity gives `lambda(a*m)=lambda(a)lambda(m)` and the real ratio is `(aN)/(am)=N/m`. This gives the entire identity without estimating or discarding a term.

Specialize K to the actual Chebyshev error `theta(x)-x`. For every prime p, the coefficient `lambda(p)=-1` gives

`R(pN)+R(N)=sum(n<=pN, p does not divide n) lambda(n)(theta(pN/n)-pN/n)`.

Theorems:

- `RHTower.liouvilleCofactorSum_multiples`
- `RHTower.liouvilleCofactorSum_dilation_residual`
- `RHTower.liouvillePrimeCountingError_dilation_residual`
- `RHTower.liouvillePrimeCountingError_prime_residual`

All carry the literal Liouville coefficients. The prime theorem quantifies over `Nat.Primes`; it assumes no zero location, cancellation, positivity, or asymptotic source bound.

Scratch and direct source checks passed with `lake env lean`. The named leaf final build passed; the module is wired into `RHTower.lean`, with no umbrella build. `#print axioms` in a scratch file reports only `propext`, `Classical.choice`, and `Quot.sound` for all four theorems.

The [experiments](../2-fully-proven/computations/signed-prime-recursion-2026-09-06/REPORT.md) numerically falsify two stronger fixed-direction explanations. Their signs, ranks, and finite bounds are not Lean results. The exact positive residue of that attack is the retained nondivisible-cofactor identity above. An all-scale bound on its right side remains missing. This bridge does not retire or close the arithmetic RH route.
