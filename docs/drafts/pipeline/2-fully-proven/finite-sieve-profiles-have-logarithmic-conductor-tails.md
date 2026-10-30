# Finite sieve profiles have logarithmic conductor tails

- **ID:** finite-sieve-logarithmic-conductor-tails
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** A finite sieve-class vector supported on integers at most `A` has squared spectral mass above conductor `R>1` at most `2(log A+L_Q)/log R` times its squared norm, where `L_Q=Σ_(p∈Q) log p/(p-1)`.

## Proof

Let `H_Q` be the actual sieve adjunction operator minus Euler's constant. Its existing complete orthonormal basis `e_m` has eigenvalues `log m+tameDifferent(m)≥log m≥0`. For a finite real class vector `x=Σ_d b_d δ_d`, its exact quadratic form is

`E(x)=Σ_d (log d+L_Q)b_d²-Σ_(d,e) K(d,e)b_d b_e`,

where the literal prime kernel `K` is entrywise nonnegative. Parseval and the eigenvector equations give

`Σ_m log m |⟨e_m,x⟩|² ≤ E(x)`.

Apply `E≥0` to the vector with coefficients `|b_d|`. Its prime quadratic form is at most `Σ_d(log d+L_Q)b_d²`. Entrywise nonnegativity then bounds the negative of the signed prime quadratic form by the same quantity. Hence

`E(x)≤2Σ_d(log d+L_Q)b_d²≤2(log A+L_Q)Σ_d b_d²`.

Each conductor `m>R` contributes at least `log R` times its coefficient square. Division by `log R>0` gives the tail bound. This uses the existing arithmetic operator and its proved eigenbasis; no spectral or prime-distribution premise is added.

## Scope and formalization

Lean formalization is in progress. Transfer from these sieve spectral coefficients to finite-horizon Ramanujan approximation requires the coefficient identification and harmonic-measure comparison described on the parent confinement card; neither transfer is asserted here.
