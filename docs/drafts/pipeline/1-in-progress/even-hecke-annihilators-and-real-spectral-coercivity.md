# Even Hecke annihilators and real spectral coercivity

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Every finite set of actual ξ-zeros has a positive Hecke annihilator involving only even powers of `T₂,T₃`, with constant coefficient one and arbitrary prescribed spectral zero orders. Its scalar value is at least one on every real pair of Hecke eigenvalues.

## Mechanism to audit

For `u=(ρ−1)/2`, one of `λ_p(u)=p^u+p^(−u)`, `p∈{2,3}`, is nonreal. Otherwise both phases lie in `{1,−1}`, contradicting the irrational logarithmic ratio of two and three at `Im u≠0`.

A nonreal `λ` has `λ²` outside the nonnegative real axis. Apply the positive quadratic construction to `λ²`, then substitute `X_p²` for the selected variable. Products and powers preserve even support. At every real pair `(x₂,x₃)`, each nonconstant monomial is nonnegative, giving the scalar lower bound one.

## Relation to the formalized construction

`PositiveHeckeAnnihilatorsOfFiniteResonances.lean` currently constructs arbitrary positive monomials; its helper for general coordinate values is private. The stronger statement needs its own public even-power construction and a checked finite-product realization. The existing literal action and constant-mode cost should then apply to the same polynomial.

Actual Hilbert-space coercivity would additionally require the literal commuting self-adjoint Hecke realization. A scalar inequality alone is not that operator theorem. Neither statement would yet exclude non-square-integrable resonant states or prove AAL.

## Status

Corpus novelty audit and Lean formalization pending. The exact actual-zeta AAL contradiction remains open.
