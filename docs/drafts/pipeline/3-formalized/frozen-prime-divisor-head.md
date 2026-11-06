# Exact divisor-head average with frozen large-prime phases

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6

Fix natural numbers `N,Y` with `N<Y²`. Let `χ` be the Steinhaus character whose
prime phases at `p≤Y` are independent uniform phases, with `χ(p)=−1`
for every prime `p>Y`. Define

`τ_χ(n)=Σ_(de=n)χ(d)conjugate(χ(e))`.

For arbitrary complex coefficients `A`, the exact finite mean is

`E Σ_(1≤n≤N) A(n)τ_χ(n)`
`=Σ_(d≥1,d²≤N) A(d²)−2Σ_(Y<p≤N,p prime)Σ_(d≥1,pd²≤N) A(pd²)`.

Every finite trace and head is integrable. A divisor trace is multiplicative
on coprime products; its ordinary Steinhaus mean is the square indicator.

## Proof

For a smooth product, both divisor characters read only the unfrozen
coordinates. Orthogonality leaves exactly the equal divisor pairs.
There is one such pair precisely when the product is a positive square.

Every nonsmooth `n≤N<Y²` has a unique factorization `n=pm`, with prime
`p>Y` and `m<Y`. Thus `p` and `m` are coprime. Dirichlet-convolution
multiplicativity gives `τ_χ(pm)=τ_χ(p)τ_χ(m)=−2τ_χ(m)`, and the cofactor
reads only unfrozen phases. Apply the corpus largest-prime bijection and
average each finite term. Reindex the equal divisor pairs by their positive
square roots. Every square at most `N` is smooth because its root is below `Y`.

The identity concerns a finite phase average. It does not prove a negative
infinite spectrum or settle the physical theta phase sum.

## Lean

`RHTower/SteinhausFrozenPrimeDivisorTrace.lean` proves
`steinhausDivisorTrace_isMultiplicative`,
`integral_steinhausDivisorTrace`,
`divisorDiagonalMass_eq_squareIndicator`, and the exact square-indexed
identity `integral_frozenPrime_divisorHead_eq_squares`.
Final file check passed; all six capstone dependency audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
