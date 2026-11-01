# Polynomial cyclic growth from finite negative index

- **Stage:** 3-formalized.
- **Type:** THEOREM.
- **Source:** B9 in `docs/reports/review-3110/route-obstacles.md`.

## Statement

Let `k : G → ℂ` be Hermitian on any group, with negative index at most
`r : ℕ`. Suppose every cyclic restriction is subexponential:
for every `g` and `ε>0`, some `C` bounds `‖k(gⁿ)‖` by `C exp(εn)` for all
natural `n`. Then, for each `g`, some nonnegative `D` satisfies

`‖k(gⁿ)‖ ≤ D (n+1)^(2r)` for all `n : ℕ`.

The underlying structural result is an index-reducing unitary filter.
A subexponential Hermitian kernel on `Multiplicative ℤ` of index at most
`r+1` is positive definite or admits `|a|=1` for which

`q(n) = 2k(n) - a k(n-1) - conjugate(a) k(n+1)`

is Hermitian and has index at most `r`.

## Proof

A normalized negative column frame has maximal length `m≤r`. A negative
vector in its orthogonal complement would extend the frame; thus that
complement is nonnegative. Cauchy–Schwarz and column nondegeneracy make
it definite. Projection splits the column form as `H₀ × ℂ^m`.

Every algebraic form-isometry on this product is bounded. Restrict its
inverse to the negative factor, obtaining a continuous finite-dimensional
map `U`. Pairing `U((Tv).2)` with `v` bounds the negative coordinate of
`Tv`; preservation of the square bounds the positive coordinate.
Translations therefore extend to a dense complete realization
`H × ℂ^m`, preserving the form and group law.

Contractive graphs over `ℂ^m` form a weakly compact convex set. An isometry
sends each graph to another: its negative projection is injective and
hence invertible. The transformed-graph equations are closed. The KMS
compact-codomain closed-graph criterion makes the graph action continuous;
the weak Hilbert fixed-point theorem yields an invariant nonpositive
graph. If `m>0`, its finite-dimensional invertible action has a nonzero
nonpositive eigenvector `w`.

Each negative coordinate of the cyclic column orbit is a finite sum of
kernel translates. Subexponential growth survives these sums and shifts;
the invariant square bounds the full orbit norm. Density detects `w` at
some column. Its orbit pairing is a nonzero scalar recurrence with
multiplier `conjugate(a)`. The existing exponential non-cancellation
theorem, applied to one node in both integer directions, forces `|a|=1`.

The image of `T-a` is orthogonal to `w`. A strictly negative subspace `V`
in that orthogonal space satisfies `dim V+1≤m`: adjoining `w` gives an
injective nonpositive family `V × ℂ`, whose negative projection is
injective. Pairing a vanishing combination with its `V` component proves
independence even when `w` is null. Finite Gram synthesis transfers this
bound to the filtered coefficient, giving the stated index drop.

The filter preserves subexponential growth and satisfies
`q(n+1) = -conjugate(a) Δₐ²k(n)`. Each unitary discrete integration raises
the polynomial growth degree by at most one. Induction on `r`, with the
bounded positive-definite case at `r=0`, gives degree `2r`. Pullback along
`ℤ → G`, `n ↦ gⁿ`, preserves Hermitian symmetry and cannot increase index.

## Lean

HKT `Index/FiniteIndexPolynomialGrowth.lean`:
- `polynomial_growth_of_finite_index_integer`;
- `cyclic_polynomial_growth_of_finite_index`.

HKT `Index/CyclicKernelFilter.lean`:
- `isPosDef_or_exists_unitary_cyclic_filter`.

The completed representation, invariant graph, unitary eigenvector,
index drop, and growth estimates are proved in their imported modules.
The final leaf passes `lake --old env lean`; both final transitive axiom
audits contain only `propext`, `Classical.choice`, `Quot.sound`.
All completed modules are wired into their programme umbrellas.

## Novelty and scope

This constructs a unitary filter from index and growth, rather than assuming
a spectral expansion. It extends the index-one quadratic growth law to
all finite indices and all groups. General unbounded higher-index spectral
decomposition in B9 remains open.

Corpus audits:
`/tmp/hgt-finite-index-growth-final-novelty.json`,
`/tmp/hgt-finite-index-filter-final-novelty.json`.
Nearby earlier results require prescribed spectral expansions; no earlier
general index-reducing filter or degree-`2r` growth theorem was found.
