# Littlewood Z3: threshold form — arbitrarily small constant per order (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletThreshold.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

```
largenessBound K := (K−1)(K−4/3)log(K−1) + K·log2
balanceBound  K := 3·2^K(K−4/3)·log(7680(K−4/3)/log2) + K·log2

littlewood_threshold (K) (hK : 2 ≤ K) :
  ∀ t, max (16π) (2π·exp(max (largenessBound K) (balanceBound K) + 1)) ≤ t →
    ‖∑_{n<2^{topExponent t+1}} n^{−1−It}‖ ≤ 1 + log2 + 2·log(t/2π)/(K−4/3)
```

Both `(t,K)` conditions say "a quantity in `K` alone is below `log(t/2π)`", so each order has an
explicit threshold.

## Why this matters

The constant `2/(K−4/3)` is arbitrarily small as `K` grows, so **the family of fixed-order bounds
already gives `o(log t)` with no construction of `K = K(t)`**. That construction is needed only for
the quantitative exponent `O(log t/loglog t)`, where `K` must grow with `t` at the rate the two
thresholds permit.

Natural stopping point for the structural work: the chain from the k-th derivative test terminates
in a self-contained unconditional statement with an explicit threshold.

## Literature check closed (2026-08-06)

arXiv 2607.01544 (Lean formalization of q-Pochhammer, q-binomials, Bailey's Lemma, **Jacobi Triple
Product**, Rogers–Ramanujan, via "AxiomProver") is **NOT in this toolchain's mathlib** — grep for
`qPochhammer|JacobiTriple|RogersRamanujan` over `.lake/packages/mathlib/Mathlib/` returns nothing.
So it is not importable here; it would have to be vendored. Do not assume Jacobi Triple Product is
available.
