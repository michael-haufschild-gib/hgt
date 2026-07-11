# Prime-occupation discrete-Morse reheating

- **ID:** `prime-occupation-discrete-morse-reheating`
- **Stage:** 5-failed
- **Type:** FAILED OUTLANDISH ROUTE; proved topological obstruction
- **Scientific status:** `[ROUTE RETIRED]`; the basic Euler-characteristic representation is known,
  and the proposed Morse strengthening is impossible at square-root scale
- **Source:** scalar-field / pre-Big-Bang ideation pivot, 2026-07-11

## Proposed mechanism

For `x>=1`, let `K_x` be the finite simplicial complex whose vertices are primes at most `x` and
whose faces are the finite prime sets `S` satisfying

```text
product_(p in S) p <= x.
```

The face `S` is a squarefree prime-occupation history, its fermion parity is `(-1)^|S|`, and

```text
sum_(S in K_x) (-1)^|S| = M(x),
```

the Mertens function, with the empty face contributing `1`. The attempted cosmological mechanism
was a source-canonical discrete Morse matching representing reheating: histories of opposite parity
cancel, while at most `O_epsilon(x^(1/2+epsilon))` critical histories survive. Such a matching would
imply the Mertens form of RH.

This is not adopted as new. The Euler-characteristic formulation of the Mertens criterion and the
supersymmetric primon-gas interpretation of `mu` are already in the literature.

## Terminal homology obstruction `[PROVED]`

The stronger discrete-Morse proposal is false by a linear lower bound on the total Betti number.

Let `n` be odd, squarefree, and satisfy

```text
x/2 < n <= x.
```

Write `F_n` for its set of prime divisors. Then `F_n` is a face of `K_x`, but
`F_n union {2}` is not, because `2n>x`. Every proper face of that missing simplex is present:

- deleting `2` leaves `F_n`, whose product is `n<=x`;
- deleting a prime `q|n` leaves a face of product `2n/q<=2x/3<x`.

Hence the simplicial boundary

```text
z_n = boundary(F_n union {2})
```

is a cycle in `K_x`. It is not a boundary. Its face `F_n` is maximal in `K_x`, because multiplying
`n>x/2` by any absent prime gives a product greater than `x`; consequently no higher-dimensional
face has `F_n` in its boundary.

The classes `[z_n]` are linearly independent across distinct `n`: in a linear combination, the
coefficient of the unique maximal face `F_n` occurs only in `z_n` and cannot be supplied by a
boundary. Therefore

```text
sum_k beta_k(K_x)
  >= #{odd squarefree n : x/2 < n <= x}
  = Omega(x).                                           (H)
```

The last estimate is the elementary positive-density theorem for odd squarefree integers.

By the weak Morse inequalities, every discrete Morse matching on `K_x` has at least the total Betti
number of critical faces. Thus `(H)` forces `Omega(x)` critical histories. No discrete Morse
reheating on the natural prime-occupation complex can leave only square-root-many defects.

## Why repairs do not preserve the mechanism

1. A non-acyclic parity pairing can ignore homology, but then its unmatched imbalance is exactly
   `|M(x)|`; asserting a square-root bound for the unmatched set restates RH.
2. Changing the cutoff complex to kill the cycles changes its Euler characteristic and loses the
   exact Mertens reader.
3. Weighting faces by `n^(-s)` returns the known fermionic Euler product `1/zeta(s)` on its
   convergence half-plane and does not continue the matching across zeta zeros.
4. Allowing nonlocal arbitrary pairings removes the source-canonical reheating law: any two finite
   parity sets can be paired down to their cardinality difference.

## Verdict

`[FAILED]` The route is simultaneously a literature collision at the Euler-characteristic/Witten
index level and topologically obstructed at the proposed Morse-mechanism level. The explicit missing
simplex cycles are retained as a firewall against future claims that a local supersymmetric or
discrete-Morse cancellation of prime occupations could prove RH.

## Literature boundary

- The Mertens criterion is a classical equivalent formulation of RH.
- Spector, *Supersymmetry and the Möbius Inversion Function*, Communications in Mathematical
  Physics 127 (1990), gives the supersymmetric Möbius/primon parent.
- No novelty claim is made for the complex itself. The explicit linear homology obstruction above
  was derived here but has not passed a broad parent-literature audit.
