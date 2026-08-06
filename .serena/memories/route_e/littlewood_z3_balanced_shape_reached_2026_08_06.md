# Littlewood Z3: the two terms balanced — Littlewood shape reached (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTailDominated.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `tail_le_head (hK : 2 ≤ K) (hL : 0 ≤ L) (hM : M ≤ L)` with
  `log(7680(K−4/3)/log2) ≤ (L − K log2)/(3·2^K·(K−4/3))` ⟹
  `3M/log2 · 2560 · exp(−(L−K log2)/(3·2^K(K−4/3))) ≤ L/(K−4/3)`.
- `norm_dirichlet_partial_littlewood_balanced` : under `16π ≤ t`, `2 ≤ K`, largeness, balance,
  **`‖∑_{n<2^{topExponent t+1}} n^{−1−It}‖ ≤ 1 + log 2 + 2·log(t/2π)/(K − 4/3)`**.

`O(log t / K)` with explicit constant 2. The two hypotheses on `(t,K)`:

```
(K−1)(K−4/3)log(K−1) + K log2 < log(t/2π)                       (largeness)
3·2^K(K−4/3)·log(7680(K−4/3)/log2) ≤ log(t/2π) − K log2          (balance)
```

Both hold for `K ≈ log₂log t`: their left sides are then `≈ (loglog t)²·logloglog t`, the right
`≈ log t`.

## Status

**The structural half of the Littlewood programme is complete** — every step from the k-th
derivative test to an `O(log t/K)` bound on the partial sum is an unconditional Lean theorem
(25 modules). Remaining: choose `K = K(t)` satisfying both inequalities and read `K ≈ log₂log t`;
then Z4 (PNTPlus truncation of `ζ(1+it)` against the partial sum) and Z5 (rectangle σ-version).

## Literature note (2026-08-06)

arXiv 2607.01544 "Formalized q-series: The Rogers–Ramanujan Identities and Beyond" formalizes
q-Pochhammer symbols, q-binomials, Bailey's Lemma, **Jacobi Triple Product**, Rogers–Ramanujan —
**in Lean**, produced with "AxiomProver". Mathlib contribution not stated in the abstract. Jacobi
Triple Product is adjacent to the corpus theta layer; check whether any of it is upstreamed before
building theta identities from scratch.
