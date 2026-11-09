# Critical adelic orbit: normalization comparison

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B133.

The sharp threshold `s>2` and a prescribed primitive height finite part are
[formalized](../3-formalized/a-height-finite-part-of-the-critical-adelic-green-product.md).
The kernel tested is a product of normalized local Green profiles.

## Remaining targets

With `h(r)=1/(4(1+r))+1/(2(1+r²))` and `c₀=log 2/4+π/8`, prove:

- The all-pairs height cutoff has a limit after subtracting
  `(log N)²/8+(γ/4+c₀)log N`.
- The proved primitive finite part equals
  `ζ(2)⁻¹ Σ_{n≥1} E(n)/n²+c₀−h(1)`, where
  `E(n)=Σ_{1≤a≤n}h(a/n)−nc₀`. The last terms remove height one.
- Determine the transformation of the finite part under rational torus
  reindexing. Absolute convergence across rows does not establish automorphy.

Comparison with the additive adelic Green kernel and Weil's diagonal remains open.
