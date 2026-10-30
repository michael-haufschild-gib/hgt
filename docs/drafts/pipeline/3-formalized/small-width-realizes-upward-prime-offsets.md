# Small width realizes the upward prime offsets

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

For `c/N≤1`, the literal upward Ramanujan prime row is exactly the
finite positive/negative offset sum with `1≤h≤ceil(ec)` and
`1≤k≤N+ceil(ec)`. Both original horizon cutoffs remain present.
An active product satisfies `|kn−j|≤j(e^(c/N)−1)≤ec`.
Reindex each off-diagonal row by its positive and negative integer gap;
all other products vanish by support. The existing square-root factor
identity identifies its normalization with
`logarithmicUpwardCoefficient φ c (ceil(ec)) N m n`.

## Lean status

`SmallWidthRealizesTheUpwardPrimeOffsets` proves the exact two-direction
reindexing and logarithmic-source normalization. Final direct Lean check
passed without warnings; all three transitive axiom audits contain only
standard logical axioms. CACT umbrella wired. Supporting exact source
identity; no separate contribution count.
