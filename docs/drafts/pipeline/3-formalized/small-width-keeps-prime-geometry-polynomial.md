# Small width keeps prime geometry polynomial

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

If `w=c/N≤1`, distinct near indices have integer distance at most
`R=2e²c`, and both indices are at least `N/R`. Indeed,
`e^(2w)−1≤2we^(2w)≤2e²c/N`; apply this estimate in both directions
to the logarithmic-distance bound. Integer separation supplies the
lower bound one on their distance. Each near row has at most `2R`
indices. Cauchy–Schwarz consequently gives

`Σ_n (Σ_(j near n) F(n,j)/√j)² ≤ 4R³K²`

whenever every active numerator has absolute value at most `K`.

Likewise, `Ne^(c/N)≤N+ec`, so the exact exterior prime-product cutoff
lies below `N+ceil(ec)`. Every exterior product can reach only rows
within that same strip of the horizon. All constants are polynomial
in overlap once physical width is bounded.

## Lean status

`SmallWidthKeepsPrimeGeometryPolynomial.lean` proves the near-pair,
near-row squared-mass, exterior-cutoff and integer-separation bounds.
Final direct Lean audit passed without warnings; all four axiom audits
contain only `propext`, `Classical.choice`, `Quot.sound`. No separate count.
