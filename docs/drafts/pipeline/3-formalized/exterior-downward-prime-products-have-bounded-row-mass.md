# Exterior downward prime products have bounded row mass

- **ID:** exterior-downward-prime-products-have-bounded-row-mass
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Fix overlap `c>0` and conductor `m`. Put `B=⌈c exp(c)⌉`, `w=c/N`, and let `g`
be a nonzero continuous bump supported in `[0,w]`, with mass `M_g=∫g²`.
The literal infinite downward prime row on `c_m(j)/√j`, divided by `M_g`,
minus its product-inside-horizon part satisfies

`Σ_{n≤N} |D_full(n)/M_g − D_interior(n)|² ≤ (B+1)(2ϕ(m)B)²`.

For dilates of any fixed nonzero compact `C²` unit profile, its norm after
`√log N` normalization tends to zero. Consequently the proved near Gamma
cancellation holds for the full downward prime action, including exterior
products. The explicit tilted spline is included.

## Proof [PROVED HERE]

Let `L=⌈N exp(c/N)⌉` and
`C_{m,N}(ℓ)=Σ_{d|ℓ, ℓ/d≤N} Λ(d)c_m(ℓ/d)`. Autocorrelation support truncates
the infinite lag series at `L`. The exact identity
`[Λ(k)/√k][c_m(j)/√j]=Λ(k)c_m(j)/√(kj)` permits regrouping by `ℓ=kj`.
The cutoff on `j` becomes `ℓ/d≤N`. Removing products `ℓ≤N` leaves exactly

`Σ_{N<ℓ≤L} [C_{m,N}(ℓ)/√ℓ] G_g(log ℓ−log n)/M_g`.

There are no omitted prime powers. The removed exact ratios have `ℓ=n≤N`
and thus never occur in this exterior sum.

Since `exp(t)−1≤t exp(t)` and `N≥1`, `L≤N+B`. A nonzero summand has
`|log ℓ−log n|≤c/N`, hence `ℓ−n≤c exp(c)≤B`. Since `ℓ>N`, its row satisfies
`n≥N−B`. Thus at most `B+1` rows and at most `B` products per row contribute.

The Ramanujan bound and the full divisor identity give
`|C_{m,N}(ℓ)|≤ϕ(m)Σ_{d|ℓ}Λ(d)=ϕ(m)log ℓ`. Cauchy–Schwarz gives
`|G_g|≤M_g`; and `log ℓ/√ℓ≤2`. Each summand therefore has absolute value
at most `2ϕ(m)`. Squaring the row bound and summing the boundary strip gives
the stated constant.

Division by `log N` proves the normalized norm limit. Finally,
`near Gamma − full downward = (near Gamma − interior downward) − exterior`.
Both normalized norms tend to zero, the first by
`TheNearGammaAndDownwardPrimeRowsCancel`; the triangle inequality completes
the full signed cancellation.

## Status

Leaf: `CriticalArithmeticCorrelationTheory/TheFullDownwardPrimeRowCancelsTheNearGammaRow.lean`.

- `downwardRamanujanRow_eq_divisors` identifies the infinite source exactly;
- `sum_actualExteriorDownwardRow_sq_le` proves the uniform boundary bound;
- `tendsto_normalizedExteriorDownwardVector_norm` removes exterior products in norm;
- `tendsto_tiltedUnitSpline_fullNearGammaDownward_norm` proves full signed cancellation.

Final direct no-olean check passed without warnings. All four axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`; CACT umbrella
import registered. This strengthens the existing near Gamma/downward
contribution; no separate count for boundary or reindexing helpers.
Actual upward logarithmic lags remain a distinct obligation.
